import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Shard Engine — Behaviour

## Lock Acquisition

When `acquireLock` arrives from the mempool worker, the shard:
1. Adds a `KeyAccess` entry to its DAG with pending read/write status.
2. Sends `TxOrderingMsg.lockAcquired` back to the worker via
   cross-type `Effect.send`.

## Write Handling

When `write` arrives, the shard updates the corresponding `KeyAccess`
entry to `committed` status with the provided datum.

## Read Request Handling

When `readRequest` arrives from an executor, the shard searches its
DAG for the most recent committed write at a preceding fingerprint.
- If found: marks the read as `fulfilled` and sends
  `ExecutorMsg.readReply` to the executor.
- If not found: marks the read as `pending` (to be fulfilled when
  the preceding write commits).

## Watermark Updates

When `updateSeenAll` arrives, the shard updates the `heardAllReads`
and `heardAllWrites` watermarks, enabling garbage collection.
-/

namespace MailboxActors.Examples.Anoma.Ordering

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Shard Behaviour
-- ============================================================================

/-- Guard for `acquireLock` messages. Extracts the fingerprint, key,
    and mempool worker address. -/
@[simp] def shardAcquireLockGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey × Address) :=
  match @GuardInput.msg (S A) _ inp with
  | .acquireLock fp key worker => some (fp, key, worker)
  | _ => none

/-- Action for `acquireLock`: add a DAG entry with pending read/write
    status and send `lockAcquired` back to the mempool worker.

    Uses cross-type `Effect.send` to deliver a `TxOrderingMsg` to
    the worker's address. -/
def shardAcquireLockAction
    (w : A.TxFingerprint × A.KVSKey × Address)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardAcquireLockGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A
  let env := inp.env
  let st := env.localState
  let fp := w.1
  let key := w.2.1
  let worker := w.2.2
  let newAccess : KeyAccess A :=
    { readStatus := some .pending
      writeStatus := some .pending }
  Effect.chain
    (Effect.update { env with
      localState := { st with
        keyAccesses := st.keyAccesses ++ [(key, fp, newAccess)] } })
    (Effect.send AnomaIdx.txOrdering worker (.lockAcquired fp key))

/-- Guard for `readRequest` messages. Extracts the fingerprint, key,
    and executor address. -/
@[simp] def shardReadRequestGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey × Address) :=
  match @GuardInput.msg (S A) _ inp with
  | .readRequest fp key executor => some (fp, key, executor)
  | _ => none

/-- Action for `readRequest`: search the DAG for the most recent
    committed write for the given key at a preceding fingerprint.

    - If a committed value is found, the read is marked `fulfilled`
      and `ExecutorMsg.readReply` is sent to the executor.
    - If no preceding write exists yet, the read is marked `pending`. -/
def shardReadRequestAction
    (w : A.TxFingerprint × A.KVSKey × Address)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardReadRequestGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A
  let env := inp.env
  let st := env.localState
  let fp := w.1
  let key := w.2.1
  let executorAddr := w.2.2
  -- Find the most recent committed write for this key preceding fp
  let precedingWrite := st.keyAccesses.foldl (init := (none : Option A.KVSDatum))
    fun acc entry =>
      if entry.1 == key && !(entry.2.1 == fp) && A.fingerprintLe entry.2.1 fp then
        match entry.2.2.writeStatus with
        | some (.committed datum) => some datum
        | _ => acc
      else acc
  match precedingWrite with
  | some datum =>
    -- Value available: mark read as fulfilled and send to executor
    Effect.chain
      (Effect.update { env with
        localState := { st with
          keyAccesses := st.keyAccesses.map fun entry =>
            if entry.1 == key && entry.2.1 == fp then
              (entry.1, entry.2.1, { entry.2.2 with readStatus := some .fulfilled })
            else entry } })
      (Effect.send AnomaIdx.executor executorAddr (.readReply key datum))
  | none =>
    -- No preceding write yet: mark read as pending
    Effect.update { env with
      localState := { st with
        keyAccesses := st.keyAccesses.map fun entry =>
          if entry.1 == key && entry.2.1 == fp then
            (entry.1, entry.2.1, { entry.2.2 with readStatus := some .pending })
          else entry } }

/-- Guard for `write` messages. -/
@[simp] def shardWriteGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey × A.KVSDatum) :=
  match @GuardInput.msg (S A) _ inp with
  | .write fp key datum => some (fp, key, datum)
  | _ => none

/-- Action for `write`: update the DAG entry for the given key and
    fingerprint to `committed` status with the provided datum. -/
def shardWriteAction
    (w : A.TxFingerprint × A.KVSKey × A.KVSDatum)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardWriteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A
  let env := inp.env
  let st := env.localState
  let fp := w.1
  let key := w.2.1
  let datum := w.2.2
  let updatedAccesses := st.keyAccesses.map fun entry =>
    if entry.1 == key && entry.2.1 == fp then
      (entry.1, entry.2.1,
        { entry.2.2 with writeStatus := some (.committed datum) })
    else entry
  Effect.update { env with
    localState := { st with keyAccesses := updatedAccesses } }

/-- Guard for `updateSeenAll` messages. -/
@[simp] def shardUpdateSeenAllGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option A.TxFingerprint :=
  match @GuardInput.msg (S A) _ inp with
  | .updateSeenAll fp => some fp
  | _ => none

/-- Action for `updateSeenAll`: update both barrier watermarks.
    Once updated, the shard can garbage-collect DAG entries older
    than the watermarks. -/
def shardUpdateSeenAllAction
    (w : A.TxFingerprint)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardUpdateSeenAllGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with
      heardAllReads := w
      heardAllWrites := w } }

def shardActions : @Behaviour (S A) AnomaIdx.shard :=
  letI := S A
  [ { Witness := A.TxFingerprint × A.KVSKey × Address
      guard := shardAcquireLockGuard A
      action := shardAcquireLockAction A }
  , { Witness := A.TxFingerprint × A.KVSKey × Address
      guard := shardReadRequestGuard A
      action := shardReadRequestAction A }
  , { Witness := A.TxFingerprint × A.KVSKey × A.KVSDatum
      guard := shardWriteGuard A
      action := shardWriteAction A }
  , { Witness := A.TxFingerprint
      guard := shardUpdateSeenAllGuard A
      action := shardUpdateSeenAllAction A } ]

private theorem shardNonOverlapping :
    @NonOverlappingGuards (S A) _ (shardActions A) := by
  letI := S A
  intro inp
  simp only [shardActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def shardBehaviour : @WellFormedBehaviour (S A) AnomaIdx.shard :=
  letI := S A
  { actions := shardActions A
    nonOverlapping := shardNonOverlapping A }

end MailboxActors.Examples.Anoma.Ordering
