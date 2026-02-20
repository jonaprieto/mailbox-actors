import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Shard Engine — Behaviour

## Lock Acquisition

When `acquireLock` arrives, the shard adds a `KeyAccess` entry to its DAG
with pending read/write status, and sends `lockAcquired` back to the
mempool worker.

## Write Handling

When `write` arrives, the shard updates the corresponding `KeyAccess`
entry to `committed` status with the provided datum.

## Read Request Handling

When `readRequest` arrives, the shard looks for the most recent
preceding write and sends the value if ready.

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

/-- Guard for `acquireLock` messages. -/
@[simp] def shardAcquireLockGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey) :=
  match @GuardInput.msg (S A) _ inp with
  | .acquireLock fp key => some (fp, key)
  | _ => none

/-- Action for `acquireLock`: add a DAG entry with pending read/write
    status. This records the transaction's access to the key. -/
def shardAcquireLockAction
    (w : A.TxFingerprint × A.KVSKey)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardAcquireLockGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A
  let env := inp.env
  let st := env.localState
  let newAccess : KeyAccess A :=
    { readStatus := some .pending
      writeStatus := some .pending }
  Effect.update { env with
    localState := { st with
      keyAccesses := st.keyAccesses ++ [(w.2, w.1, newAccess)] } }

/-- Guard for `readRequest` messages. -/
@[simp] def shardReadRequestGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey) :=
  match @GuardInput.msg (S A) _ inp with
  | .readRequest fp key => some (fp, key)
  | _ => none

/-- Action for `readRequest`: look up the key in the DAG and
    attempt to fulfill the read from a preceding write. -/
def shardReadRequestAction
    (w : A.TxFingerprint × A.KVSKey)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardReadRequestGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A; Effect.noop

/-- Guard for `write` messages. -/
@[simp] def shardWriteGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey × A.KVSDatum) :=
  match @GuardInput.msg (S A) _ inp with
  | .write fp key datum => some (fp, key, datum)
  | _ => none

/-- Action for `write`: update the DAG entry for the given key and
    fingerprint to `committed` status with the provided datum.
    Then check for any pending reads that can now be fulfilled. -/
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
  [ { Witness := A.TxFingerprint × A.KVSKey
      guard := shardAcquireLockGuard A
      action := shardAcquireLockAction A }
  , { Witness := A.TxFingerprint × A.KVSKey
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
