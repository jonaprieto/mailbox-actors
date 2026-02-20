import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# TxOrdering Engine (Mempool Worker) — Behaviour

## Transaction Submission Flow

When a `submitTx` message arrives:
1. The worker increments the gensym counter (`nextFingerprint`) to assign
   a unique position in the ordering.
2. It adds the fingerprint to `pendingLocks` to track lock acquisition.
3. It spawns an executor engine with the transaction's access rights.

## Lock Acquisition Flow

When a `lockAcquired` message arrives from a shard, the worker removes
the corresponding entry from `pendingLocks`.

## Executor Completion Flow

When an `executorFinished` message arrives, the worker removes the
transaction from tracking.
-/

namespace MailboxActors.Examples.Anoma.Ordering

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § TxOrdering Behaviour
-- ============================================================================

/-- Guard for `submitTx` messages. Extracts the fingerprint and executable. -/
@[simp]
def txOrderingSubmitGuard
    (inp : @GuardInput (S A) AnomaIdx.txOrdering) :
    Option (A.TxFingerprint × A.Executable) :=
  match @GuardInput.msg (S A) _ inp with
  | .submitTx fp exe => some (fp, exe)
  | _ => none

/-- Action for `submitTx`: increment the gensym counter and record
    the transaction as pending. The executor is spawned to execute
    the transaction program.

    Effect: `update` the local state with the new fingerprint counter
    and pending locks list, then `spawn` an executor engine. -/
def txOrderingSubmitAction
    (w : A.TxFingerprint × A.Executable)
    (inp : @GuardInput (S A) AnomaIdx.txOrdering)
    (_ : txOrderingSubmitGuard A inp = some w) :
    @Effect (S A) AnomaIdx.txOrdering :=
  letI := S A
  let env := inp.env
  let st := env.localState
  let nextFp := A.fingerprintSucc st.nextFingerprint
  Effect.chain
    (Effect.update { env with
      localState := { nextFingerprint := nextFp
                      pendingLocks := st.pendingLocks ++ [w.1] } })
    (Effect.spawn AnomaIdx.executor
      { fingerprint := w.1
        executable := w.2
        lazyReadKeys := []
        eagerReadKeys := []
        willWriteKeys := []
        mayWriteKeys := [] }
      { programState := A.initProgramState w.2
        completedReads := []
        completedWrites := [] })

/-- Guard for `lockAcquired` messages. -/
@[simp]
def txOrderingLockGuard
    (inp : @GuardInput (S A) AnomaIdx.txOrdering) :
    Option (A.TxFingerprint × A.KVSKey) :=
  match @GuardInput.msg (S A) _ inp with
  | .lockAcquired fp key => some (fp, key)
  | _ => none

/-- Action for `lockAcquired`: remove the transaction from pending locks
    once all locks have been acquired. -/
def txOrderingLockAction
    (w : A.TxFingerprint × A.KVSKey)
    (inp : @GuardInput (S A) AnomaIdx.txOrdering)
    (_ : txOrderingLockGuard A inp = some w) :
    @Effect (S A) AnomaIdx.txOrdering :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with
      pendingLocks := st.pendingLocks.filter (· != w.1) } }

/-- Guard for `executorFinished` messages. -/
@[simp]
def txOrderingFinishedGuard
    (inp : @GuardInput (S A) AnomaIdx.txOrdering) :
    Option A.TxFingerprint :=
  match @GuardInput.msg (S A) _ inp with
  | .executorFinished fp => some fp
  | _ => none

/-- Action for `executorFinished`: clean up tracking state.
    The transaction has completed execution. -/
def txOrderingFinishedAction
    (w : A.TxFingerprint)
    (inp : @GuardInput (S A) AnomaIdx.txOrdering)
    (_ : txOrderingFinishedGuard A inp = some w) :
    @Effect (S A) AnomaIdx.txOrdering :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with
      pendingLocks := st.pendingLocks.filter (· != w) } }

def txOrderingActions : @Behaviour (S A) AnomaIdx.txOrdering :=
  letI := S A
  [ { Witness := A.TxFingerprint × A.Executable
      guard := txOrderingSubmitGuard A
      action := txOrderingSubmitAction A }
  , { Witness := A.TxFingerprint × A.KVSKey
      guard := txOrderingLockGuard A
      action := txOrderingLockAction A }
  , { Witness := A.TxFingerprint
      guard := txOrderingFinishedGuard A
      action := txOrderingFinishedAction A } ]

private theorem txOrderingNonOverlapping :
    @NonOverlappingGuards (S A) _ (txOrderingActions A) := by
  letI := S A
  intro inp
  simp only [txOrderingActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def txOrderingBehaviour : @WellFormedBehaviour (S A) AnomaIdx.txOrdering :=
  letI := S A
  { actions := txOrderingActions A
    nonOverlapping := txOrderingNonOverlapping A }

end MailboxActors.Examples.Anoma.Ordering
