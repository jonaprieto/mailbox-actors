import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Ordering Subsystem — Behaviours

Guards and actions for `txOrdering`, `shard`, `executor`.
-/

namespace MailboxActors.Examples.Anoma.Ordering

open MailboxActors

variable (A : AnomaTypes)

-- Use a convenient abbreviation for the EngineSpec instance
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § TxOrdering Behaviour
-- ============================================================================

@[simp]
def txOrderingSubmitGuard
    (inp : @GuardInput (S A) AnomaIdx.txOrdering) :
    Option (A.TxFingerprint × A.Executable) :=
  match @GuardInput.msg (S A) _ inp with
  | .submitTx fp exe => some (fp, exe)
  | _ => none

def txOrderingSubmitAction
    (w : A.TxFingerprint × A.Executable)
    (inp : @GuardInput (S A) AnomaIdx.txOrdering)
    (_ : txOrderingSubmitGuard A inp = some w) :
    @Effect (S A) AnomaIdx.txOrdering :=
  letI := S A; Effect.noop

@[simp]
def txOrderingLockGuard
    (inp : @GuardInput (S A) AnomaIdx.txOrdering) :
    Option (A.TxFingerprint × A.KVSKey) :=
  match @GuardInput.msg (S A) _ inp with
  | .lockAcquired fp key => some (fp, key)
  | _ => none

def txOrderingLockAction
    (w : A.TxFingerprint × A.KVSKey)
    (inp : @GuardInput (S A) AnomaIdx.txOrdering)
    (_ : txOrderingLockGuard A inp = some w) :
    @Effect (S A) AnomaIdx.txOrdering :=
  letI := S A; Effect.noop

@[simp]
def txOrderingFinishedGuard
    (inp : @GuardInput (S A) AnomaIdx.txOrdering) :
    Option A.TxFingerprint :=
  match @GuardInput.msg (S A) _ inp with
  | .executorFinished fp => some fp
  | _ => none

def txOrderingFinishedAction
    (w : A.TxFingerprint)
    (inp : @GuardInput (S A) AnomaIdx.txOrdering)
    (_ : txOrderingFinishedGuard A inp = some w) :
    @Effect (S A) AnomaIdx.txOrdering :=
  letI := S A; Effect.noop

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

/-- The txOrdering actions are non-overlapping. -/
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

-- ============================================================================
-- § Shard Behaviour
-- ============================================================================

@[simp] def shardAcquireLockGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey) :=
  match @GuardInput.msg (S A) _ inp with
  | .acquireLock fp key => some (fp, key)
  | _ => none

def shardAcquireLockAction
    (w : A.TxFingerprint × A.KVSKey)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardAcquireLockGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A; Effect.noop

@[simp] def shardReadRequestGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey) :=
  match @GuardInput.msg (S A) _ inp with
  | .readRequest fp key => some (fp, key)
  | _ => none

def shardReadRequestAction
    (w : A.TxFingerprint × A.KVSKey)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardReadRequestGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A; Effect.noop

@[simp] def shardWriteGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option (A.TxFingerprint × A.KVSKey × A.KVSDatum) :=
  match @GuardInput.msg (S A) _ inp with
  | .write fp key datum => some (fp, key, datum)
  | _ => none

def shardWriteAction
    (w : A.TxFingerprint × A.KVSKey × A.KVSDatum)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardWriteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A; Effect.noop

@[simp] def shardUpdateSeenAllGuard
    (inp : @GuardInput (S A) AnomaIdx.shard) :
    Option A.TxFingerprint :=
  match @GuardInput.msg (S A) _ inp with
  | .updateSeenAll fp => some fp
  | _ => none

def shardUpdateSeenAllAction
    (w : A.TxFingerprint)
    (inp : @GuardInput (S A) AnomaIdx.shard)
    (_ : shardUpdateSeenAllGuard A inp = some w) :
    @Effect (S A) AnomaIdx.shard :=
  letI := S A; Effect.noop

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

-- ============================================================================
-- § Executor Behaviour
-- ============================================================================

@[simp] def executorReadReplyGuard
    (inp : @GuardInput (S A) AnomaIdx.executor) :
    Option (A.KVSKey × A.KVSDatum) :=
  match @GuardInput.msg (S A) _ inp with
  | .readReply key datum => some (key, datum)

def executorReadReplyAction
    (w : A.KVSKey × A.KVSDatum)
    (inp : @GuardInput (S A) AnomaIdx.executor)
    (_ : executorReadReplyGuard A inp = some w) :
    @Effect (S A) AnomaIdx.executor :=
  letI := S A; Effect.noop

def executorActions : @Behaviour (S A) AnomaIdx.executor :=
  letI := S A
  [ { Witness := A.KVSKey × A.KVSDatum
      guard := executorReadReplyGuard A
      action := executorReadReplyAction A } ]

private theorem executorNonOverlapping :
    @NonOverlappingGuards (S A) _ (executorActions A) := by
  letI := S A
  intro inp
  simp only [executorActions, List.filter]
  split <;> simp

def executorBehaviour : @WellFormedBehaviour (S A) AnomaIdx.executor :=
  letI := S A
  { actions := executorActions A
    nonOverlapping := executorNonOverlapping A }

end MailboxActors.Examples.Anoma.Ordering
