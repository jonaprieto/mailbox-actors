import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Infrastructure Subsystem — Behaviours

Guards and actions for `ticker`, `wallClock`, `logging`,
`kvStore`, `tsStore`, `storage`.
-/

namespace MailboxActors.Examples.Anoma.Infra

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Ticker Behaviour
-- ============================================================================

@[simp] def tickerIncrGuard
    (inp : @GuardInput (S A) AnomaIdx.ticker) :
    Option Unit :=
  match @GuardInput.msg (S A) _ inp with
  | .increment => some ()
  | _ => none

def tickerIncrAction
    (_ : Unit)
    (inp : @GuardInput (S A) AnomaIdx.ticker)
    (_ : tickerIncrGuard A inp = some ()) :
    @Effect (S A) AnomaIdx.ticker :=
  letI := S A
  let env := inp.env
  Effect.update { env with localState := { counter := env.localState.counter + 1 } }

@[simp] def tickerGetCountGuard
    (inp : @GuardInput (S A) AnomaIdx.ticker) :
    Option Unit :=
  match @GuardInput.msg (S A) _ inp with
  | .getCount => some ()
  | _ => none

def tickerGetCountAction
    (_ : Unit)
    (inp : @GuardInput (S A) AnomaIdx.ticker)
    (_ : tickerGetCountGuard A inp = some ()) :
    @Effect (S A) AnomaIdx.ticker :=
  letI := S A; Effect.noop

@[simp] def tickerCountGuard
    (inp : @GuardInput (S A) AnomaIdx.ticker) :
    Option Nat :=
  match @GuardInput.msg (S A) _ inp with
  | .count n => some n
  | _ => none

def tickerCountAction
    (w : Nat)
    (inp : @GuardInput (S A) AnomaIdx.ticker)
    (_ : tickerCountGuard A inp = some w) :
    @Effect (S A) AnomaIdx.ticker :=
  letI := S A; Effect.noop

def tickerActions : @Behaviour (S A) AnomaIdx.ticker :=
  letI := S A
  [ { Witness := Unit
      guard := tickerIncrGuard A
      action := tickerIncrAction A }
  , { Witness := Unit
      guard := tickerGetCountGuard A
      action := tickerGetCountAction A }
  , { Witness := Nat
      guard := tickerCountGuard A
      action := tickerCountAction A } ]

private theorem tickerNonOverlapping :
    @NonOverlappingGuards (S A) _ (tickerActions A) := by
  letI := S A; intro inp
  simp only [tickerActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def tickerBehaviour : @WellFormedBehaviour (S A) AnomaIdx.ticker :=
  letI := S A
  { actions := tickerActions A
    nonOverlapping := tickerNonOverlapping A }

-- ============================================================================
-- § WallClock Behaviour
-- ============================================================================

@[simp] def wallClockGetTimeGuard
    (inp : @GuardInput (S A) AnomaIdx.wallClock) :
    Option Unit :=
  match @GuardInput.msg (S A) _ inp with
  | .getTime => some ()
  | _ => none

def wallClockGetTimeAction
    (_ : Unit)
    (inp : @GuardInput (S A) AnomaIdx.wallClock)
    (_ : wallClockGetTimeGuard A inp = some ()) :
    @Effect (S A) AnomaIdx.wallClock :=
  letI := S A; Effect.noop

@[simp] def wallClockTimeReplyGuard
    (inp : @GuardInput (S A) AnomaIdx.wallClock) :
    Option A.Epoch :=
  match @GuardInput.msg (S A) _ inp with
  | .timeReply ep => some ep
  | _ => none

def wallClockTimeReplyAction
    (w : A.Epoch)
    (inp : @GuardInput (S A) AnomaIdx.wallClock)
    (_ : wallClockTimeReplyGuard A inp = some w) :
    @Effect (S A) AnomaIdx.wallClock :=
  letI := S A; Effect.noop

def wallClockActions : @Behaviour (S A) AnomaIdx.wallClock :=
  letI := S A
  [ { Witness := Unit
      guard := wallClockGetTimeGuard A
      action := wallClockGetTimeAction A }
  , { Witness := A.Epoch
      guard := wallClockTimeReplyGuard A
      action := wallClockTimeReplyAction A } ]

private theorem wallClockNonOverlapping :
    @NonOverlappingGuards (S A) _ (wallClockActions A) := by
  letI := S A; intro inp
  simp only [wallClockActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def wallClockBehaviour : @WellFormedBehaviour (S A) AnomaIdx.wallClock :=
  letI := S A
  { actions := wallClockActions A
    nonOverlapping := wallClockNonOverlapping A }

-- ============================================================================
-- § Logging Behaviour
-- ============================================================================

@[simp] def loggingAppendGuard
    (inp : @GuardInput (S A) AnomaIdx.logging) :
    Option String :=
  match @GuardInput.msg (S A) _ inp with
  | .append s => some s

def loggingAppendAction
    (w : String)
    (inp : @GuardInput (S A) AnomaIdx.logging)
    (_ : loggingAppendGuard A inp = some w) :
    @Effect (S A) AnomaIdx.logging :=
  letI := S A
  let env := inp.env
  Effect.update { env with
    localState := { entries := env.localState.entries ++ [w]
                    position := env.localState.position + 1 } }

def loggingActions : @Behaviour (S A) AnomaIdx.logging :=
  letI := S A
  [ { Witness := String
      guard := loggingAppendGuard A
      action := loggingAppendAction A } ]

private theorem loggingNonOverlapping :
    @NonOverlappingGuards (S A) _ (loggingActions A) := by
  letI := S A; intro inp
  simp only [loggingActions, List.filter]
  split <;> simp

def loggingBehaviour : @WellFormedBehaviour (S A) AnomaIdx.logging :=
  letI := S A
  { actions := loggingActions A
    nonOverlapping := loggingNonOverlapping A }

-- ============================================================================
-- § KVStore Behaviour
-- ============================================================================

@[simp] def kvStoreGetGuard
    (inp : @GuardInput (S A) AnomaIdx.kvStore) :
    Option A.StorageKey :=
  match @GuardInput.msg (S A) _ inp with
  | .getReq key => some key
  | _ => none

def kvStoreGetAction
    (w : A.StorageKey)
    (inp : @GuardInput (S A) AnomaIdx.kvStore)
    (_ : kvStoreGetGuard A inp = some w) :
    @Effect (S A) AnomaIdx.kvStore :=
  letI := S A; Effect.noop

@[simp] def kvStoreSetGuard
    (inp : @GuardInput (S A) AnomaIdx.kvStore) :
    Option (A.StorageKey × A.StorageValue) :=
  match @GuardInput.msg (S A) _ inp with
  | .setReq key val => some (key, val)
  | _ => none

def kvStoreSetAction
    (w : A.StorageKey × A.StorageValue)
    (inp : @GuardInput (S A) AnomaIdx.kvStore)
    (_ : kvStoreSetGuard A inp = some w) :
    @Effect (S A) AnomaIdx.kvStore :=
  letI := S A; Effect.noop

@[simp] def kvStoreDeleteGuard
    (inp : @GuardInput (S A) AnomaIdx.kvStore) :
    Option A.StorageKey :=
  match @GuardInput.msg (S A) _ inp with
  | .deleteReq key => some key
  | _ => none

def kvStoreDeleteAction
    (w : A.StorageKey)
    (inp : @GuardInput (S A) AnomaIdx.kvStore)
    (_ : kvStoreDeleteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.kvStore :=
  letI := S A; Effect.noop

def kvStoreActions : @Behaviour (S A) AnomaIdx.kvStore :=
  letI := S A
  [ { Witness := A.StorageKey
      guard := kvStoreGetGuard A
      action := kvStoreGetAction A }
  , { Witness := A.StorageKey × A.StorageValue
      guard := kvStoreSetGuard A
      action := kvStoreSetAction A }
  , { Witness := A.StorageKey
      guard := kvStoreDeleteGuard A
      action := kvStoreDeleteAction A } ]

private theorem kvStoreNonOverlapping :
    @NonOverlappingGuards (S A) _ (kvStoreActions A) := by
  letI := S A; intro inp
  simp only [kvStoreActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def kvStoreBehaviour : @WellFormedBehaviour (S A) AnomaIdx.kvStore :=
  letI := S A
  { actions := kvStoreActions A
    nonOverlapping := kvStoreNonOverlapping A }

-- ============================================================================
-- § TSStore Behaviour
-- ============================================================================

@[simp] def tsStoreRecordGuard
    (inp : @GuardInput (S A) AnomaIdx.tsStore) :
    Option (A.StorageKey × A.StorageValue) :=
  match @GuardInput.msg (S A) _ inp with
  | .recordReq key val => some (key, val)
  | _ => none

def tsStoreRecordAction
    (w : A.StorageKey × A.StorageValue)
    (inp : @GuardInput (S A) AnomaIdx.tsStore)
    (_ : tsStoreRecordGuard A inp = some w) :
    @Effect (S A) AnomaIdx.tsStore :=
  letI := S A; Effect.noop

@[simp] def tsStoreQueryGuard
    (inp : @GuardInput (S A) AnomaIdx.tsStore) :
    Option A.StorageKey :=
  match @GuardInput.msg (S A) _ inp with
  | .queryReq key => some key
  | _ => none

def tsStoreQueryAction
    (w : A.StorageKey)
    (inp : @GuardInput (S A) AnomaIdx.tsStore)
    (_ : tsStoreQueryGuard A inp = some w) :
    @Effect (S A) AnomaIdx.tsStore :=
  letI := S A; Effect.noop

@[simp] def tsStoreDeleteGuard
    (inp : @GuardInput (S A) AnomaIdx.tsStore) :
    Option A.StorageKey :=
  match @GuardInput.msg (S A) _ inp with
  | .deleteReq key => some key
  | _ => none

def tsStoreDeleteAction
    (w : A.StorageKey)
    (inp : @GuardInput (S A) AnomaIdx.tsStore)
    (_ : tsStoreDeleteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.tsStore :=
  letI := S A; Effect.noop

def tsStoreActions : @Behaviour (S A) AnomaIdx.tsStore :=
  letI := S A
  [ { Witness := A.StorageKey × A.StorageValue
      guard := tsStoreRecordGuard A
      action := tsStoreRecordAction A }
  , { Witness := A.StorageKey
      guard := tsStoreQueryGuard A
      action := tsStoreQueryAction A }
  , { Witness := A.StorageKey
      guard := tsStoreDeleteGuard A
      action := tsStoreDeleteAction A } ]

private theorem tsStoreNonOverlapping :
    @NonOverlappingGuards (S A) _ (tsStoreActions A) := by
  letI := S A; intro inp
  simp only [tsStoreActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def tsStoreBehaviour : @WellFormedBehaviour (S A) AnomaIdx.tsStore :=
  letI := S A
  { actions := tsStoreActions A
    nonOverlapping := tsStoreNonOverlapping A }

-- ============================================================================
-- § Storage Behaviour (stub)
-- ============================================================================

def storageBehaviour : @WellFormedBehaviour (S A) AnomaIdx.storage :=
  letI := S A
  { actions := []
    nonOverlapping := by intro inp; simp [List.filter] }

end MailboxActors.Examples.Anoma.Infra
