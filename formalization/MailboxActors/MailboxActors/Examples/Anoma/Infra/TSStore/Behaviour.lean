import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# TSStore Engine — Behaviour

The time-series store engine maintains time-indexed data series.
It supports recording new data points, querying existing series,
and deleting series.
-/

namespace MailboxActors.Examples.Anoma.Infra

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

/-- Guard for `recordReq` messages. -/
@[simp] def tsStoreRecordGuard
    (inp : @GuardInput (S A) AnomaIdx.tsStore) :
    Option (A.StorageKey × A.StorageValue) :=
  match @GuardInput.msg (S A) _ inp with
  | .recordReq key val => some (key, val)
  | _ => none

/-- Action for `recordReq`: increment the series count. -/
def tsStoreRecordAction
    (w : A.StorageKey × A.StorageValue)
    (inp : @GuardInput (S A) AnomaIdx.tsStore)
    (_ : tsStoreRecordGuard A inp = some w) :
    @Effect (S A) AnomaIdx.tsStore :=
  letI := S A
  let env := inp.env
  Effect.update { env with
    localState := { seriesCount := env.localState.seriesCount + 1 } }

/-- Guard for `queryReq` messages. -/
@[simp] def tsStoreQueryGuard
    (inp : @GuardInput (S A) AnomaIdx.tsStore) :
    Option A.StorageKey :=
  match @GuardInput.msg (S A) _ inp with
  | .queryReq key => some key
  | _ => none

/-- Action for `queryReq`: no-op (response requires sender address). -/
def tsStoreQueryAction
    (w : A.StorageKey)
    (inp : @GuardInput (S A) AnomaIdx.tsStore)
    (_ : tsStoreQueryGuard A inp = some w) :
    @Effect (S A) AnomaIdx.tsStore :=
  letI := S A; Effect.noop

/-- Guard for `deleteReq` messages. -/
@[simp] def tsStoreDeleteGuard
    (inp : @GuardInput (S A) AnomaIdx.tsStore) :
    Option A.StorageKey :=
  match @GuardInput.msg (S A) _ inp with
  | .deleteReq key => some key
  | _ => none

/-- Action for `deleteReq`: decrement the series count. -/
def tsStoreDeleteAction
    (w : A.StorageKey)
    (inp : @GuardInput (S A) AnomaIdx.tsStore)
    (_ : tsStoreDeleteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.tsStore :=
  letI := S A
  let env := inp.env
  Effect.update { env with
    localState := { seriesCount := env.localState.seriesCount - 1 } }

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

end MailboxActors.Examples.Anoma.Infra
