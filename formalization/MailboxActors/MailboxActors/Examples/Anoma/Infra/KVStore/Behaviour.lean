import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# KVStore Engine — Behaviour
-/

namespace MailboxActors.Examples.Anoma.Infra

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

@[simp] def kvStoreGetGuard
    (inp : @GuardInput (S A) AnomaIdx.kvStore) :
    Option A.StorageKey :=
  match @GuardInput.msg (S A) _ inp with
  | .getReq key => some key
  | _ => none

/-- Action for `getReq`: in a full implementation, would look up the key
    and reply with the value. -/
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

/-- Action for `setReq`: update the entry count. -/
def kvStoreSetAction
    (w : A.StorageKey × A.StorageValue)
    (inp : @GuardInput (S A) AnomaIdx.kvStore)
    (_ : kvStoreSetGuard A inp = some w) :
    @Effect (S A) AnomaIdx.kvStore :=
  letI := S A
  let env := inp.env
  Effect.update { env with
    localState := { entryCount := env.localState.entryCount + 1 } }

@[simp] def kvStoreDeleteGuard
    (inp : @GuardInput (S A) AnomaIdx.kvStore) :
    Option A.StorageKey :=
  match @GuardInput.msg (S A) _ inp with
  | .deleteReq key => some key
  | _ => none

/-- Action for `deleteReq`: decrement the entry count. -/
def kvStoreDeleteAction
    (w : A.StorageKey)
    (inp : @GuardInput (S A) AnomaIdx.kvStore)
    (_ : kvStoreDeleteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.kvStore :=
  letI := S A
  let env := inp.env
  Effect.update { env with
    localState := { entryCount := env.localState.entryCount - 1 } }

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

end MailboxActors.Examples.Anoma.Infra
