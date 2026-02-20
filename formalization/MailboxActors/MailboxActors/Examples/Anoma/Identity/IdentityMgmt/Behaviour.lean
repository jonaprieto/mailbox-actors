import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Identity Management Engine -- Behaviour

## Generate Request

When `generateReq` arrives with a backend and capability, the identity
management engine increments its `nextId` counter, preparing for the
next identity generation. In a full implementation the engine would
also spawn commitment/decryption sub-engines according to the capability.

## Delete Request

When `deleteReq` arrives, the engine acknowledges the deletion request.
The actual teardown of sub-engines is left abstract.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Identity Management Behaviour
-- ============================================================================

/-- Guard for `generateReq` messages. -/
@[simp] def identityGenerateGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option (A.Backend × Capability) :=
  match @GuardInput.msg (S A) _ inp with
  | .generateReq backend cap => some (backend, cap)
  | _ => none

/-- Action for `generateReq`: increment `nextId` in the local state,
    reserving an identity slot for the new external identity. -/
def identityGenerateAction
    (w : A.Backend × Capability)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityGenerateGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with nextId := st.nextId + 1 } }

/-- Guard for `deleteReq` messages. -/
@[simp] def identityDeleteGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .deleteReq eid => some eid
  | _ => none

/-- Action for `deleteReq`: no-op for now. In a full implementation this
    would terminate the commitment/decryption sub-engines associated
    with the deleted identity. -/
def identityDeleteAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityDeleteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A; Effect.noop

def identityActions : @Behaviour (S A) AnomaIdx.identity :=
  letI := S A
  [ { Witness := A.Backend × Capability
      guard := identityGenerateGuard A
      action := identityGenerateAction A }
  , { Witness := A.ExternalIdentity
      guard := identityDeleteGuard A
      action := identityDeleteAction A } ]

private theorem identityNonOverlapping :
    @NonOverlappingGuards (S A) _ (identityActions A) := by
  letI := S A; intro inp
  simp only [identityActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def identityBehaviour : @WellFormedBehaviour (S A) AnomaIdx.identity :=
  letI := S A
  { actions := identityActions A
    nonOverlapping := identityNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
