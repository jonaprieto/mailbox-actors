import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Name Registry Engine -- Behaviour

## Submit

When `submit` arrives with name-evidence, the engine records the
registration by incrementing `registrationCount` in the local state.

## Query

When `query` arrives with an external identity, the engine should look
up the registered name mapping. Currently `noop` because the reply
would require the sender address.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § NameRegistry Behaviour
-- ============================================================================

/-- Guard for `query` messages. -/
@[simp] def nameRegistryQueryGuard
    (inp : @GuardInput (S A) AnomaIdx.nameRegistry) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .query eid => some eid
  | _ => none

/-- Action for `query`: intended to look up the name registration
    and reply with `EvidenceMsg.reply`. Currently `noop` because the
    sender address is not available in `GuardInput`. -/
def nameRegistryQueryAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.nameRegistry)
    (_ : nameRegistryQueryGuard A inp = some w) :
    @Effect (S A) AnomaIdx.nameRegistry :=
  letI := S A; Effect.noop

/-- Guard for `submit` messages. -/
@[simp] def nameRegistrySubmitGuard
    (inp : @GuardInput (S A) AnomaIdx.nameRegistry) :
    Option A.NameEvidence :=
  match @GuardInput.msg (S A) _ inp with
  | .submit ev => some ev
  | _ => none

/-- Action for `submit`: increment `registrationCount` to record the
    newly submitted name registration evidence. -/
def nameRegistrySubmitAction
    (w : A.NameEvidence)
    (inp : @GuardInput (S A) AnomaIdx.nameRegistry)
    (_ : nameRegistrySubmitGuard A inp = some w) :
    @Effect (S A) AnomaIdx.nameRegistry :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with registrationCount := st.registrationCount + 1 } }

def nameRegistryActions : @Behaviour (S A) AnomaIdx.nameRegistry :=
  letI := S A
  [ { Witness := A.ExternalIdentity
      guard := nameRegistryQueryGuard A
      action := nameRegistryQueryAction A }
  , { Witness := A.NameEvidence
      guard := nameRegistrySubmitGuard A
      action := nameRegistrySubmitAction A } ]

private theorem nameRegistryNonOverlapping :
    @NonOverlappingGuards (S A) _ (nameRegistryActions A) := by
  letI := S A; intro inp
  simp only [nameRegistryActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def nameRegistryBehaviour : @WellFormedBehaviour (S A) AnomaIdx.nameRegistry :=
  letI := S A
  { actions := nameRegistryActions A
    nonOverlapping := nameRegistryNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
