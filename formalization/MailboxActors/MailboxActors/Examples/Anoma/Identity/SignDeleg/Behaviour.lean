import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# SignsFor Delegation Engine -- Behaviour

## Submit

When `submit` arrives with sign-evidence, the engine records the
evidence by incrementing `evidenceCount` in the local state.

## Query

When `query` arrives with an external identity, the engine should look
up whether a signs-for delegation relationship exists. Currently `noop`
because the reply would require the sender address.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § SignDeleg Behaviour
-- ============================================================================

/-- Guard for `query` messages. -/
@[simp] def signDelegQueryGuard
    (inp : @GuardInput (S A) AnomaIdx.signDeleg) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .query eid => some eid
  | _ => none

/-- Action for `query`: intended to look up the signs-for relationship
    and reply with `EvidenceMsg.reply`. Currently `noop` because the
    sender address is not available in `GuardInput`. -/
def signDelegQueryAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.signDeleg)
    (_ : signDelegQueryGuard A inp = some w) :
    @Effect (S A) AnomaIdx.signDeleg :=
  letI := S A; Effect.noop

/-- Guard for `submit` messages. -/
@[simp] def signDelegSubmitGuard
    (inp : @GuardInput (S A) AnomaIdx.signDeleg) :
    Option A.SignEvidence :=
  match @GuardInput.msg (S A) _ inp with
  | .submit ev => some ev
  | _ => none

/-- Action for `submit`: increment `evidenceCount` to record the
    newly submitted delegation evidence. -/
def signDelegSubmitAction
    (w : A.SignEvidence)
    (inp : @GuardInput (S A) AnomaIdx.signDeleg)
    (_ : signDelegSubmitGuard A inp = some w) :
    @Effect (S A) AnomaIdx.signDeleg :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with evidenceCount := st.evidenceCount + 1 } }

def signDelegActions : @Behaviour (S A) AnomaIdx.signDeleg :=
  letI := S A
  [ { Witness := A.ExternalIdentity
      guard := signDelegQueryGuard A
      action := signDelegQueryAction A }
  , { Witness := A.SignEvidence
      guard := signDelegSubmitGuard A
      action := signDelegSubmitAction A } ]

private theorem signDelegNonOverlapping :
    @NonOverlappingGuards (S A) _ (signDelegActions A) := by
  letI := S A; intro inp
  simp only [signDelegActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def signDelegBehaviour : @WellFormedBehaviour (S A) AnomaIdx.signDeleg :=
  letI := S A
  { actions := signDelegActions A
    nonOverlapping := signDelegNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
