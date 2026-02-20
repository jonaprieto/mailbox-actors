import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Commitment Engine -- Behaviour

## Sign Request

When `signReq` arrives with signable data, the commitment engine should
compute the signature using `A.sign inp.config.cfg.backend w` and send
a `CommitmentMsg.signReply` back to the requester.

Currently the action is `Effect.noop` because the framework's `GuardInput`
does not carry the sender address, so we cannot construct the
`Effect.send` target. The cryptographic backend is available via
`inp.config.cfg.backend`.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Commitment Behaviour
-- ============================================================================

/-- Guard for `signReq` messages. -/
@[simp] def commitmentSignGuard
    (inp : @GuardInput (S A) AnomaIdx.commitment) :
    Option A.Signable :=
  match @GuardInput.msg (S A) _ inp with
  | .signReq s => some s
  | _ => none

/-- Action for `signReq`: intended to compute `A.sign backend signable`
    and reply with `CommitmentMsg.signReply`. Currently `noop` because
    the sender address is not available in `GuardInput`. -/
def commitmentSignAction
    (w : A.Signable)
    (inp : @GuardInput (S A) AnomaIdx.commitment)
    (_ : commitmentSignGuard A inp = some w) :
    @Effect (S A) AnomaIdx.commitment :=
  letI := S A; Effect.noop

def commitmentActions : @Behaviour (S A) AnomaIdx.commitment :=
  letI := S A
  [ { Witness := A.Signable
      guard := commitmentSignGuard A
      action := commitmentSignAction A } ]

private theorem commitmentNonOverlapping :
    @NonOverlappingGuards (S A) _ (commitmentActions A) := by
  letI := S A; intro inp
  simp only [commitmentActions, List.filter]
  split <;> simp

def commitmentBehaviour : @WellFormedBehaviour (S A) AnomaIdx.commitment :=
  letI := S A
  { actions := commitmentActions A
    nonOverlapping := commitmentNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
