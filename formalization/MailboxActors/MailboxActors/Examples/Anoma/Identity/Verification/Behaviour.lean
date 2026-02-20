import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Verification Engine -- Behaviour

## Verify Request

When `verifyReq` arrives with `(eid, signable, signature, useSF)`, the
verification engine should compute
`A.verify_ inp.config.cfg.backend eid signable signature` and reply
with `VerificationMsg.verifyReply result`. If `useSF` is true, the engine
should also consult the signs-for delegation engine before replying.

Currently the action is `Effect.noop` because the framework's `GuardInput`
does not carry the sender address, so we cannot construct the
`Effect.send` target.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Verification Behaviour
-- ============================================================================

/-- Guard for `verifyReq` messages. -/
@[simp] def verificationGuard
    (inp : @GuardInput (S A) AnomaIdx.verification) :
    Option (A.ExternalIdentity × A.Signable × A.Signature × Bool) :=
  match @GuardInput.msg (S A) _ inp with
  | .verifyReq eid s sig useSF => some (eid, s, sig, useSF)
  | _ => none

/-- Action for `verifyReq`: intended to compute
    `A.verify_ backend eid signable signature` and reply with
    `VerificationMsg.verifyReply`. Currently `noop` because the sender
    address is not available in `GuardInput`. -/
def verificationAction
    (w : A.ExternalIdentity × A.Signable × A.Signature × Bool)
    (inp : @GuardInput (S A) AnomaIdx.verification)
    (_ : verificationGuard A inp = some w) :
    @Effect (S A) AnomaIdx.verification :=
  letI := S A; Effect.noop

def verificationActions : @Behaviour (S A) AnomaIdx.verification :=
  letI := S A
  [ { Witness := A.ExternalIdentity × A.Signable × A.Signature × Bool
      guard := verificationGuard A
      action := verificationAction A } ]

private theorem verificationNonOverlapping :
    @NonOverlappingGuards (S A) _ (verificationActions A) := by
  letI := S A; intro inp
  simp only [verificationActions, List.filter]
  split <;> simp

def verificationBehaviour : @WellFormedBehaviour (S A) AnomaIdx.verification :=
  letI := S A
  { actions := verificationActions A
    nonOverlapping := verificationNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
