import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Verification Engine — Behaviour

## Verify Request

When `verifyReq` arrives with `(eid, signable, signature, useSF, replyTo)`,
the verification engine computes
`A.verify_ backend eid signable signature` and sends the result as
`IdentityMsg.verifyResult` to the identity manager.

If `useSF` is true, the engine should also consult the signs-for
delegation engine before replying. This delegation-aware verification
is left abstract (the direct verification result is sent regardless).
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Verification Behaviour
-- ============================================================================

/-- Guard for `verifyReq` messages. Extracts the external identity,
    signable data, signature, signs-for flag, and reply address. -/
@[simp] def verificationGuard
    (inp : @GuardInput (S A) AnomaIdx.verification) :
    Option (A.ExternalIdentity × A.Signable × A.Signature × Bool × Address) :=
  match @GuardInput.msg (S A) _ inp with
  | .verifyReq eid s sig useSF replyTo => some (eid, s, sig, useSF, replyTo)
  | _ => none

/-- Action for `verifyReq`: compute `A.verify_ backend eid signable sig`
    and send the result to the identity manager as
    `IdentityMsg.verifyResult`. -/
def verificationAction
    (w : A.ExternalIdentity × A.Signable × A.Signature × Bool × Address)
    (inp : @GuardInput (S A) AnomaIdx.verification)
    (_ : verificationGuard A inp = some w) :
    @Effect (S A) AnomaIdx.verification :=
  letI := S A
  let eid := w.1
  let signable := w.2.1
  let sig := w.2.2.1
  let replyTo := w.2.2.2.2
  let backend := inp.config.cfg.backend
  let result := A.verify_ backend eid signable sig
  Effect.send AnomaIdx.identity replyTo (.verifyResult result)

def verificationActions : @Behaviour (S A) AnomaIdx.verification :=
  letI := S A
  [ { Witness := A.ExternalIdentity × A.Signable × A.Signature × Bool × Address
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
