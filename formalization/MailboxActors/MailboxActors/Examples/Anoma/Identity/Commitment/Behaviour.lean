import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Commitment Engine — Behaviour

## Sign Request

When `signReq` arrives with signable data and a reply address, the
commitment engine computes the signature using `A.sign backend signable`
and sends the result as `IdentityMsg.signResult` to the identity
manager via cross-type `Effect.send .identity`.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Commitment Behaviour
-- ============================================================================

/-- Guard for `signReq` messages. Extracts the signable data and
    the identity manager's reply address. -/
@[simp] def commitmentSignGuard
    (inp : @GuardInput (S A) AnomaIdx.commitment) :
    Option (A.Signable × Address) :=
  match @GuardInput.msg (S A) _ inp with
  | .signReq s replyTo => some (s, replyTo)
  | _ => none

/-- Action for `signReq`: compute `A.sign backend signable` and send
    the signature to the identity manager as `IdentityMsg.signResult`.

    The backend is accessed from the engine's configuration
    (`inp.config.cfg.backend`). -/
def commitmentSignAction
    (w : A.Signable × Address)
    (inp : @GuardInput (S A) AnomaIdx.commitment)
    (_ : commitmentSignGuard A inp = some w) :
    @Effect (S A) AnomaIdx.commitment :=
  letI := S A
  let signable := w.1
  let replyTo := w.2
  let backend := inp.config.cfg.backend
  let sig := A.sign backend signable
  Effect.send AnomaIdx.identity replyTo (.signResult sig)

def commitmentActions : @Behaviour (S A) AnomaIdx.commitment :=
  letI := S A
  [ { Witness := A.Signable × Address
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
