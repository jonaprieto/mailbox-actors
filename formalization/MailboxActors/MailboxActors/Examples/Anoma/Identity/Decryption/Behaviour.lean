import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Decryption Engine — Behaviour

## Decrypt Request

When `decryptReq` arrives with ciphertext and a reply address, the
decryption engine computes `A.decrypt_ backend ciphertext` and sends
the result as `IdentityMsg.decryptResult` to the identity manager
via cross-type `Effect.send .identity`.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Decryption Behaviour
-- ============================================================================

/-- Guard for `decryptReq` messages. Extracts the ciphertext and
    the identity manager's reply address. -/
@[simp] def decryptionGuard
    (inp : @GuardInput (S A) AnomaIdx.decryption) :
    Option (A.Ciphertext × Address) :=
  match @GuardInput.msg (S A) _ inp with
  | .decryptReq ct replyTo => some (ct, replyTo)
  | _ => none

/-- Action for `decryptReq`: compute `A.decrypt_ backend ciphertext`
    and send the plaintext to the identity manager as
    `IdentityMsg.decryptResult`. -/
def decryptionAction
    (w : A.Ciphertext × Address)
    (inp : @GuardInput (S A) AnomaIdx.decryption)
    (_ : decryptionGuard A inp = some w) :
    @Effect (S A) AnomaIdx.decryption :=
  letI := S A
  let ct := w.1
  let replyTo := w.2
  let backend := inp.config.cfg.backend
  let pt := A.decrypt_ backend ct
  Effect.send AnomaIdx.identity replyTo (.decryptResult pt)

def decryptionActions : @Behaviour (S A) AnomaIdx.decryption :=
  letI := S A
  [ { Witness := A.Ciphertext × Address
      guard := decryptionGuard A
      action := decryptionAction A } ]

private theorem decryptionNonOverlapping :
    @NonOverlappingGuards (S A) _ (decryptionActions A) := by
  letI := S A; intro inp
  simp only [decryptionActions, List.filter]
  split <;> simp

def decryptionBehaviour : @WellFormedBehaviour (S A) AnomaIdx.decryption :=
  letI := S A
  { actions := decryptionActions A
    nonOverlapping := decryptionNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
