import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Encryption Engine — Behaviour

## Encrypt Request

When `encryptReq` arrives with `(eid, plaintext, useRF, replyTo)`,
the encryption engine computes `A.encrypt_ backend eid plaintext`
and sends the result as `IdentityMsg.encryptResult` to the identity
manager via cross-type `Effect.send .identity`.

If `useRF` is true, the engine should also consult the reads-for
delegation engine to resolve the actual target identity before
encrypting. This delegation-aware encryption is left abstract.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Encryption Behaviour
-- ============================================================================

/-- Guard for `encryptReq` messages. Extracts the target identity,
    plaintext, reads-for flag, and reply address. -/
@[simp] def encryptionGuard
    (inp : @GuardInput (S A) AnomaIdx.encryption) :
    Option (A.ExternalIdentity × A.Plaintext × Bool × Address) :=
  match @GuardInput.msg (S A) _ inp with
  | .encryptReq eid pt useRF replyTo => some (eid, pt, useRF, replyTo)
  | _ => none

/-- Action for `encryptReq`: compute `A.encrypt_ backend eid plaintext`
    and send the ciphertext to the identity manager as
    `IdentityMsg.encryptResult`. -/
def encryptionAction
    (w : A.ExternalIdentity × A.Plaintext × Bool × Address)
    (inp : @GuardInput (S A) AnomaIdx.encryption)
    (_ : encryptionGuard A inp = some w) :
    @Effect (S A) AnomaIdx.encryption :=
  letI := S A
  let eid := w.1
  let pt := w.2.1
  let replyTo := w.2.2.2
  let backend := inp.config.cfg.backend
  let ct := A.encrypt_ backend eid pt
  Effect.send AnomaIdx.identity replyTo (.encryptResult ct)

def encryptionActions : @Behaviour (S A) AnomaIdx.encryption :=
  letI := S A
  [ { Witness := A.ExternalIdentity × A.Plaintext × Bool × Address
      guard := encryptionGuard A
      action := encryptionAction A } ]

private theorem encryptionNonOverlapping :
    @NonOverlappingGuards (S A) _ (encryptionActions A) := by
  letI := S A; intro inp
  simp only [encryptionActions, List.filter]
  split <;> simp

def encryptionBehaviour : @WellFormedBehaviour (S A) AnomaIdx.encryption :=
  letI := S A
  { actions := encryptionActions A
    nonOverlapping := encryptionNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
