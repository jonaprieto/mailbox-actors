import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Encryption Engine -- Behaviour

## Encrypt Request

When `encryptReq` arrives with `(eid, plaintext, useRF)`, the encryption
engine should compute `A.encrypt_ inp.config.cfg.backend eid plaintext`
and reply with `EncryptionMsg.encryptReply ciphertext`. If `useRF` is
true, the engine should also consult the reads-for delegation engine
to resolve the actual target identity before encrypting.

Currently the action is `Effect.noop` because the framework's `GuardInput`
does not carry the sender address, so we cannot construct the
`Effect.send` target.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Encryption Behaviour
-- ============================================================================

/-- Guard for `encryptReq` messages. -/
@[simp] def encryptionGuard
    (inp : @GuardInput (S A) AnomaIdx.encryption) :
    Option (A.ExternalIdentity × A.Plaintext × Bool) :=
  match @GuardInput.msg (S A) _ inp with
  | .encryptReq eid pt useRF => some (eid, pt, useRF)
  | _ => none

/-- Action for `encryptReq`: intended to compute
    `A.encrypt_ backend eid plaintext` and reply with
    `EncryptionMsg.encryptReply`. Currently `noop` because the sender
    address is not available in `GuardInput`. -/
def encryptionAction
    (w : A.ExternalIdentity × A.Plaintext × Bool)
    (inp : @GuardInput (S A) AnomaIdx.encryption)
    (_ : encryptionGuard A inp = some w) :
    @Effect (S A) AnomaIdx.encryption :=
  letI := S A; Effect.noop

def encryptionActions : @Behaviour (S A) AnomaIdx.encryption :=
  letI := S A
  [ { Witness := A.ExternalIdentity × A.Plaintext × Bool
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
