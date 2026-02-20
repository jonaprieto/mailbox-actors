import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Decryption Engine -- Behaviour

## Decrypt Request

When `decryptReq` arrives with ciphertext, the decryption engine should
compute `A.decrypt_ inp.config.cfg.backend ct` and reply with
`DecryptionMsg.decryptReply`. The cryptographic backend is available
via `inp.config.cfg.backend`.

Currently the action is `Effect.noop` because the framework's `GuardInput`
does not carry the sender address, so we cannot construct the
`Effect.send` target.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Decryption Behaviour
-- ============================================================================

/-- Guard for `decryptReq` messages. -/
@[simp] def decryptionGuard
    (inp : @GuardInput (S A) AnomaIdx.decryption) :
    Option A.Ciphertext :=
  match @GuardInput.msg (S A) _ inp with
  | .decryptReq ct => some ct
  | _ => none

/-- Action for `decryptReq`: intended to compute
    `A.decrypt_ backend ciphertext` and reply with
    `DecryptionMsg.decryptReply`. Currently `noop` because the sender
    address is not available in `GuardInput`. -/
def decryptionAction
    (w : A.Ciphertext)
    (inp : @GuardInput (S A) AnomaIdx.decryption)
    (_ : decryptionGuard A inp = some w) :
    @Effect (S A) AnomaIdx.decryption :=
  letI := S A; Effect.noop

def decryptionActions : @Behaviour (S A) AnomaIdx.decryption :=
  letI := S A
  [ { Witness := A.Ciphertext
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
