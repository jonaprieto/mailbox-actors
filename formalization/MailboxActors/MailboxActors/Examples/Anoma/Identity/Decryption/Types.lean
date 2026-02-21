import MailboxActors.Examples.Anoma.EngIdx
import MailboxActors.Basic

/-!
# Decryption Engine — Types

The decryption engine decrypts ciphertext using a backend
cryptographic provider. Each decryption engine is associated
with a single identity.

When `decryptReq` arrives, the engine computes
`A.decrypt_ backend ciphertext` and sends the result as
`IdentityMsg.decryptResult` to the identity manager at `replyTo`.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Messages for the decryption engine.
- `decryptReq`: Request to decrypt ciphertext. Carries `replyTo`
  (the identity manager's address) for cross-type reply.
- `decryptReply`: Response with the decrypted plaintext. -/
inductive DecryptionMsg where
  | decryptReq : A.Ciphertext → MailboxActors.Address → DecryptionMsg
  | decryptReply : A.Plaintext → DecryptionMsg
  deriving DecidableEq, BEq

/-- Configuration for the decryption engine.
- `backend`: The cryptographic backend for decryption operations. -/
structure DecryptionCfg where
  backend : A.Backend

abbrev DecryptionState := Unit

end MailboxActors.Examples.Anoma.Identity
