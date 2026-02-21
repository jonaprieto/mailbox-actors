import MailboxActors.Examples.Anoma.EngIdx
import MailboxActors.Basic

/-!
# Encryption Engine — Types

The encryption engine encrypts plaintext for a target identity.
It supports both direct encryption and reads-for-aware encryption
that respects delegation chains.

When `encryptReq` arrives, the engine computes
`A.encrypt_ backend eid plaintext` and sends the result as
`IdentityMsg.encryptResult` to the identity manager at `replyTo`.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Messages for the encryption engine.
- `encryptReq`: Request to encrypt plaintext for a target identity.
  The `Bool` flag indicates whether to use reads-for delegation awareness.
  Carries `replyTo` for cross-type reply to the identity manager.
- `encryptReply`: Response with the produced ciphertext. -/
inductive EncryptionMsg where
  | encryptReq : A.ExternalIdentity → A.Plaintext → Bool
      → MailboxActors.Address → EncryptionMsg
  | encryptReply : A.Ciphertext → EncryptionMsg
  deriving DecidableEq, BEq

/-- Configuration for the encryption engine.
- `backend`: The cryptographic backend for encryption. -/
structure EncryptionCfg where
  backend : A.Backend

abbrev EncryptionState := Unit

end MailboxActors.Examples.Anoma.Identity
