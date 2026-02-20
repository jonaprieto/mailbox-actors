import MailboxActors.Examples.Anoma.EngIdx

/-!
# Encryption Engine — Types

The encryption engine encrypts plaintext for a target identity.
It supports both direct encryption and reads-for-aware encryption
that respects delegation chains.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Messages for the encryption engine.
- `encryptReq`: Request to encrypt plaintext for a target identity.
  The `Bool` flag indicates whether to use reads-for delegation awareness.
- `encryptReply`: Response with the produced ciphertext. -/
inductive EncryptionMsg where
  | encryptReq : A.ExternalIdentity → A.Plaintext → Bool → EncryptionMsg
  | encryptReply : A.Ciphertext → EncryptionMsg
  deriving DecidableEq, BEq

/-- Configuration for the encryption engine.
- `backend`: The cryptographic backend for encryption. -/
structure EncryptionCfg where
  backend : A.Backend

abbrev EncryptionState := Unit

end MailboxActors.Examples.Anoma.Identity
