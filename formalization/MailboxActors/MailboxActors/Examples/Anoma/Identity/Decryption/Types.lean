import MailboxActors.Examples.Anoma.EngIdx

/-!
# Decryption Engine — Types

The decryption engine decrypts ciphertext using a backend
cryptographic provider. Each decryption engine is associated
with a single identity.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Messages for the decryption engine.
- `decryptReq`: Request to decrypt ciphertext.
- `decryptReply`: Response with the decrypted plaintext. -/
inductive DecryptionMsg where
  | decryptReq : A.Ciphertext → DecryptionMsg
  | decryptReply : A.Plaintext → DecryptionMsg
  deriving DecidableEq, BEq

/-- Configuration for the decryption engine.
- `backend`: The cryptographic backend for decryption operations. -/
structure DecryptionCfg where
  backend : A.Backend

abbrev DecryptionState := Unit

end MailboxActors.Examples.Anoma.Identity
