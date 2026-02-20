import MailboxActors.Examples.Anoma.EngIdx

/-!
# Identity Management Engine — Types

The identity management engine coordinates identity lifecycle:
generation, connection, and deletion. It spawns commitment and
decryption engines based on the requested capabilities.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Capability flags for an identity.
- `commit`: Can produce signatures (spawns a commitment engine).
- `decrypt`: Can decrypt messages (spawns a decryption engine).
- `both`: Can both sign and decrypt. -/
inductive Capability where
  | commit : Capability
  | decrypt : Capability
  | both : Capability
  deriving DecidableEq, BEq

/-- Messages for the identity-management engine.
- `generateReq`: Request to generate a new identity with given backend and capabilities.
- `generateReply`: Response with the generated external identity.
- `deleteReq`: Request to delete an identity.
- `deleteReply`: Confirmation of deletion. -/
inductive IdentityMsg where
  | generateReq : A.Backend → Capability → IdentityMsg
  | generateReply : A.ExternalIdentity → IdentityMsg
  | deleteReq : A.ExternalIdentity → IdentityMsg
  | deleteReply : Bool → IdentityMsg
  deriving DecidableEq, BEq

abbrev IdentityCfg := Unit

/-- Local state for the identity-management engine.
- `nextId`: Counter for generating unique identity addresses. -/
structure IdentityState where
  nextId : Nat

end MailboxActors.Examples.Anoma.Identity
