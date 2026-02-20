import MailboxActors.Examples.Anoma.EngIdx
import MailboxActors.Examples.Anoma.Identity.SignDeleg.Types

/-!
# Name Registry Engine — Types

The name registry engine manages the mapping from human-readable
identity names to cryptographic identities. It functions as a
decentralized DNS-like system.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

abbrev NameRegistryMsg := EvidenceMsg A A.NameEvidence
abbrev NameRegistryCfg := Unit

/-- Local state for the name registry engine.
- `registrationCount`: Number of name registrations. -/
structure NameRegistryState where
  registrationCount : Nat

end MailboxActors.Examples.Anoma.Identity
