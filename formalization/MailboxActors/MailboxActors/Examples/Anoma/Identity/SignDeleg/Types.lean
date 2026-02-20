import MailboxActors.Examples.Anoma.EngIdx

/-!
# SignsFor Delegation Engine — Types

The signs-for delegation engine manages the signs-for relationship:
identity A can sign on behalf of identity B. It stores evidence
supporting these delegation claims.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Shared message type for delegation/naming evidence engines.
    Used by `signDeleg`, `readDeleg`, and `nameRegistry`.
- `query`: Query whether a delegation/naming relationship holds.
- `reply`: Response to a query.
- `submit`: Submit new evidence for a relationship.
- `confirm`: Confirmation of evidence submission. -/
inductive EvidenceMsg (E : Type) where
  | query : A.ExternalIdentity → EvidenceMsg E
  | reply : Bool → EvidenceMsg E
  | submit : E → EvidenceMsg E
  | confirm : Bool → EvidenceMsg E
  deriving DecidableEq, BEq

abbrev SignDelegMsg := EvidenceMsg A A.SignEvidence
abbrev SignDelegCfg := Unit

/-- Local state for the signs-for delegation engine.
- `evidenceCount`: Number of evidence items submitted. -/
structure SignDelegState where
  evidenceCount : Nat

end MailboxActors.Examples.Anoma.Identity
