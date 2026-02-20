import MailboxActors.Examples.Anoma.EngIdx
import MailboxActors.Examples.Anoma.Identity.SignDeleg.Types

/-!
# ReadsFor Delegation Engine — Types

The reads-for delegation engine manages the reads-for relationship:
identity A can read data encrypted for identity B.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Message type for the reads-for delegation engine, instantiating
    the generic `EvidenceMsg` with `ReadEvidence`. -/
abbrev ReadDelegMsg := EvidenceMsg A A.ReadEvidence

/-- Configuration for the reads-for delegation engine (no configuration needed). -/
abbrev ReadDelegCfg := Unit

/-- Local state for the reads-for delegation engine.
- `evidenceCount`: Number of evidence items submitted. -/
structure ReadDelegState where
  evidenceCount : Nat

end MailboxActors.Examples.Anoma.Identity
