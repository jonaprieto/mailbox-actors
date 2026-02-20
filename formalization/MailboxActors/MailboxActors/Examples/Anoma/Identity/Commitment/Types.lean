import MailboxActors.Examples.Anoma.EngIdx

/-!
# Commitment Engine — Types

The commitment engine produces digital signatures using a backend
cryptographic provider. Each commitment engine is associated with
a single identity and keeps the signing key secure.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Messages for the commitment engine.
- `signReq`: Request to sign data.
- `signReply`: Response with the produced signature. -/
inductive CommitmentMsg where
  | signReq : A.Signable → CommitmentMsg
  | signReply : A.Signature → CommitmentMsg
  deriving DecidableEq, BEq

/-- Configuration for the commitment engine.
- `backend`: The cryptographic backend for signing operations. -/
structure CommitmentCfg where
  backend : A.Backend

abbrev CommitmentState := Unit

end MailboxActors.Examples.Anoma.Identity
