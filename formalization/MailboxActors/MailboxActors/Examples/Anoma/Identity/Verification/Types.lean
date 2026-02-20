import MailboxActors.Examples.Anoma.EngIdx

/-!
# Verification Engine — Types

The verification engine verifies digital signatures. It supports
both direct verification and signs-for-aware verification that
checks delegation chains.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Messages for the verification engine.
- `verifyReq`: Request to verify a signature. The `Bool` flag indicates
  whether to use signs-for delegation awareness.
- `verifyReply`: Response with verification result. -/
inductive VerificationMsg where
  | verifyReq : A.ExternalIdentity → A.Signable → A.Signature → Bool → VerificationMsg
  | verifyReply : Bool → VerificationMsg
  deriving DecidableEq, BEq

/-- Configuration for the verification engine.
- `backend`: The cryptographic backend for verification. -/
structure VerificationCfg where
  backend : A.Backend

abbrev VerificationState := Unit

end MailboxActors.Examples.Anoma.Identity
