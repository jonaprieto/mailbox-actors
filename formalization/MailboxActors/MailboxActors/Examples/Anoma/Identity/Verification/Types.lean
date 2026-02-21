import MailboxActors.Examples.Anoma.EngIdx
import MailboxActors.Basic

/-!
# Verification Engine — Types

The verification engine verifies digital signatures. It supports
both direct verification and signs-for-aware verification that
checks delegation chains.

When `verifyReq` arrives, the engine computes
`A.verify_ backend eid signable signature` and sends the result
as `IdentityMsg.verifyResult` to the identity manager at `replyTo`.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Messages for the verification engine.
- `verifyReq`: Request to verify a signature. The `Bool` flag indicates
  whether to use signs-for delegation awareness. Carries `replyTo`
  for cross-type reply to the identity manager.
- `verifyReply`: Response with verification result. -/
inductive VerificationMsg where
  | verifyReq : A.ExternalIdentity → A.Signable → A.Signature → Bool
      → MailboxActors.Address → VerificationMsg
  | verifyReply : Bool → VerificationMsg
  deriving DecidableEq, BEq

/-- Configuration for the verification engine.
- `backend`: The cryptographic backend for verification. -/
structure VerificationCfg where
  backend : A.Backend

abbrev VerificationState := Unit

end MailboxActors.Examples.Anoma.Identity
