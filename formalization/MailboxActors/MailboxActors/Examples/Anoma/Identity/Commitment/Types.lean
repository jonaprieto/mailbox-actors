import MailboxActors.Examples.Anoma.EngIdx
import MailboxActors.Basic

/-!
# Commitment Engine — Types

The commitment engine produces digital signatures using a backend
cryptographic provider. Each commitment engine is associated with
a single identity and keeps the signing key secure.

When `signReq` arrives, the engine computes `A.sign backend signable`
and sends the result as `IdentityMsg.signResult` to the identity
manager at `replyTo`.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

/-- Messages for the commitment engine.
- `signReq`: Request to sign data. Carries `replyTo` (the identity
  manager's address) so the engine can send the result back via
  cross-type `Effect.send .identity`.
- `signReply`: Response with the produced signature (used for
  same-type forwarding within the identity subsystem). -/
inductive CommitmentMsg where
  | signReq : A.Signable → MailboxActors.Address → CommitmentMsg
  | signReply : A.Signature → CommitmentMsg
  deriving DecidableEq, BEq

/-- Configuration for the commitment engine.
- `backend`: The cryptographic backend for signing operations. -/
structure CommitmentCfg where
  backend : A.Backend

abbrev CommitmentState := Unit

end MailboxActors.Examples.Anoma.Identity
