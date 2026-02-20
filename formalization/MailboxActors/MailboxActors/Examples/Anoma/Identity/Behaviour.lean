import MailboxActors.Examples.Anoma.Identity.IdentityMgmt.Behaviour
import MailboxActors.Examples.Anoma.Identity.Commitment.Behaviour
import MailboxActors.Examples.Anoma.Identity.Decryption.Behaviour
import MailboxActors.Examples.Anoma.Identity.Verification.Behaviour
import MailboxActors.Examples.Anoma.Identity.Encryption.Behaviour
import MailboxActors.Examples.Anoma.Identity.SignDeleg.Behaviour
import MailboxActors.Examples.Anoma.Identity.ReadDeleg.Behaviour
import MailboxActors.Examples.Anoma.Identity.NameRegistry.Behaviour

/-!
# Identity Subsystem — Behaviours

Re-exports all behaviour definitions for the Identity subsystem engines.

## Implemented actions

- **IdentityMgmt**: `generateReq` increments the identity counter;
  `deleteReq` is abstract (noop).
- **Commitment / Decryption / Verification / Encryption**: Guards extract
  the crypto request; actions are abstract pending sender-address support
  in `GuardInput` (needed for `Effect.send` replies).
- **SignDeleg / ReadDeleg / NameRegistry**: `submit` increments evidence
  count; `query` is abstract (noop).
-/
