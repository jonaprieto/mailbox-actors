import MailboxActors.Examples.Anoma.Identity.IdentityMgmt.Types
import MailboxActors.Examples.Anoma.Identity.Commitment.Types
import MailboxActors.Examples.Anoma.Identity.Decryption.Types
import MailboxActors.Examples.Anoma.Identity.Verification.Types
import MailboxActors.Examples.Anoma.Identity.Encryption.Types
import MailboxActors.Examples.Anoma.Identity.SignDeleg.Types
import MailboxActors.Examples.Anoma.Identity.ReadDeleg.Types
import MailboxActors.Examples.Anoma.Identity.NameRegistry.Types

/-!
# Identity Subsystem — Types

Re-exports all type definitions for the eight Identity subsystem engines.

## Architecture

The identity subsystem provides cryptographic identity lifecycle management,
including key generation, delegation, and evidence-based authorization.

### Engine hierarchy

- **IdentityMgmt** is the top-level manager. On `generateReq`, it spawns
  dedicated crypto engines based on the requested `Capability`:
  - `commit` → spawns a **Commitment** engine (signature production).
  - `decrypt` → spawns a **Decryption** engine.
  - `both` → spawns both.

- **Verification** and **Encryption** engines handle external-identity
  operations (verifying signatures, encrypting for others).

- **SignDeleg**, **ReadDeleg**, and **NameRegistry** are evidence registries
  that track delegation and naming proofs. All three share the polymorphic
  `EvidenceMsg` type parameterized by the evidence kind.
-/
