import MailboxActors.Examples.Anoma.AnomaTypes
import MailboxActors.Examples.Anoma.EngIdx
import MailboxActors.Examples.Anoma.Ordering.Types
import MailboxActors.Examples.Anoma.Identity.Types
import MailboxActors.Examples.Anoma.Network.Types
import MailboxActors.Examples.Anoma.Infra.Types
import MailboxActors.Examples.Anoma.Spec
import MailboxActors.Examples.Anoma.Ordering.Behaviour
import MailboxActors.Examples.Anoma.Identity.Behaviour
import MailboxActors.Examples.Anoma.Network.Behaviour
import MailboxActors.Examples.Anoma.Infra.Behaviour

/-!
# Anoma Protocol — Lean 4 Formalization

Formal specification of the 23 Anoma protocol engines using the
MailboxActors framework.

## Subsystems

- **Ordering** (3 engines): `txOrdering`, `shard`, `executor`
- **Identity** (8 engines): `identity`, `commitment`, `decryption`,
  `verification`, `encryption`, `signDeleg`, `readDeleg`, `nameRegistry`
- **Network** (6 engines): `router`, `transport`, `protocol`,
  `connection`, `peerRegistry`, `pubsub`
- **Infrastructure** (6 engines): `ticker`, `wallClock`, `logging`,
  `kvStore`, `tsStore`, `storage`

## Key design decisions

- All domain types are opaque via `AnomaTypes`
- `AnomaIdx` is a finite type
- `anomaEngineSpec A` provides the `EngineSpec` instance
- All engines use trivial mailbox semantics (FIFO pass-through)
- `unwrap` is same-type identity cast
-/
