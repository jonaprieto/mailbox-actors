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
MailboxActors framework. Each engine is specified as a `WellFormedBehaviour`
with guarded actions and a machine-checked `NonOverlappingGuards` proof.

## Subsystems

- **Ordering** (3 engines): `txOrdering`, `shard`, `executor` —
  Transaction ordering via gensym-based fingerprinting and DAG-based MVCC.
- **Identity** (8 engines): `identity`, `commitment`, `decryption`,
  `verification`, `encryption`, `signDeleg`, `readDeleg`, `nameRegistry` —
  Cryptographic identity lifecycle, delegation, and evidence management.
- **Network** (6 engines): `router`, `transport`, `protocol`,
  `connection`, `peerRegistry`, `pubsub` —
  Inter-node message routing with layered transport and pub/sub.
- **Infrastructure** (6 engines): `ticker`, `wallClock`, `logging`,
  `kvStore`, `tsStore`, `storage` —
  Shared services: time, logging, key-value and blob storage.

## Design decisions

- **Opaque types**: All domain types are abstract via `AnomaTypes`, keeping
  the specification representation-independent. Operations like `sign`,
  `encrypt_`, `fingerprintSucc` are carried as fields of `AnomaTypes`.
- **Finite engine index**: `AnomaIdx` is a `Fintype` with 23 constructors.
- **Parameterized spec**: `anomaEngineSpec (A : AnomaTypes)` provides the
  `EngineSpec` instance. All engines are parameterized over `A`.
- **Trivial mailbox**: All engines use FIFO pass-through mailbox semantics
  (`mailboxContains := True`, `mailboxRemove := id`).
- **Same-type unwrap**: `unwrap` casts messages between engines of the same
  type; cross-type messages return `none`.

## Module structure

Each engine has a `Types.lean` (messages, config, state) and a
`Behaviour.lean` (guards, actions, well-formedness proof), organized
in per-engine subdirectories under each subsystem.
-/
