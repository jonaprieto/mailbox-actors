import MailboxActors.Examples.Anoma.AnomaTypes
import Mathlib.Data.Fintype.Basic

/-!
# Engine Index — Anoma Engine Types

The finite index type enumerating all 23 Anoma engine types,
grouped into four subsystems.

## Ordering (3 engines)

Transaction ordering via gensym-based fingerprinting and DAG-based
multi-version concurrency control.

- `txOrdering` — Mempool worker: assigns fingerprints, spawns executors, tracks locks.
- `shard` — Per-key DAG manager: acquires locks, fulfills reads from preceding writes.
- `executor` — Transaction executor: runs programs, receives read replies.

## Identity (8 engines)

Cryptographic identity lifecycle, delegation, and evidence management.

- `identity` — Identity manager: generates/deletes identities, spawns crypto engines.
- `commitment` — Signature production via backend.
- `decryption` — Ciphertext decryption via backend.
- `verification` — Signature verification via backend and external identity.
- `encryption` — Plaintext encryption via backend and external identity.
- `signDeleg` — Sign-delegation evidence registry.
- `readDeleg` — Read-delegation evidence registry.
- `nameRegistry` — Name-to-identity resolution registry.

## Network (6 engines)

Message routing between local engines and remote nodes.

- `router` — Central message dispatcher: local delivery, remote forwarding.
- `transport` — Transport-layer abstraction: delegates to protocol engines.
- `protocol` — Protocol negotiation and connection lifecycle management.
- `connection` — Per-connection state: sequence numbers, send/receive.
- `peerRegistry` — Directory of known nodes and topics.
- `pubsub` — Publish/subscribe topic-based message broadcasting.

## Infrastructure (6 engines)

Shared services: time, logging, key-value storage, and blob storage.

- `ticker` — Epoch-based tick generation.
- `wallClock` — Wall-clock time queries.
- `logging` — Append-only log accumulation.
- `kvStore` — Key-value store: get, set, delete.
- `tsStore` — Time-series store: record, query, delete.
- `storage` — Blob storage: chunk-addressed get/put.
-/

namespace MailboxActors.Examples.Anoma

/-- The 23 Anoma engine types, grouped into four subsystems:
    Ordering (3), Identity (8), Network (6), Infrastructure (6). -/
inductive AnomaIdx where
  -- Ordering (3)
  | txOrdering | shard | executor
  -- Identity (8)
  | identity | commitment | decryption
  | verification | encryption
  | signDeleg | readDeleg | nameRegistry
  -- Network (6)
  | router | transport | protocol
  | connection | peerRegistry | pubsub
  -- Infrastructure (6)
  | ticker | wallClock | logging
  | kvStore | tsStore | storage
  deriving DecidableEq, Repr

instance
    : Fintype AnomaIdx
    where
  elems := { .txOrdering, .shard, .executor,
             .identity, .commitment, .decryption,
             .verification, .encryption,
             .signDeleg, .readDeleg, .nameRegistry,
             .router, .transport, .protocol,
             .connection, .peerRegistry, .pubsub,
             .ticker, .wallClock, .logging,
             .kvStore, .tsStore, .storage }
  complete x := by cases x <;> simp

end MailboxActors.Examples.Anoma
