import MailboxActors.Examples.Anoma.EngIdx
import MailboxActors.Basic

/-!
# Shard Engine — Types

Each shard manages a subset of KVS keys with a DAG-based multi-version
concurrent control structure. The DAG tracks per-key accesses ordered by
transaction fingerprint, enabling parallel execution while maintaining
serializability.

## DAG Structure

For each key, the shard maintains a map from `TxFingerprint` to `KeyAccess`,
recording the read/write status of each transaction's access to that key.

### Four Optimizations (from the Anoma spec)

1. **Per-key ordering**: Transactions are totally ordered by happens-before
   on each key. Unrelated keys can execute in parallel.
2. **Order w.r.t. writes only**: Only write-before-read dependencies matter.
   Reads can proceed once the preceding write completes.
3. **MVCC (Multi-Version Concurrent Control)**: Writes do not wait for
   earlier reads. The shard maintains a complete history of values.
4. **Partial order execution**: Transactions can execute before total
   consensus order if the partial order is sufficient.
-/

namespace MailboxActors.Examples.Anoma.Ordering

variable (A : AnomaTypes)

/-- Read status for a key access in the shard DAG.
- `pending`: Read registered but value not yet sent to executor.
- `fulfilled`: Value has been sent to the requesting executor. -/
inductive ReadStatus where
  | pending : ReadStatus
  | fulfilled : ReadStatus
  deriving DecidableEq, BEq

/-- Write status for a key access in the shard DAG.
- `pending`: Write lock acquired but no value written yet.
- `committed`: Value has been written by the executor. -/
inductive WriteStatus where
  | pending : WriteStatus
  | committed : A.KVSDatum → WriteStatus
  deriving DecidableEq, BEq

/-- Per-key access record at a given transaction fingerprint.
    Tracks the read and write status for one transaction's
    interaction with one key. -/
structure KeyAccess where
  readStatus : Option ReadStatus
  writeStatus : Option (WriteStatus A)
  deriving DecidableEq, BEq

/-- Messages for the shard engine.

- `acquireLock`: The mempool worker requests a lock for a transaction
  on a key. Carries the worker's address so the shard can reply with
  `TxOrderingMsg.lockAcquired`. The shard adds an entry to its DAG
  and sends the confirmation back.
- `readRequest`: An executor requests the current value of a key at
  a given transaction fingerprint. Carries the executor's address so
  the shard can reply with `ExecutorMsg.readReply` when the value is
  available.
- `write`: An executor writes a value for a key at a given fingerprint.
- `updateSeenAll`: The mempool worker updates the barrier watermarks,
  allowing the shard to garbage-collect old DAG entries. -/
inductive ShardMsg where
  | acquireLock : A.TxFingerprint → A.KVSKey → MailboxActors.Address → ShardMsg
  | readRequest : A.TxFingerprint → A.KVSKey → MailboxActors.Address → ShardMsg
  | write : A.TxFingerprint → A.KVSKey → A.KVSDatum → ShardMsg
  | updateSeenAll : A.TxFingerprint → ShardMsg
  deriving DecidableEq, BEq

/-- Configuration for the shard engine. -/
abbrev ShardCfg := Unit

/-- Local state for the shard engine.

- `keyAccesses`: The DAG structure mapping `(key, fingerprint)` pairs
  to their access records.
- `heardAllReads`: Lower bound on read operations. No further read
  locks will arrive with a fingerprint before this value.
- `heardAllWrites`: Lower bound on write operations. No further write
  locks will arrive with a fingerprint before this value. -/
structure ShardState where
  keyAccesses : List (A.KVSKey × A.TxFingerprint × KeyAccess A)
  heardAllReads : A.TxFingerprint
  heardAllWrites : A.TxFingerprint

end MailboxActors.Examples.Anoma.Ordering
