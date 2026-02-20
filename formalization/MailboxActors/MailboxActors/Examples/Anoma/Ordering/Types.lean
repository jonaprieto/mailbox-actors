import MailboxActors.Examples.Anoma.Ordering.TxOrdering.Types
import MailboxActors.Examples.Anoma.Ordering.Shard.Types
import MailboxActors.Examples.Anoma.Ordering.Executor.Types

/-!
# Ordering Subsystem — Types

Re-exports all type definitions for the three Ordering subsystem engines.

## Architecture

The ordering subsystem implements transaction ordering using
gensym-based fingerprinting and DAG-based multi-version concurrency
control (MVCC).

### Transaction lifecycle

1. A `submitTx` message arrives at the **TxOrdering** (mempool worker) engine.
2. The worker assigns a unique fingerprint via the gensym counter,
   adds the transaction to `pendingLocks`, and spawns an **Executor** engine.
3. The worker sends `acquireLock` messages to the relevant **Shard** engines.
4. Each shard adds a `KeyAccess` entry to its DAG and replies with `lockAcquired`.
5. The executor receives `readReply` messages from shards as data becomes available.
6. When the executor completes, it sends `executorFinished` to the mempool worker.

### Key types

- `ReadStatus` / `WriteStatus` — Track per-key access states in the shard DAG.
- `KeyAccess` — Combined read/write status for a single key at a given transaction.
- `TxOrderingState.nextFingerprint` — Gensym counter for ordering.
- `ExecutorCfg` — Access rights (lazy/eager reads, will/may writes).
-/
