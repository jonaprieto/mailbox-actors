import MailboxActors.Examples.Anoma.Ordering.TxOrdering.Behaviour
import MailboxActors.Examples.Anoma.Ordering.Shard.Behaviour
import MailboxActors.Examples.Anoma.Ordering.Executor.Behaviour

/-!
# Ordering Subsystem — Behaviours

Re-exports all behaviour definitions for the Ordering subsystem engines.

## Implemented actions

- **TxOrdering**: `submitTx` increments gensym counter and spawns executor;
  `lockAcquired` / `executorFinished` update pending-lock tracking.
- **Shard**: `acquireLock` appends DAG entry; `write` commits datum;
  `updateSeenAll` advances watermarks; `readRequest` is abstract (noop).
- **Executor**: `readReply` tracks completed reads.
-/
