import MailboxActors.Examples.Anoma.Infra.Ticker.Behaviour
import MailboxActors.Examples.Anoma.Infra.WallClock.Behaviour
import MailboxActors.Examples.Anoma.Infra.Logging.Behaviour
import MailboxActors.Examples.Anoma.Infra.KVStore.Behaviour
import MailboxActors.Examples.Anoma.Infra.TSStore.Behaviour
import MailboxActors.Examples.Anoma.Infra.Storage.Behaviour

/-!
# Infrastructure Subsystem — Behaviours

Re-exports all behaviour definitions for the Infrastructure subsystem engines.

## Implemented actions

- **Ticker**: `tick` increments the epoch counter.
- **WallClock**: `timeReply` stores the received epoch.
- **Logging**: `logAppend` appends the message to the log list.
- **KVStore**: `setReq` / `deleteReq` increment/decrement entry count.
- **TSStore**: `recordReq` / `deleteReq` increment/decrement series count.
- **Storage**: `chunkPut` increments chunk count; `chunkGet` is abstract (noop).
-/
