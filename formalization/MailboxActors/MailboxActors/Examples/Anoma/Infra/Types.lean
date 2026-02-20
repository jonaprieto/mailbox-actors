import MailboxActors.Examples.Anoma.Infra.Ticker.Types
import MailboxActors.Examples.Anoma.Infra.WallClock.Types
import MailboxActors.Examples.Anoma.Infra.Logging.Types
import MailboxActors.Examples.Anoma.Infra.KVStore.Types
import MailboxActors.Examples.Anoma.Infra.TSStore.Types
import MailboxActors.Examples.Anoma.Infra.Storage.Types

/-!
# Infrastructure Subsystem — Types

Re-exports all type definitions for the six Infrastructure subsystem engines.

## Architecture

The infrastructure subsystem provides shared services used by all other
subsystems:

- **Ticker** — Generates periodic epoch ticks. Other engines subscribe to
  receive `tick` messages for time-based logic.
- **WallClock** — Provides wall-clock time queries (`getTime` / `timeReply`).
- **Logging** — Append-only log accumulator. Engines send `logAppend` messages
  which are stored in order.
- **KVStore** — Persistent key-value store with `getReq`/`setReq`/`deleteReq`.
- **TSStore** — Time-series data store with `recordReq`/`queryReq`/`deleteReq`.
- **Storage** — Blob storage addressed by chunk IDs (`chunkGet`/`chunkPut`).
-/
