import MailboxActors.Examples.Anoma.Network.Router.Behaviour
import MailboxActors.Examples.Anoma.Network.Transport.Behaviour
import MailboxActors.Examples.Anoma.Network.Protocol.Behaviour
import MailboxActors.Examples.Anoma.Network.Connection.Behaviour
import MailboxActors.Examples.Anoma.Network.PeerRegistry.Behaviour
import MailboxActors.Examples.Anoma.Network.PubSub.Behaviour

/-!
# Network Subsystem — Behaviours

Re-exports all behaviour definitions for the Network subsystem engines.

## Implemented actions

- **Router**: `sendRemote` increments outgoing sequence number;
  other routing actions are abstract (noop).
- **Connection**: `send` increments per-connection sequence number.
- **PeerRegistry**: `advertNode` / `advertTopic` increment directory counters.
- **PubSub**: `subscribe` / `unsubscribe` track subscriber count;
  `publish` increments message count.
- **Transport / Protocol**: Guards extract messages; actions are abstract
  pending full inter-engine routing support.
-/
