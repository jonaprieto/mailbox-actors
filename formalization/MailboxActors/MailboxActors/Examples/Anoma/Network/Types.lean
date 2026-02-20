import MailboxActors.Examples.Anoma.Network.Router.Types
import MailboxActors.Examples.Anoma.Network.Transport.Types
import MailboxActors.Examples.Anoma.Network.Protocol.Types
import MailboxActors.Examples.Anoma.Network.Connection.Types
import MailboxActors.Examples.Anoma.Network.PeerRegistry.Types
import MailboxActors.Examples.Anoma.Network.PubSub.Types

/-!
# Network Subsystem — Types

Re-exports all type definitions for the six Network subsystem engines.

## Architecture

The network subsystem handles inter-node communication through a
layered architecture:

### Message flow (outgoing)

1. A local engine sends to the **Router** (`sendRemote`).
2. The router forwards to the **Transport** layer.
3. Transport delegates to the appropriate **Protocol** engine.
4. The protocol uses a **Connection** engine for sequenced delivery.

### Message flow (incoming)

1. A **Connection** engine receives bytes from the network.
2. The connection delivers to its **Protocol** engine.
3. The protocol forwards to **Transport**, which delivers to the **Router**.
4. The router dispatches to the target local engine (`sendLocal`).

### Supporting engines

- **PeerRegistry** — directory service for node and topic discovery.
- **PubSub** — topic-based publish/subscribe message broadcasting.
-/
