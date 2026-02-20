import MailboxActors.Examples.Anoma.EngIdx

/-!
# Protocol Engine — Types

The protocol engine handles protocol-specific connection management
(e.g., QUIC, TLS, TCP). It spawns connection engines for individual
transport connections.
-/

namespace MailboxActors.Examples.Anoma.Network

variable (A : AnomaTypes)

/-- Messages for the protocol engine.
- `openConnection`: Request to open a new connection.
- `incomingConnection`: Notification of an incoming connection.
- `send`: Send data over a managed connection. -/
inductive ProtocolMsg where
  | openConnection : A.TransportAddr → ProtocolMsg
  | incomingConnection : A.TransportAddr → ProtocolMsg
  | send : A.TransportAddr → A.ByteString → ProtocolMsg
  deriving DecidableEq, BEq

/-- Configuration for the protocol engine (no configuration needed). -/
abbrev ProtocolCfg := Unit

/-- Local state for the protocol engine (stateless). -/
abbrev ProtocolState := Unit

end MailboxActors.Examples.Anoma.Network
