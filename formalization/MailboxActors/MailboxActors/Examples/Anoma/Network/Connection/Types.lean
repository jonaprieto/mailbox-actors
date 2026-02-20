import MailboxActors.Examples.Anoma.EngIdx

/-!
# Connection Engine — Types

Each connection engine manages a single transport connection to a
remote node. It handles encryption, sequence numbering, and
keep-alive messages.
-/

namespace MailboxActors.Examples.Anoma.Network

variable (A : AnomaTypes)

/-- Connection status. -/
inductive ConnectionStatus where
  | connecting : ConnectionStatus
  | established : ConnectionStatus
  | closed : ConnectionStatus
  deriving DecidableEq, BEq

/-- Messages for the connection engine.
- `send`: Send data over this connection.
- `recv`: Data received on this connection. -/
inductive ConnectionMsg where
  | send : A.ByteString → ConnectionMsg
  | recv : A.ByteString → ConnectionMsg
  deriving DecidableEq, BEq

/-- Configuration for the connection engine.
- `remoteAddr`: The transport address of the remote endpoint. -/
structure ConnectionCfg where
  remoteAddr : A.TransportAddr

/-- Local state for the connection engine.
- `sequenceNumber`: Outgoing message sequence counter.
- `status`: Current connection status. -/
structure ConnectionState where
  sequenceNumber : Nat
  status : ConnectionStatus

end MailboxActors.Examples.Anoma.Network
