import MailboxActors.Examples.Anoma.EngIdx

/-!
# Transport Engine — Types

The transport engine manages protocol-level connections. It delegates
to protocol-specific engines for actual data transfer.
-/

namespace MailboxActors.Examples.Anoma.Network

variable (A : AnomaTypes)

/-- Messages for the transport engine.
- `send`: Send data to a transport address.
- `recv`: Receive data from a transport address.
- `connectionEstablished`: Notification that a connection is ready. -/
inductive TransportMsg where
  | send : A.TransportAddr → A.ByteString → TransportMsg
  | recv : A.TransportAddr → A.ByteString → TransportMsg
  | connectionEstablished : A.TransportAddr → TransportMsg
  deriving DecidableEq, BEq

/-- Configuration for the transport engine (no configuration needed). -/
abbrev TransportCfg := Unit

/-- Local state for the transport engine (stateless). -/
abbrev TransportState := Unit

end MailboxActors.Examples.Anoma.Network
