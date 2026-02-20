import MailboxActors.Examples.Anoma.EngIdx

/-!
# Router Engine — Types

The router is the central message dispatcher for the network subsystem.
It routes messages between local engines and remote nodes, manages
connection establishment, and maintains a sequence number for outgoing
messages.
-/

namespace MailboxActors.Examples.Anoma.Network

variable (A : AnomaTypes)

/-- Messages for the router engine.
- `sendLocal`: Route a message to a local engine on the same node.
- `sendRemote`: Forward a message to a remote node via the transport layer.
- `recv`: An incoming message from a remote node.
- `connectReq`: Initiate connection to a remote node.
- `connectReply`: Response to a connection request. -/
inductive RouterMsg where
  | sendLocal : A.NodeID → A.ByteString → RouterMsg
  | sendRemote : A.NodeID → A.ByteString → RouterMsg
  | recv : A.NodeID → A.ByteString → RouterMsg
  | connectReq : A.NodeID → RouterMsg
  | connectReply : A.NodeID → Bool → RouterMsg
  deriving DecidableEq, BEq

/-- Configuration for the router engine.
- `localNodeId`: The node ID of the local node. -/
structure RouterCfg where
  localNodeId : A.NodeID

/-- Local state for the router engine.
- `seqNum`: Monotonically increasing sequence number for outgoing messages. -/
structure RouterState where
  seqNum : Nat

end MailboxActors.Examples.Anoma.Network
