import MailboxActors.Examples.Anoma.EngIdx

/-!
# Network Subsystem — Message, Config, and State Types

Engines: `router`, `transport`, `protocol`, `connection`,
`peerRegistry`, `pubsub`.
-/

namespace MailboxActors.Examples.Anoma.Network

variable (A : AnomaTypes)

-- ============================================================================
-- § Router
-- ============================================================================

/-- Messages for the router engine. -/
inductive RouterMsg where
  | sendLocal   : A.NodeID → A.ByteString → RouterMsg
  | sendRemote  : A.NodeID → A.ByteString → RouterMsg
  | recv        : A.NodeID → A.ByteString → RouterMsg
  | connectReq  : A.NodeID → RouterMsg
  | connectReply : A.NodeID → Bool → RouterMsg
  deriving DecidableEq, BEq

/-- Configuration for the router engine. -/
structure RouterCfg where
  localNodeId : A.NodeID

/-- Local state for the router engine. -/
structure RouterState where
  seqNum : Nat

-- ============================================================================
-- § Transport
-- ============================================================================

/-- Messages for the transport engine. -/
inductive TransportMsg where
  | send : A.TransportAddr → A.ByteString → TransportMsg
  deriving DecidableEq, BEq

/-- Configuration for the transport engine. -/
abbrev TransportCfg := Unit

/-- Local state for the transport engine. -/
abbrev TransportState := Unit

-- ============================================================================
-- § Protocol (transport protocol)
-- ============================================================================

/-- Messages for the protocol engine. -/
inductive ProtocolMsg where
  | send : A.TransportAddr → A.ByteString → ProtocolMsg
  deriving DecidableEq, BEq

/-- Configuration for the protocol engine. -/
abbrev ProtocolCfg := Unit

/-- Local state for the protocol engine. -/
abbrev ProtocolState := Unit

-- ============================================================================
-- § Connection (transport connection)
-- ============================================================================

/-- Messages for the connection engine. -/
inductive ConnectionMsg where
  | send : A.ByteString → ConnectionMsg
  deriving DecidableEq, BEq

/-- Configuration for the connection engine. -/
structure ConnectionCfg where
  remoteAddr : A.TransportAddr

/-- Local state for the connection engine. -/
abbrev ConnectionState := Unit

-- ============================================================================
-- § PeerRegistry (network registry)
-- ============================================================================

/-- Messages for the peer-registry engine. -/
inductive PeerRegistryMsg where
  | advertNode   : A.NodeID → A.TransportAddr → PeerRegistryMsg
  | lookupNode   : A.NodeID → PeerRegistryMsg
  | lookupReply  : A.NodeID → Bool → PeerRegistryMsg
  | advertTopic  : A.TopicID → A.NodeID → PeerRegistryMsg
  | lookupTopic  : A.TopicID → PeerRegistryMsg
  | topicReply   : A.TopicID → Bool → PeerRegistryMsg
  deriving DecidableEq, BEq

/-- Configuration for the peer-registry engine. -/
abbrev PeerRegistryCfg := Unit

/-- Local state for the peer-registry engine. -/
structure PeerRegistryState where
  nodeCount : Nat
  topicCount : Nat

-- ============================================================================
-- § PubSub (pub/sub topic)
-- ============================================================================

/-- Messages for the pub/sub engine. -/
inductive PubSubMsg where
  | publish     : A.TopicID → A.ByteString → PubSubMsg
  | subscribe   : A.TopicID → PubSubMsg
  | unsubscribe : A.TopicID → PubSubMsg
  | forward     : A.TopicID → A.ByteString → PubSubMsg
  deriving DecidableEq, BEq

/-- Configuration for the pub/sub engine. -/
structure PubSubCfg where
  topicId : A.TopicID

/-- Local state for the pub/sub engine. -/
structure PubSubState where
  subscriberCount : Nat
  messageCount    : Nat

end MailboxActors.Examples.Anoma.Network
