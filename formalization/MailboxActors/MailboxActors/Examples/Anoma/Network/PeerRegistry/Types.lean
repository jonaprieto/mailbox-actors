import MailboxActors.Examples.Anoma.EngIdx

/-!
# Peer Registry Engine — Types

The peer registry maintains a directory of known nodes and topics.
It enables node discovery and topic-based pub/sub routing.
-/

namespace MailboxActors.Examples.Anoma.Network

variable (A : AnomaTypes)

/-- Messages for the peer-registry engine.
- `advertNode`: Register a node with its transport address.
- `lookupNode`: Query for a node's address.
- `lookupReply`: Response to a node lookup.
- `advertTopic`: Register a topic with a node.
- `lookupTopic`: Query for nodes hosting a topic.
- `topicReply`: Response to a topic lookup. -/
inductive PeerRegistryMsg where
  | advertNode : A.NodeID → A.TransportAddr → PeerRegistryMsg
  | lookupNode : A.NodeID → PeerRegistryMsg
  | lookupReply : A.NodeID → Bool → PeerRegistryMsg
  | advertTopic : A.TopicID → A.NodeID → PeerRegistryMsg
  | lookupTopic : A.TopicID → PeerRegistryMsg
  | topicReply : A.TopicID → Bool → PeerRegistryMsg
  deriving DecidableEq, BEq

abbrev PeerRegistryCfg := Unit

/-- Local state for the peer-registry engine.
- `nodeCount`: Number of registered nodes.
- `topicCount`: Number of registered topics. -/
structure PeerRegistryState where
  nodeCount : Nat
  topicCount : Nat

end MailboxActors.Examples.Anoma.Network
