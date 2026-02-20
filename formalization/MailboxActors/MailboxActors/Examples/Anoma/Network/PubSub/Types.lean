import MailboxActors.Examples.Anoma.EngIdx

/-!
# PubSub Engine — Types

The pub/sub engine manages topic-based message dissemination.
Each instance corresponds to a single topic and maintains subscriber
lists for both local and remote subscribers.
-/

namespace MailboxActors.Examples.Anoma.Network

variable (A : AnomaTypes)

/-- Messages for the pub/sub engine.
- `publish`: Publish a message to a topic.
- `subscribe`: Subscribe to a topic.
- `unsubscribe`: Unsubscribe from a topic.
- `forward`: Forward a published message to remote subscribers. -/
inductive PubSubMsg where
  | publish : A.TopicID → A.ByteString → PubSubMsg
  | subscribe : A.TopicID → PubSubMsg
  | unsubscribe : A.TopicID → PubSubMsg
  | forward : A.TopicID → A.ByteString → PubSubMsg
  deriving DecidableEq, BEq

/-- Configuration for the pub/sub engine.
- `topicId`: The topic this engine instance manages. -/
structure PubSubCfg where
  topicId : A.TopicID

/-- Local state for the pub/sub engine.
- `subscriberCount`: Number of active subscribers.
- `messageCount`: Number of messages published. -/
structure PubSubState where
  subscriberCount : Nat
  messageCount : Nat

end MailboxActors.Examples.Anoma.Network
