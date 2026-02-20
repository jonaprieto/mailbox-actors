import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# PubSub Engine — Behaviour

The pub/sub engine manages topic-based message dissemination.

## publish
Publishing a message increments the `messageCount`.

## subscribe
Subscribing to a topic increments the `subscriberCount`.

## unsubscribe
Unsubscribing decrements the `subscriberCount`.

## forward
Forwarding a published message to remote subscribers is currently a
no-op (the routing logic handles delivery).
-/

namespace MailboxActors.Examples.Anoma.Network

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Guards
-- ============================================================================

/-- Guard for `publish` messages. -/
@[simp]
def pubsubPublishGuard
    (inp : @GuardInput (S A) AnomaIdx.pubsub) :
    Option (A.TopicID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .publish tid bs => some (tid, bs)
  | _ => none

/-- Guard for `subscribe` messages. -/
@[simp]
def pubsubSubscribeGuard
    (inp : @GuardInput (S A) AnomaIdx.pubsub) :
    Option A.TopicID :=
  match @GuardInput.msg (S A) _ inp with
  | .subscribe tid => some tid
  | _ => none

/-- Guard for `unsubscribe` messages. -/
@[simp]
def pubsubUnsubscribeGuard
    (inp : @GuardInput (S A) AnomaIdx.pubsub) :
    Option A.TopicID :=
  match @GuardInput.msg (S A) _ inp with
  | .unsubscribe tid => some tid
  | _ => none

/-- Guard for `forward` messages. -/
@[simp]
def pubsubForwardGuard
    (inp : @GuardInput (S A) AnomaIdx.pubsub) :
    Option (A.TopicID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .forward tid bs => some (tid, bs)
  | _ => none

-- ============================================================================
-- § Actions
-- ============================================================================

/-- Action for `publish`: increment the message count. -/
def pubsubPublishAction
    (w : A.TopicID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.pubsub)
    (_ : pubsubPublishGuard A inp = some w) :
    @Effect (S A) AnomaIdx.pubsub :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with messageCount := st.messageCount + 1 } }

/-- Action for `subscribe`: increment the subscriber count. -/
def pubsubSubscribeAction
    (w : A.TopicID)
    (inp : @GuardInput (S A) AnomaIdx.pubsub)
    (_ : pubsubSubscribeGuard A inp = some w) :
    @Effect (S A) AnomaIdx.pubsub :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with subscriberCount := st.subscriberCount + 1 } }

/-- Action for `unsubscribe`: decrement the subscriber count. -/
def pubsubUnsubscribeAction
    (w : A.TopicID)
    (inp : @GuardInput (S A) AnomaIdx.pubsub)
    (_ : pubsubUnsubscribeGuard A inp = some w) :
    @Effect (S A) AnomaIdx.pubsub :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with subscriberCount := st.subscriberCount - 1 } }

/-- Action for `forward`: no-op — the routing logic handles delivery. -/
def pubsubForwardAction
    (w : A.TopicID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.pubsub)
    (_ : pubsubForwardGuard A inp = some w) :
    @Effect (S A) AnomaIdx.pubsub :=
  letI := S A; Effect.noop

-- ============================================================================
-- § Behaviour assembly
-- ============================================================================

def pubsubActions : @Behaviour (S A) AnomaIdx.pubsub :=
  letI := S A
  [ { Witness := A.TopicID × A.ByteString
      guard := pubsubPublishGuard A
      action := pubsubPublishAction A }
  , { Witness := A.TopicID
      guard := pubsubSubscribeGuard A
      action := pubsubSubscribeAction A }
  , { Witness := A.TopicID
      guard := pubsubUnsubscribeGuard A
      action := pubsubUnsubscribeAction A }
  , { Witness := A.TopicID × A.ByteString
      guard := pubsubForwardGuard A
      action := pubsubForwardAction A } ]

private theorem pubsubNonOverlapping :
    @NonOverlappingGuards (S A) _ (pubsubActions A) := by
  letI := S A; intro inp
  simp only [pubsubActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def pubsubBehaviour : @WellFormedBehaviour (S A) AnomaIdx.pubsub :=
  letI := S A
  { actions := pubsubActions A
    nonOverlapping := pubsubNonOverlapping A }

end MailboxActors.Examples.Anoma.Network
