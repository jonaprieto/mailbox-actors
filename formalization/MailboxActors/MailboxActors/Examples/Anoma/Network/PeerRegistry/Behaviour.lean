import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Peer Registry Engine — Behaviour

The peer registry maintains a directory of known nodes and topics.

## advertNode
Register a node — increments the `nodeCount`.

## lookupNode
Query for a node's address — no state change.

## advertTopic
Register a topic with a node — increments the `topicCount`.

## lookupTopic
Query for nodes hosting a topic — no state change.

Reply messages (`lookupReply`, `topicReply`) are not guarded here;
they are produced by the actions above and consumed by other engines.
-/

namespace MailboxActors.Examples.Anoma.Network

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Guards
-- ============================================================================

/-- Guard for `advertNode` messages. -/
@[simp]
def peerRegistryAdvertNodeGuard
    (inp : @GuardInput (S A) AnomaIdx.peerRegistry) :
    Option (A.NodeID × A.TransportAddr) :=
  match @GuardInput.msg (S A) _ inp with
  | .advertNode nid addr => some (nid, addr)
  | _ => none

/-- Guard for `lookupNode` messages. -/
@[simp]
def peerRegistryLookupNodeGuard
    (inp : @GuardInput (S A) AnomaIdx.peerRegistry) :
    Option A.NodeID :=
  match @GuardInput.msg (S A) _ inp with
  | .lookupNode nid => some nid
  | _ => none

/-- Guard for `advertTopic` messages. -/
@[simp]
def peerRegistryAdvertTopicGuard
    (inp : @GuardInput (S A) AnomaIdx.peerRegistry) :
    Option (A.TopicID × A.NodeID) :=
  match @GuardInput.msg (S A) _ inp with
  | .advertTopic tid nid => some (tid, nid)
  | _ => none

/-- Guard for `lookupTopic` messages. -/
@[simp]
def peerRegistryLookupTopicGuard
    (inp : @GuardInput (S A) AnomaIdx.peerRegistry) :
    Option A.TopicID :=
  match @GuardInput.msg (S A) _ inp with
  | .lookupTopic tid => some tid
  | _ => none

-- ============================================================================
-- § Actions
-- ============================================================================

/-- Action for `advertNode`: increment the node count. -/
def peerRegistryAdvertNodeAction
    (w : A.NodeID × A.TransportAddr)
    (inp : @GuardInput (S A) AnomaIdx.peerRegistry)
    (_ : peerRegistryAdvertNodeGuard A inp = some w) :
    @Effect (S A) AnomaIdx.peerRegistry :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with nodeCount := st.nodeCount + 1 } }

/-- Action for `lookupNode`: no-op. -/
def peerRegistryLookupNodeAction
    (w : A.NodeID)
    (inp : @GuardInput (S A) AnomaIdx.peerRegistry)
    (_ : peerRegistryLookupNodeGuard A inp = some w) :
    @Effect (S A) AnomaIdx.peerRegistry :=
  letI := S A; Effect.noop

/-- Action for `advertTopic`: increment the topic count. -/
def peerRegistryAdvertTopicAction
    (w : A.TopicID × A.NodeID)
    (inp : @GuardInput (S A) AnomaIdx.peerRegistry)
    (_ : peerRegistryAdvertTopicGuard A inp = some w) :
    @Effect (S A) AnomaIdx.peerRegistry :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with topicCount := st.topicCount + 1 } }

/-- Action for `lookupTopic`: no-op. -/
def peerRegistryLookupTopicAction
    (w : A.TopicID)
    (inp : @GuardInput (S A) AnomaIdx.peerRegistry)
    (_ : peerRegistryLookupTopicGuard A inp = some w) :
    @Effect (S A) AnomaIdx.peerRegistry :=
  letI := S A; Effect.noop

-- ============================================================================
-- § Behaviour assembly
-- ============================================================================

def peerRegistryActions : @Behaviour (S A) AnomaIdx.peerRegistry :=
  letI := S A
  [ { Witness := A.NodeID × A.TransportAddr
      guard := peerRegistryAdvertNodeGuard A
      action := peerRegistryAdvertNodeAction A }
  , { Witness := A.NodeID
      guard := peerRegistryLookupNodeGuard A
      action := peerRegistryLookupNodeAction A }
  , { Witness := A.TopicID × A.NodeID
      guard := peerRegistryAdvertTopicGuard A
      action := peerRegistryAdvertTopicAction A }
  , { Witness := A.TopicID
      guard := peerRegistryLookupTopicGuard A
      action := peerRegistryLookupTopicAction A } ]

private theorem peerRegistryNonOverlapping :
    @NonOverlappingGuards (S A) _ (peerRegistryActions A) := by
  letI := S A; intro inp
  simp only [peerRegistryActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def peerRegistryBehaviour : @WellFormedBehaviour (S A) AnomaIdx.peerRegistry :=
  letI := S A
  { actions := peerRegistryActions A
    nonOverlapping := peerRegistryNonOverlapping A }

end MailboxActors.Examples.Anoma.Network
