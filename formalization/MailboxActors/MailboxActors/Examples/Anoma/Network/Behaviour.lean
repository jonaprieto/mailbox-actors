import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Network Subsystem — Behaviours

Guards and actions for `router`, `transport`, `protocol`,
`connection`, `peerRegistry`, `pubsub`.

Transport, protocol, and connection engines have stub behaviours
(empty action lists) as the old nspec left them incomplete.
-/

namespace MailboxActors.Examples.Anoma.Network

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Router Behaviour
-- ============================================================================

@[simp]
def routerSendLocalGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option (A.NodeID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .sendLocal nid bs => some (nid, bs)
  | _ => none

def routerSendLocalAction
    (w : A.NodeID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerSendLocalGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

@[simp]
def routerSendRemoteGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option (A.NodeID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .sendRemote nid bs => some (nid, bs)
  | _ => none

def routerSendRemoteAction
    (w : A.NodeID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerSendRemoteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

@[simp]
def routerRecvGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option (A.NodeID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .recv nid bs => some (nid, bs)
  | _ => none

def routerRecvAction
    (w : A.NodeID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerRecvGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

@[simp]
def routerConnectGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option A.NodeID :=
  match @GuardInput.msg (S A) _ inp with
  | .connectReq nid => some nid
  | _ => none

def routerConnectAction
    (w : A.NodeID)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerConnectGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

@[simp]
def routerConnectReplyGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option (A.NodeID × Bool) :=
  match @GuardInput.msg (S A) _ inp with
  | .connectReply nid ok => some (nid, ok)
  | _ => none

def routerConnectReplyAction
    (w : A.NodeID × Bool)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerConnectReplyGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

def routerActions : @Behaviour (S A) AnomaIdx.router :=
  letI := S A
  [ { Witness := A.NodeID × A.ByteString
      guard := routerSendLocalGuard A
      action := routerSendLocalAction A }
  , { Witness := A.NodeID × A.ByteString
      guard := routerSendRemoteGuard A
      action := routerSendRemoteAction A }
  , { Witness := A.NodeID × A.ByteString
      guard := routerRecvGuard A
      action := routerRecvAction A }
  , { Witness := A.NodeID
      guard := routerConnectGuard A
      action := routerConnectAction A }
  , { Witness := A.NodeID × Bool
      guard := routerConnectReplyGuard A
      action := routerConnectReplyAction A } ]

private theorem routerNonOverlapping :
    @NonOverlappingGuards (S A) _ (routerActions A) := by
  letI := S A; intro inp
  simp only [routerActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def routerBehaviour : @WellFormedBehaviour (S A) AnomaIdx.router :=
  letI := S A
  { actions := routerActions A
    nonOverlapping := routerNonOverlapping A }

-- ============================================================================
-- § Transport Behaviour (stub)
-- ============================================================================

def transportBehaviour : @WellFormedBehaviour (S A) AnomaIdx.transport :=
  letI := S A
  { actions := []
    nonOverlapping := by intro inp; simp [List.filter] }

-- ============================================================================
-- § Protocol Behaviour (stub)
-- ============================================================================

def protocolBehaviour : @WellFormedBehaviour (S A) AnomaIdx.protocol :=
  letI := S A
  { actions := []
    nonOverlapping := by intro inp; simp [List.filter] }

-- ============================================================================
-- § Connection Behaviour (stub)
-- ============================================================================

def connectionBehaviour : @WellFormedBehaviour (S A) AnomaIdx.connection :=
  letI := S A
  { actions := []
    nonOverlapping := by intro inp; simp [List.filter] }

-- ============================================================================
-- § PeerRegistry Behaviour (stub)
-- ============================================================================

def peerRegistryBehaviour : @WellFormedBehaviour (S A) AnomaIdx.peerRegistry :=
  letI := S A
  { actions := []
    nonOverlapping := by intro inp; simp [List.filter] }

-- ============================================================================
-- § PubSub Behaviour
-- ============================================================================

@[simp]
def pubsubPublishGuard
    (inp : @GuardInput (S A) AnomaIdx.pubsub) :
    Option (A.TopicID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .publish tid bs => some (tid, bs)
  | _ => none

def pubsubPublishAction
    (w : A.TopicID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.pubsub)
    (_ : pubsubPublishGuard A inp = some w) :
    @Effect (S A) AnomaIdx.pubsub :=
  letI := S A; Effect.noop

@[simp]
def pubsubSubscribeGuard
    (inp : @GuardInput (S A) AnomaIdx.pubsub) :
    Option A.TopicID :=
  match @GuardInput.msg (S A) _ inp with
  | .subscribe tid => some tid
  | _ => none

def pubsubSubscribeAction
    (w : A.TopicID)
    (inp : @GuardInput (S A) AnomaIdx.pubsub)
    (_ : pubsubSubscribeGuard A inp = some w) :
    @Effect (S A) AnomaIdx.pubsub :=
  letI := S A; Effect.noop

@[simp]
def pubsubUnsubscribeGuard
    (inp : @GuardInput (S A) AnomaIdx.pubsub) :
    Option A.TopicID :=
  match @GuardInput.msg (S A) _ inp with
  | .unsubscribe tid => some tid
  | _ => none

def pubsubUnsubscribeAction
    (w : A.TopicID)
    (inp : @GuardInput (S A) AnomaIdx.pubsub)
    (_ : pubsubUnsubscribeGuard A inp = some w) :
    @Effect (S A) AnomaIdx.pubsub :=
  letI := S A; Effect.noop

@[simp]
def pubsubForwardGuard
    (inp : @GuardInput (S A) AnomaIdx.pubsub) :
    Option (A.TopicID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .forward tid bs => some (tid, bs)
  | _ => none

def pubsubForwardAction
    (w : A.TopicID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.pubsub)
    (_ : pubsubForwardGuard A inp = some w) :
    @Effect (S A) AnomaIdx.pubsub :=
  letI := S A; Effect.noop

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
