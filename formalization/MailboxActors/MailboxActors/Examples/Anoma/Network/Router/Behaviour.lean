import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Router Engine — Behaviour

The router is the central message dispatcher for the network subsystem.

## sendLocal
Forward a message to a local engine on the same node.
No state change needed; the router merely dispatches.

## sendRemote
Forward a message to a remote node.  The sequence number is
incremented so the remote end can detect reordering / loss.

## recv
An incoming message from a remote node.
Currently a no-op (message is forwarded by the routing logic).

## connectReq / connectReply
Connection-handshake messages.  Currently no-ops.
-/

namespace MailboxActors.Examples.Anoma.Network

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Guards
-- ============================================================================

/-- Guard for `sendLocal` messages. -/
@[simp]
def routerSendLocalGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option (A.NodeID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .sendLocal nid bs => some (nid, bs)
  | _ => none

/-- Guard for `sendRemote` messages. -/
@[simp]
def routerSendRemoteGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option (A.NodeID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .sendRemote nid bs => some (nid, bs)
  | _ => none

/-- Guard for `recv` messages. -/
@[simp]
def routerRecvGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option (A.NodeID × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .recv nid bs => some (nid, bs)
  | _ => none

/-- Guard for `connectReq` messages. -/
@[simp]
def routerConnectReqGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option A.NodeID :=
  match @GuardInput.msg (S A) _ inp with
  | .connectReq nid => some nid
  | _ => none

/-- Guard for `connectReply` messages. -/
@[simp]
def routerConnectReplyGuard
    (inp : @GuardInput (S A) AnomaIdx.router) :
    Option (A.NodeID × Bool) :=
  match @GuardInput.msg (S A) _ inp with
  | .connectReply nid ok => some (nid, ok)
  | _ => none

-- ============================================================================
-- § Actions
-- ============================================================================

/-- Action for `sendLocal`: no-op — the router merely dispatches the
    message to the target local engine. -/
def routerSendLocalAction
    (w : A.NodeID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerSendLocalGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

/-- Action for `sendRemote`: increment the outgoing sequence number
    so the remote end can detect reordering or loss. -/
def routerSendRemoteAction
    (w : A.NodeID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerSendRemoteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with seqNum := st.seqNum + 1 } }

/-- Action for `recv`: no-op — incoming messages are forwarded by the
    routing logic without modifying state. -/
def routerRecvAction
    (w : A.NodeID × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerRecvGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

/-- Action for `connectReq`: no-op — connection setup is delegated to
    the transport/protocol layers. -/
def routerConnectReqAction
    (w : A.NodeID)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerConnectReqGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

/-- Action for `connectReply`: no-op — the reply is consumed by the
    router but no state change is needed. -/
def routerConnectReplyAction
    (w : A.NodeID × Bool)
    (inp : @GuardInput (S A) AnomaIdx.router)
    (_ : routerConnectReplyGuard A inp = some w) :
    @Effect (S A) AnomaIdx.router :=
  letI := S A; Effect.noop

-- ============================================================================
-- § Behaviour assembly
-- ============================================================================

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
      guard := routerConnectReqGuard A
      action := routerConnectReqAction A }
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

end MailboxActors.Examples.Anoma.Network
