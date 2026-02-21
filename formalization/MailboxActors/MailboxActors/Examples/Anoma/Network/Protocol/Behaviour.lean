import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Protocol Engine — Behaviour

The protocol engine handles protocol-specific connection management
(e.g., QUIC, TLS, TCP). It spawns connection engines for individual
transport connections.

## openConnection

When `openConnection` arrives with a transport address, the protocol
engine spawns a new connection engine for that address with initial
`connecting` status.

## incomingConnection

When `incomingConnection` arrives, the protocol engine similarly
spawns a connection engine to handle the incoming connection.

## send

When `send` arrives with a transport address and payload, the protocol
engine should forward the data to the appropriate connection engine.
Currently noop because the connection engine's address is not available
without a connection table in the protocol state.
-/

namespace MailboxActors.Examples.Anoma.Network

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Guards
-- ============================================================================

/-- Guard for `openConnection` messages. -/
@[simp]
def protocolOpenConnectionGuard
    (inp : @GuardInput (S A) AnomaIdx.protocol) :
    Option A.TransportAddr :=
  match @GuardInput.msg (S A) _ inp with
  | .openConnection addr => some addr
  | _ => none

/-- Guard for `incomingConnection` messages. -/
@[simp]
def protocolIncomingConnectionGuard
    (inp : @GuardInput (S A) AnomaIdx.protocol) :
    Option A.TransportAddr :=
  match @GuardInput.msg (S A) _ inp with
  | .incomingConnection addr => some addr
  | _ => none

/-- Guard for `send` messages. -/
@[simp]
def protocolSendGuard
    (inp : @GuardInput (S A) AnomaIdx.protocol) :
    Option (A.TransportAddr × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .send addr bs => some (addr, bs)
  | _ => none

-- ============================================================================
-- § Actions
-- ============================================================================

/-- Action for `openConnection`: spawn a new connection engine for the
    given transport address with `connecting` status and sequence
    number 0. -/
def protocolOpenConnectionAction
    (w : A.TransportAddr)
    (inp : @GuardInput (S A) AnomaIdx.protocol)
    (_ : protocolOpenConnectionGuard A inp = some w) :
    @Effect (S A) AnomaIdx.protocol :=
  letI := S A
  Effect.spawn AnomaIdx.connection
    ({ remoteAddr := w } : ConnectionCfg A)
    ({ sequenceNumber := 0, status := .connecting } : ConnectionState)

/-- Action for `incomingConnection`: spawn a connection engine for the
    incoming transport address with `connecting` status. -/
def protocolIncomingConnectionAction
    (w : A.TransportAddr)
    (inp : @GuardInput (S A) AnomaIdx.protocol)
    (_ : protocolIncomingConnectionGuard A inp = some w) :
    @Effect (S A) AnomaIdx.protocol :=
  letI := S A
  Effect.spawn AnomaIdx.connection
    ({ remoteAddr := w } : ConnectionCfg A)
    ({ sequenceNumber := 0, status := .connecting } : ConnectionState)

/-- Action for `send`: noop. Forwarding to the appropriate connection
    engine requires a connection table mapping transport addresses to
    connection engine addresses, which is left abstract. -/
def protocolSendAction
    (w : A.TransportAddr × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.protocol)
    (_ : protocolSendGuard A inp = some w) :
    @Effect (S A) AnomaIdx.protocol :=
  letI := S A; Effect.noop

-- ============================================================================
-- § Behaviour assembly
-- ============================================================================

def protocolActions : @Behaviour (S A) AnomaIdx.protocol :=
  letI := S A
  [ { Witness := A.TransportAddr
      guard := protocolOpenConnectionGuard A
      action := protocolOpenConnectionAction A }
  , { Witness := A.TransportAddr
      guard := protocolIncomingConnectionGuard A
      action := protocolIncomingConnectionAction A }
  , { Witness := A.TransportAddr × A.ByteString
      guard := protocolSendGuard A
      action := protocolSendAction A } ]

private theorem protocolNonOverlapping :
    @NonOverlappingGuards (S A) _ (protocolActions A) := by
  letI := S A; intro inp
  simp only [protocolActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def protocolBehaviour : @WellFormedBehaviour (S A) AnomaIdx.protocol :=
  letI := S A
  { actions := protocolActions A
    nonOverlapping := protocolNonOverlapping A }

end MailboxActors.Examples.Anoma.Network
