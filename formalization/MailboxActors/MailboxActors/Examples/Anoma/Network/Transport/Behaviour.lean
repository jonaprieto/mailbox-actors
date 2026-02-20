import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Transport Engine — Behaviour

The transport engine manages protocol-level connections.  It delegates
to protocol-specific engines for actual data transfer.

All actions are currently no-ops; the guards exist to match every
message constructor so that the behaviour is total.
-/

namespace MailboxActors.Examples.Anoma.Network

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Guards
-- ============================================================================

/-- Guard for `send` messages. -/
@[simp]
def transportSendGuard
    (inp : @GuardInput (S A) AnomaIdx.transport) :
    Option (A.TransportAddr × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .send addr bs => some (addr, bs)
  | _ => none

/-- Guard for `recv` messages. -/
@[simp]
def transportRecvGuard
    (inp : @GuardInput (S A) AnomaIdx.transport) :
    Option (A.TransportAddr × A.ByteString) :=
  match @GuardInput.msg (S A) _ inp with
  | .recv addr bs => some (addr, bs)
  | _ => none

/-- Guard for `connectionEstablished` messages. -/
@[simp]
def transportConnectionEstablishedGuard
    (inp : @GuardInput (S A) AnomaIdx.transport) :
    Option A.TransportAddr :=
  match @GuardInput.msg (S A) _ inp with
  | .connectionEstablished addr => some addr
  | _ => none

-- ============================================================================
-- § Actions
-- ============================================================================

/-- Action for `send`: no-op. -/
def transportSendAction
    (w : A.TransportAddr × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.transport)
    (_ : transportSendGuard A inp = some w) :
    @Effect (S A) AnomaIdx.transport :=
  letI := S A; Effect.noop

/-- Action for `recv`: no-op. -/
def transportRecvAction
    (w : A.TransportAddr × A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.transport)
    (_ : transportRecvGuard A inp = some w) :
    @Effect (S A) AnomaIdx.transport :=
  letI := S A; Effect.noop

/-- Action for `connectionEstablished`: no-op. -/
def transportConnectionEstablishedAction
    (w : A.TransportAddr)
    (inp : @GuardInput (S A) AnomaIdx.transport)
    (_ : transportConnectionEstablishedGuard A inp = some w) :
    @Effect (S A) AnomaIdx.transport :=
  letI := S A; Effect.noop

-- ============================================================================
-- § Behaviour assembly
-- ============================================================================

def transportActions : @Behaviour (S A) AnomaIdx.transport :=
  letI := S A
  [ { Witness := A.TransportAddr × A.ByteString
      guard := transportSendGuard A
      action := transportSendAction A }
  , { Witness := A.TransportAddr × A.ByteString
      guard := transportRecvGuard A
      action := transportRecvAction A }
  , { Witness := A.TransportAddr
      guard := transportConnectionEstablishedGuard A
      action := transportConnectionEstablishedAction A } ]

private theorem transportNonOverlapping :
    @NonOverlappingGuards (S A) _ (transportActions A) := by
  letI := S A; intro inp
  simp only [transportActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def transportBehaviour : @WellFormedBehaviour (S A) AnomaIdx.transport :=
  letI := S A
  { actions := transportActions A
    nonOverlapping := transportNonOverlapping A }

end MailboxActors.Examples.Anoma.Network
