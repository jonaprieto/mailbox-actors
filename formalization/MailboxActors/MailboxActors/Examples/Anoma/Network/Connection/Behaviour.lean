import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Connection Engine — Behaviour

Each connection engine manages a single transport connection to a
remote node.  It handles encryption, sequence numbering, and
keep-alive messages.

## send
Sending data increments the outgoing `sequenceNumber` so the remote
end can detect reordering or loss.

## recv
Receiving data is currently a no-op.
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
def connectionSendGuard
    (inp : @GuardInput (S A) AnomaIdx.connection) :
    Option A.ByteString :=
  match @GuardInput.msg (S A) _ inp with
  | .send bs => some bs
  | _ => none

/-- Guard for `recv` messages. -/
@[simp]
def connectionRecvGuard
    (inp : @GuardInput (S A) AnomaIdx.connection) :
    Option A.ByteString :=
  match @GuardInput.msg (S A) _ inp with
  | .recv bs => some bs
  | _ => none

-- ============================================================================
-- § Actions
-- ============================================================================

/-- Action for `send`: increment the outgoing sequence number. -/
def connectionSendAction
    (w : A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.connection)
    (_ : connectionSendGuard A inp = some w) :
    @Effect (S A) AnomaIdx.connection :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with sequenceNumber := st.sequenceNumber + 1 } }

/-- Action for `recv`: no-op. -/
def connectionRecvAction
    (w : A.ByteString)
    (inp : @GuardInput (S A) AnomaIdx.connection)
    (_ : connectionRecvGuard A inp = some w) :
    @Effect (S A) AnomaIdx.connection :=
  letI := S A; Effect.noop

-- ============================================================================
-- § Behaviour assembly
-- ============================================================================

def connectionActions : @Behaviour (S A) AnomaIdx.connection :=
  letI := S A
  [ { Witness := A.ByteString
      guard := connectionSendGuard A
      action := connectionSendAction A }
  , { Witness := A.ByteString
      guard := connectionRecvGuard A
      action := connectionRecvAction A } ]

private theorem connectionNonOverlapping :
    @NonOverlappingGuards (S A) _ (connectionActions A) := by
  letI := S A; intro inp
  simp only [connectionActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def connectionBehaviour : @WellFormedBehaviour (S A) AnomaIdx.connection :=
  letI := S A
  { actions := connectionActions A
    nonOverlapping := connectionNonOverlapping A }

end MailboxActors.Examples.Anoma.Network
