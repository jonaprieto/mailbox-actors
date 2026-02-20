import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# ReadsFor Delegation Engine -- Behaviour

## Submit

When `submit` arrives with read-evidence, the engine records the
evidence by incrementing `evidenceCount` in the local state.

## Query

When `query` arrives with an external identity, the engine should look
up whether a reads-for delegation relationship exists. Currently `noop`
because the reply would require the sender address.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § ReadDeleg Behaviour
-- ============================================================================

/-- Guard for `query` messages. -/
@[simp] def readDelegQueryGuard
    (inp : @GuardInput (S A) AnomaIdx.readDeleg) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .query eid => some eid
  | _ => none

/-- Action for `query`: intended to look up the reads-for relationship
    and reply with `EvidenceMsg.reply`. Currently `noop` because the
    sender address is not available in `GuardInput`. -/
def readDelegQueryAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.readDeleg)
    (_ : readDelegQueryGuard A inp = some w) :
    @Effect (S A) AnomaIdx.readDeleg :=
  letI := S A; Effect.noop

/-- Guard for `submit` messages. -/
@[simp] def readDelegSubmitGuard
    (inp : @GuardInput (S A) AnomaIdx.readDeleg) :
    Option A.ReadEvidence :=
  match @GuardInput.msg (S A) _ inp with
  | .submit ev => some ev
  | _ => none

/-- Action for `submit`: increment `evidenceCount` to record the
    newly submitted delegation evidence. -/
def readDelegSubmitAction
    (w : A.ReadEvidence)
    (inp : @GuardInput (S A) AnomaIdx.readDeleg)
    (_ : readDelegSubmitGuard A inp = some w) :
    @Effect (S A) AnomaIdx.readDeleg :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with evidenceCount := st.evidenceCount + 1 } }

def readDelegActions : @Behaviour (S A) AnomaIdx.readDeleg :=
  letI := S A
  [ { Witness := A.ExternalIdentity
      guard := readDelegQueryGuard A
      action := readDelegQueryAction A }
  , { Witness := A.ReadEvidence
      guard := readDelegSubmitGuard A
      action := readDelegSubmitAction A } ]

private theorem readDelegNonOverlapping :
    @NonOverlappingGuards (S A) _ (readDelegActions A) := by
  letI := S A; intro inp
  simp only [readDelegActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def readDelegBehaviour : @WellFormedBehaviour (S A) AnomaIdx.readDeleg :=
  letI := S A
  { actions := readDelegActions A
    nonOverlapping := readDelegNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
