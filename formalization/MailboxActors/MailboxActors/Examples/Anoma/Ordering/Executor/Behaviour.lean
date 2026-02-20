import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Executor Engine — Behaviour

## Read Reply Handling

When a `readReply` arrives from a shard, the executor:
1. Records the key as completed in `completedReads`.
2. The program state advances (abstractly) based on the received data.

The executor terminates when all reads and writes are complete.
-/

namespace MailboxActors.Examples.Anoma.Ordering

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Executor Behaviour
-- ============================================================================

/-- Guard for `readReply` messages. -/
@[simp] def executorReadReplyGuard
    (inp : @GuardInput (S A) AnomaIdx.executor) :
    Option (A.KVSKey × A.KVSDatum) :=
  match @GuardInput.msg (S A) _ inp with
  | .readReply key datum => some (key, datum)

/-- Action for `readReply`: record the key as read and update
    the program state. -/
def executorReadReplyAction
    (w : A.KVSKey × A.KVSDatum)
    (inp : @GuardInput (S A) AnomaIdx.executor)
    (_ : executorReadReplyGuard A inp = some w) :
    @Effect (S A) AnomaIdx.executor :=
  letI := S A
  let env := inp.env
  let st := env.localState
  Effect.update { env with
    localState := { st with
      completedReads := st.completedReads ++ [w.1] } }

def executorActions : @Behaviour (S A) AnomaIdx.executor :=
  letI := S A
  [ { Witness := A.KVSKey × A.KVSDatum
      guard := executorReadReplyGuard A
      action := executorReadReplyAction A } ]

private theorem executorNonOverlapping :
    @NonOverlappingGuards (S A) _ (executorActions A) := by
  letI := S A
  intro inp
  simp only [executorActions, List.filter]
  split <;> simp

def executorBehaviour : @WellFormedBehaviour (S A) AnomaIdx.executor :=
  letI := S A
  { actions := executorActions A
    nonOverlapping := executorNonOverlapping A }

end MailboxActors.Examples.Anoma.Ordering
