import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Logging Engine — Behaviour

The logging engine provides append-only log storage. Each `append` message
adds an entry to the log and advances the write position.
-/

namespace MailboxActors.Examples.Anoma.Infra

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

/-- Guard for `append` messages. -/
@[simp] def loggingAppendGuard
    (inp : @GuardInput (S A) AnomaIdx.logging) :
    Option String :=
  match @GuardInput.msg (S A) _ inp with
  | .append s => some s

/-- Action for `append`: add the entry to the log and increment position. -/
def loggingAppendAction
    (w : String)
    (inp : @GuardInput (S A) AnomaIdx.logging)
    (_ : loggingAppendGuard A inp = some w) :
    @Effect (S A) AnomaIdx.logging :=
  letI := S A
  let env := inp.env
  Effect.update { env with
    localState := { entries := env.localState.entries ++ [w]
                    position := env.localState.position + 1 } }

def loggingActions : @Behaviour (S A) AnomaIdx.logging :=
  letI := S A
  [ { Witness := String
      guard := loggingAppendGuard A
      action := loggingAppendAction A } ]

private theorem loggingNonOverlapping :
    @NonOverlappingGuards (S A) _ (loggingActions A) := by
  letI := S A; intro inp
  simp only [loggingActions, List.filter]
  split <;> simp

def loggingBehaviour : @WellFormedBehaviour (S A) AnomaIdx.logging :=
  letI := S A
  { actions := loggingActions A
    nonOverlapping := loggingNonOverlapping A }

end MailboxActors.Examples.Anoma.Infra
