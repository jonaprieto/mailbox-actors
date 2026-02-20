import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# WallClock Engine — Behaviour
-/

namespace MailboxActors.Examples.Anoma.Infra

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

@[simp] def wallClockGetTimeGuard
    (inp : @GuardInput (S A) AnomaIdx.wallClock) :
    Option Unit :=
  match @GuardInput.msg (S A) _ inp with
  | .getTime => some ()
  | _ => none

/-- Action for `getTime`: in a full implementation, this would reply
    with the current epoch to the requester. -/
def wallClockGetTimeAction
    (_ : Unit)
    (inp : @GuardInput (S A) AnomaIdx.wallClock)
    (_ : wallClockGetTimeGuard A inp = some ()) :
    @Effect (S A) AnomaIdx.wallClock :=
  letI := S A; Effect.noop

@[simp] def wallClockTimeReplyGuard
    (inp : @GuardInput (S A) AnomaIdx.wallClock) :
    Option A.Epoch :=
  match @GuardInput.msg (S A) _ inp with
  | .timeReply ep => some ep
  | _ => none

/-- Action for `timeReply`: update the local state with the received epoch. -/
def wallClockTimeReplyAction
    (w : A.Epoch)
    (inp : @GuardInput (S A) AnomaIdx.wallClock)
    (_ : wallClockTimeReplyGuard A inp = some w) :
    @Effect (S A) AnomaIdx.wallClock :=
  letI := S A
  let env := inp.env
  Effect.update { env with localState := { currentEpoch := w } }

def wallClockActions : @Behaviour (S A) AnomaIdx.wallClock :=
  letI := S A
  [ { Witness := Unit
      guard := wallClockGetTimeGuard A
      action := wallClockGetTimeAction A }
  , { Witness := A.Epoch
      guard := wallClockTimeReplyGuard A
      action := wallClockTimeReplyAction A } ]

private theorem wallClockNonOverlapping :
    @NonOverlappingGuards (S A) _ (wallClockActions A) := by
  letI := S A; intro inp
  simp only [wallClockActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def wallClockBehaviour : @WellFormedBehaviour (S A) AnomaIdx.wallClock :=
  letI := S A
  { actions := wallClockActions A
    nonOverlapping := wallClockNonOverlapping A }

end MailboxActors.Examples.Anoma.Infra
