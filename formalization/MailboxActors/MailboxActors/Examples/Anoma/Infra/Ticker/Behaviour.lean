import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Ticker Engine — Behaviour

The ticker maintains a monotonically increasing counter.
On each `increment` message it advances the counter by one.
The `getCount` and `count` messages support querying the current value.
-/

namespace MailboxActors.Examples.Anoma.Infra

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

/-- Guard for `increment` messages. -/
@[simp] def tickerIncrGuard
    (inp : @GuardInput (S A) AnomaIdx.ticker) :
    Option Unit :=
  match @GuardInput.msg (S A) _ inp with
  | .increment => some ()
  | _ => none

/-- Action for `increment`: advance the counter by one. -/
def tickerIncrAction
    (_ : Unit)
    (inp : @GuardInput (S A) AnomaIdx.ticker)
    (_ : tickerIncrGuard A inp = some ()) :
    @Effect (S A) AnomaIdx.ticker :=
  letI := S A
  let env := inp.env
  Effect.update { env with localState := { counter := env.localState.counter + 1 } }

/-- Guard for `getCount` messages. -/
@[simp] def tickerGetCountGuard
    (inp : @GuardInput (S A) AnomaIdx.ticker) :
    Option Unit :=
  match @GuardInput.msg (S A) _ inp with
  | .getCount => some ()
  | _ => none

/-- Action for `getCount`: no-op (response requires sender address). -/
def tickerGetCountAction
    (_ : Unit)
    (inp : @GuardInput (S A) AnomaIdx.ticker)
    (_ : tickerGetCountGuard A inp = some ()) :
    @Effect (S A) AnomaIdx.ticker :=
  letI := S A; Effect.noop

/-- Guard for `count` reply messages. -/
@[simp] def tickerCountGuard
    (inp : @GuardInput (S A) AnomaIdx.ticker) :
    Option Nat :=
  match @GuardInput.msg (S A) _ inp with
  | .count n => some n
  | _ => none

/-- Action for `count`: no-op (reply acknowledgement). -/
def tickerCountAction
    (w : Nat)
    (inp : @GuardInput (S A) AnomaIdx.ticker)
    (_ : tickerCountGuard A inp = some w) :
    @Effect (S A) AnomaIdx.ticker :=
  letI := S A; Effect.noop

def tickerActions : @Behaviour (S A) AnomaIdx.ticker :=
  letI := S A
  [ { Witness := Unit
      guard := tickerIncrGuard A
      action := tickerIncrAction A }
  , { Witness := Unit
      guard := tickerGetCountGuard A
      action := tickerGetCountAction A }
  , { Witness := Nat
      guard := tickerCountGuard A
      action := tickerCountAction A } ]

private theorem tickerNonOverlapping :
    @NonOverlappingGuards (S A) _ (tickerActions A) := by
  letI := S A; intro inp
  simp only [tickerActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def tickerBehaviour : @WellFormedBehaviour (S A) AnomaIdx.ticker :=
  letI := S A
  { actions := tickerActions A
    nonOverlapping := tickerNonOverlapping A }

end MailboxActors.Examples.Anoma.Infra
