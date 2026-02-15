import MailboxActors.Basic
import MailboxActors.Engine.Config
import MailboxActors.Engine.Env
import MailboxActors.Engine.Effect

/-!
# Guards, Actions, and Guarded Actions

## Design note

Two refinements simplify the development:

1. **Dependent action type.** The action field of `GuardedAction` has type
   `(inp : GuardInput i) → guard inp = true → Effect i`, recording that the
   action is only invoked when the guard holds. This makes the guard-match
   proof available inside the action and in semantic rules, eliminating a
   separate assumption.

2. **Well-formed behaviours** (see `Behaviour.lean`): behaviours carry a
   proof of non-overlapping guards, so downstream theorems need not take
   `NonOverlappingGuards` as a hypothesis.
-/

namespace MailboxActors

variable [EngineSpec]

/-- The input triple for guard and action evaluation. -/
structure GuardInput (i : EngineSpec.EngIdx) where
  msg : EngineSpec.MsgType i
  config : EngineConfig i
  env : EngineEnv i

/-- A guarded action pairs a guard with an action.

    The action is dependently typed: it may only be applied when
    `guard inp = some w`, so the type system enforces the invariant
    "action only when guard holds." -/
structure GuardedAction (i : EngineSpec.EngIdx) where
  Witness : Type
  /-- The guard: returns `some w` when the action should fire, providing a witness `w`. -/
  guard : GuardInput i → Option Witness
  /-- The action: produces an effect, given an input **and** a proof that
      the guard holds on that input with witness `w`. -/
  action : (w : Witness) → (inp : GuardInput i) → guard inp = some w → Effect i

/-- Apply a guarded action: if the guard matches, fire the action
    (passing the proof that the guard holds); otherwise produce `noop`. -/
def GuardedAction.apply (ga : GuardedAction i) (inp : GuardInput i) : Effect i :=
  match h : ga.guard inp with
  | some w => ga.action w inp h
  | none   => Effect.noop

end MailboxActors
