/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Basic
import MailboxActors.Engine.Config
import MailboxActors.Engine.Env
import MailboxActors.Engine.Effect

/-!
# Guards, Actions, and Guarded Actions

Paper Definitions 11–13.
-/

namespace MailboxActors

variable [EngineSpec]

/-- The input triple for guard and action evaluation. -/
structure GuardInput (i : EngineSpec.EngIdx) where
  msg : EngineSpec.MsgType i
  config : EngineConfig i
  env : EngineEnv i

/-- A guarded action pairs a guard with an action.
    The guard inspects the input and optionally extracts a witness;
    the action produces an effect given that witness and the input.

    For simplicity, the witness type is erased: the guard returns
    `Bool` and the action takes the full input.  Paper Definition 13. -/
structure GuardedAction (i : EngineSpec.EngIdx) where
  /-- The guard: returns `true` when the action should fire. -/
  guard : GuardInput i → Bool
  /-- The action: produces an effect from the input. -/
  action : GuardInput i → Effect i

/-- Apply a guarded action: if the guard matches, fire the action;
    otherwise produce `noop`.  Paper composite operation `g ⊙ a`. -/
def GuardedAction.apply (ga : GuardedAction i) (inp : GuardInput i) : Effect i :=
  if ga.guard inp then ga.action inp else Effect.noop

end MailboxActors
