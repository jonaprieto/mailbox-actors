/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Engine.Guard

/-!
# Engine Behaviour

Paper Definitions 14–15.
-/

namespace MailboxActors

variable [EngineSpec]

/-- A behaviour is a list of guarded actions.  Paper Definition 14. -/
abbrev Behaviour (i : EngineSpec.EngIdx) := List (GuardedAction i)

/-- Non-overlapping guards: for any input, at most one guarded action
    produces a non-`noop` effect.  Paper Definition 15. -/
def NonOverlappingGuards (b : Behaviour i) : Prop :=
  ∀ (inp : GuardInput i),
    (b.filter (fun ga => ga.guard inp)).length ≤ 1

end MailboxActors
