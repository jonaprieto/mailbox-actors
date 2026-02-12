/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Engine.Guard

/-!
# Engine Behaviour
-/

namespace MailboxActors

variable [EngineSpec]

/-- A behaviour is a list of guarded actions. -/
abbrev Behaviour (i : EngineSpec.EngIdx) := List (GuardedAction i)

/-- Non-overlapping guards: for any input, at most one guarded action
    produces a non-`noop` effect. -/
def NonOverlappingGuards (b : Behaviour i) : Prop :=
  ∀ (inp : GuardInput i),
    (b.filter (fun ga => ga.guard inp)).length ≤ 1

/-- A well-formed behaviour bundles a list of guarded actions with a proof
    of non-overlapping guards, so downstream theorems need not take
    `NonOverlappingGuards` as a separate hypothesis. -/
structure WellFormedBehaviour (i : EngineSpec.EngIdx) where
  /-- The underlying list of guarded actions. -/
  actions : List (GuardedAction i)
  /-- Proof that guards do not overlap. -/
  nonOverlapping : NonOverlappingGuards actions

end MailboxActors
