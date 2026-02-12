/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Progress

A well-typed system state with pending work can always take a step.
Paper Proposition 2.
-/

namespace MailboxActors

variable [EngineSpec]

/-- A state has pending work when messages are in transit, an engine is busy,
    or an engine is terminated (awaiting cleanup). -/
def hasPendingWork (κ : SystemState) : Prop :=
  κ.messages ≠ [] ∨
  (∃ addr se, κ.engineAt addr = some se ∧
    ∃ i v, se.idx = i ∧ se.engine.status = EngineStatus.busy v) ∨
  (∃ addr se, κ.engineAt addr = some se ∧
    ∃ (_ : se.idx = se.idx), se.engine.status = EngineStatus.terminated)

/-- **Progress**: a well-typed state with pending work can step.
    Paper Proposition 2. -/
theorem progress (κ : SystemState) :
    WellTypedState κ → hasPendingWork κ → ∃ κ', SysStep κ κ' := by
  sorry

end MailboxActors
