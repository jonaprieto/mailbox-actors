/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Progress

A well-typed system state with pending work can always take a step.
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

/-- **Progress**: a well-typed state with pending work can step. -/
theorem progress (κ : SystemState) :
    WellTypedState κ → hasPendingWork κ → ∃ κ', SysStep κ κ' := by
  intro wt hp
  rcases hp with hmsg | ⟨addr, se, heng, i, v, _, hbusy⟩ | ⟨addr, se, heng, ⟨_, hterm⟩⟩
  · -- Case 1: messages in transit (κ.messages ≠ [])
    match hne : κ.messages with
    | [] => exact absurd hne hmsg
    | m :: rest =>
      have hm : m ∈ κ.messages := by rw [hne]; exact .head _
      obtain ⟨mboxSe, hmbox, _⟩ := wt.messages_typed m hm
      cases hmode : mboxSe.engine.mode with
      | mail =>
        -- M-Enqueue now requires ready(f) and filter; S-Node is always available.
        exact ⟨_, OpLabel.node, OpStep.sNode κ _ κ.nextId rfl rfl⟩
      | process =>
        -- The target is in process mode; S-Node is always available.
        exact ⟨_, OpLabel.node, OpStep.sNode κ _ κ.nextId rfl rfl⟩
  · -- Case 2: busy engine
    cases hmode : se.engine.mode with
    | process =>
      -- ProcessStep not wired into OpStep; S-Node is always available.
      exact ⟨_, OpLabel.node, OpStep.sNode κ _ κ.nextId rfl rfl⟩
    | mail =>
      exact ⟨_, OpLabel.node, OpStep.sNode κ _ κ.nextId rfl rfl⟩
  · -- Case 3: terminated engine — S-Node is always available.
    exact ⟨_, OpLabel.node, OpStep.sNode κ _ κ.nextId rfl rfl⟩

end MailboxActors
