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
        exact ⟨{ κ with messages := rest }, OpLabel.enqueue,
          OpStep.mEnqueue κ _ m mboxSe [] rest hne hmbox hmode rfl⟩
      | process =>
        obtain ⟨mboxSe', hmbox', _⟩ := wt.mailbox_exists m.target mboxSe hmbox hmode
        exact ⟨κ, OpLabel.dequeue, OpStep.mDequeue κ κ m.target mboxSe mboxSe'
          hmbox hmode hmbox' rfl⟩
  · -- Case 2: busy engine
    cases hmode : se.engine.mode with
    | process =>
      obtain ⟨mboxSe, hmbox, _⟩ := wt.mailbox_exists addr se heng hmode
      exact ⟨κ, OpLabel.dequeue, OpStep.mDequeue κ κ addr se mboxSe heng hmode hmbox rfl⟩
    | mail =>
      exact ⟨_, OpLabel.node, OpStep.sNode κ _ κ.nextId rfl rfl⟩
  · -- Case 3: terminated engine → S-Clean
    exact ⟨κ.removeEngineAt addr, OpLabel.clean,
      OpStep.sClean κ (κ.removeEngineAt addr) 0 addr se heng ⟨rfl, hterm⟩ rfl⟩

end MailboxActors
