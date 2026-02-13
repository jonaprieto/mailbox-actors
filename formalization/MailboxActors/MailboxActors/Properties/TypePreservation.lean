/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Type Preservation

If a well-typed state takes a step, the resulting state is well-typed.
-/

namespace MailboxActors

variable [EngineSpec]

/-- **Type Preservation**: transitions preserve well-typedness. -/
theorem typePreservation (κ κ' : SystemState) (op : OpLabel) :
    WellTypedState κ → OpStep κ op κ' → WellTypedState κ' := by
  intro wt step
  cases step with
  -- ── S-Node: create a new empty node ──────────────────────────────────────
  | sNode =>
    subst_vars
    -- engineAt is preserved because the new node has no engines.
    have key := engineAt_append_emptyNode κ
    exact {
      messages_typed := fun m hm => by
        obtain ⟨se, hse, hidx⟩ := wt.messages_typed m hm
        exact ⟨se, by rw [key]; exact hse, hidx⟩
      mailbox_exists := fun addr se heng hmode => by
        rw [key] at heng
        obtain ⟨mboxSe, hmbox, hmboxIdx, hmboxMode⟩ := wt.mailbox_exists addr se heng hmode
        exact ⟨mboxSe, by rw [key]; exact hmbox, hmboxIdx, hmboxMode⟩
    }
  -- ── S-Clean: remove terminated processing engine ────────────────────────
  | sClean =>
    subst_vars
    rename_i _ addr se heng hmode _ hnomsgs
    exact {
      messages_typed := fun m hm => by
        simp only [SystemState.removeEngineAt_messages] at hm
        obtain ⟨se', hse', hidx⟩ := wt.messages_typed m hm
        have hne := hnomsgs m hm
        exact ⟨se', by rw [engineAt_removeEngineAt_ne κ addr m.target hne]; exact hse', hidx⟩
      mailbox_exists := fun addr' se' heng' hmode' => by
        -- addr' ≠ addr: if it were, engineAt would be none (removeEngineAt_self)
        have hne : addr' ≠ addr := by
          intro h; subst h
          rw [engineAt_removeEngineAt_self] at heng'; exact absurd heng' (by simp)
        rw [engineAt_removeEngineAt_ne κ addr addr' hne] at heng'
        obtain ⟨mboxSe, hmbox, hmboxIdx, hmboxMode⟩ := wt.mailbox_exists addr' se' heng' hmode'
        -- κ.mailboxOf addr' ≠ addr: if it were, the mailbox would be process-mode
        -- (since se at addr has mode process), contradicting hmboxMode = mail.
        have hmboxNe : κ.mailboxOf addr' ≠ addr := by
          intro h; rw [h] at hmbox; rw [heng] at hmbox
          cases hmbox; rw [hmode] at hmboxMode; exact absurd hmboxMode (by simp)
        refine ⟨mboxSe, ?_, hmboxIdx, hmboxMode⟩
        -- mailboxOf ignores the state, so normalize to κ.mailboxOf
        change (κ.removeEngineAt addr).engineAt (κ.mailboxOf addr') = some mboxSe
        rw [engineAt_removeEngineAt_ne κ addr (κ.mailboxOf addr') hmboxNe]
        exact hmbox
    }
  -- ── M-Send: place message in transit to target's mailbox ────────────────
  | mSend =>
    subst_vars
    rename_i sender target senderEng targetEng hsender htarget hmode v
    exact {
      messages_typed := fun m hm => by
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · -- old message: nodes unchanged, so engineAt is the same
          exact wt.messages_typed m hm
        · -- new message: ⟨sender, κ.mailboxOf target, ⟨targetEng.idx, v⟩⟩
          rw [List.mem_singleton] at hm; subst hm
          -- By mailbox_exists the mailbox has the same type index as targetEng.
          obtain ⟨mboxSe, hmbox, hmboxIdx, _⟩ :=
            wt.mailbox_exists target targetEng htarget hmode
          exact ⟨mboxSe, hmbox, hmboxIdx.symm⟩
      mailbox_exists := fun addr se heng hmode' =>
        -- nodes unchanged, so engineAt and mailboxOf are the same
        wt.mailbox_exists addr se heng hmode'
    }
  -- ── M-Enqueue: message removed from transit ────────────────────────────
  | mEnqueue =>
    subst_vars
    rename_i pre post hmsg _ _
    exact {
      messages_typed := fun m' hm' => by
        apply wt.messages_typed
        rw [hmsg]
        simp only [List.mem_append, List.mem_cons] at hm' ⊢
        tauto
      mailbox_exists := fun addr se heng hmode =>
        wt.mailbox_exists addr se heng hmode
    }
  -- ── M-Dequeue: transition proc→busy, update mailbox ────────────────────
  | mDequeue => subst_vars; sorry

end MailboxActors
