/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Type Preservation

If a well-typed state takes a step, the resulting state is well-typed.
Paper Proposition 1.
-/

namespace MailboxActors

variable [EngineSpec]

/-- **Type Preservation**: transitions preserve well-typedness.
    Paper Proposition 1. -/
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
  -- ── S-Clean: placeholder κ' = κ ─────────────────────────────────────────
  | sClean => subst_vars; exact wt
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
  -- ── M-Enqueue: placeholder κ' = κ ──────────────────────────────────────
  | mEnqueue => subst_vars; exact wt
  -- ── M-Dequeue: placeholder κ' = κ ──────────────────────────────────────
  | mDequeue => subst_vars; exact wt

end MailboxActors
