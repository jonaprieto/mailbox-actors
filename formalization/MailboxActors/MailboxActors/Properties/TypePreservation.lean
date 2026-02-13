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

/-- **Type Preservation**: transitions preserve well-typedness.
    Requires `MailboxIsolation` so that S-Clean (which only removes the
    processing engine, not its mailbox) cannot orphan message targets. -/
theorem typePreservation (κ κ' : SystemState) (op : OpLabel) :
    WellTypedState κ → MailboxIsolation κ → OpStep κ op κ' → WellTypedState κ' := by
  intro wt hiso step
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
    rename_i _ addr se heng hpmode _
    exact {
      messages_typed := fun m hm => by
        simp only [SystemState.removeEngineAt_messages] at hm
        obtain ⟨se', hse', hidx⟩ := wt.messages_typed m hm
        -- By MailboxIsolation, messages target mail engines; the cleaned
        -- engine is in process mode, so no message can target it.
        have hne : m.target ≠ addr := by
          intro h; subst h
          exact absurd (hiso m hm se heng) (by simp [hpmode])
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
          cases hmbox; rw [hpmode] at hmboxMode; exact absurd hmboxMode (by simp)
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
  -- ── M-Enqueue: deliver message, mailbox ready→busy ─────────────────────
  | mEnqueue =>
    subst_vars
    rename_i m mboxEng w _ pre post hmsg heng _ hmode _ _
    exact {
      messages_typed := fun m' hm' => by
        simp only [SystemState.withMessages_engineAt]
        have hm'_old : m' ∈ κ.messages := by
          rw [hmsg]; simp only [List.mem_append, List.mem_cons] at hm' ⊢; tauto
        obtain ⟨se_old, hse_old, hidx_old⟩ := wt.messages_typed m' hm'_old
        by_cases h : m'.target = m.target
        · refine ⟨⟨mboxEng.idx, { mboxEng.engine with status := .busy w }⟩, ?_, ?_⟩
          · rw [h, engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩]
          · rw [h] at hse_old; rw [heng] at hse_old; cases hse_old; exact hidx_old
        · exact ⟨se_old, by rw [engineAt_updateEngineAt_ne _ _ _ _ h]; exact hse_old, hidx_old⟩
      mailbox_exists := fun addr' se' heng' hmode' => by
        simp only [SystemState.withMessages_engineAt, SystemState.withMessages_mailboxOf,
          SystemState.updateEngineAt_mailboxOf] at heng' ⊢
        by_cases h : addr' = m.target
        · -- addr' = m.target: mode is mail, contradicts process
          subst h
          rw [engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩] at heng'
          cases heng'
          change mboxEng.engine.mode = EngineMode.process at hmode'
          rw [hmode] at hmode'; exact absurd hmode' (by decide)
        · -- addr' ≠ m.target: engine unchanged
          rw [engineAt_updateEngineAt_ne _ _ _ _ h] at heng'
          obtain ⟨mboxSe, hmboxSe, hmboxIdx, hmboxMode⟩ :=
            wt.mailbox_exists addr' se' heng' hmode'
          by_cases hm : κ.mailboxOf addr' = m.target
          · -- mailboxOf addr' = m.target: updated engine, same idx and mode
            refine ⟨⟨mboxEng.idx, { mboxEng.engine with status := .busy w }⟩, ?_, ?_, ?_⟩
            · rw [hm]; exact engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩
            · rw [hm] at hmboxSe; rw [heng] at hmboxSe; cases hmboxSe; exact hmboxIdx
            · exact hmode
          · -- neither: engine unchanged
            refine ⟨mboxSe, ?_, hmboxIdx, hmboxMode⟩
            exact (engineAt_updateEngineAt_ne _ _ _ _ hm).trans hmboxSe
    }
  -- ── M-Dequeue: transition proc→busy, update mailbox ────────────────────
  | mDequeue =>
    subst_vars
    rename_i procAddr i procEng mboxEng v f newMboxEnv hproc hpmode _ hmbox _
    have hne : κ.mailboxOf procAddr ≠ procAddr := mailboxOf_ne_self κ procAddr
    -- Derive mailbox engine properties from WellTypedState
    obtain ⟨mboxSe, hmboxSe, hmboxIdx, hmboxMode⟩ :=
      wt.mailbox_exists procAddr ⟨i, procEng⟩ hproc hpmode
    rw [hmbox] at hmboxSe; cases hmboxSe
    -- Now: hmboxIdx : mboxEng.idx = i, hmboxMode : mboxEng.engine.mode = mail
    -- Helper: the intermediate state preserves the mailbox engine
    set procEng' : SomeEngine := ⟨i, { procEng with status := .busy v }⟩
    have hmbox₁ : (κ.updateEngineAt procAddr procEng').engineAt
        (κ.mailboxOf procAddr) = some mboxEng := by
      rw [engineAt_updateEngineAt_ne _ _ _ _ hne]; exact hmbox
    exact {
      messages_typed := fun m hm => by
        simp only [SystemState.updateEngineAt_messages] at hm
        obtain ⟨se_old, hse_old, hidx⟩ := wt.messages_typed m hm
        by_cases h1 : m.target = κ.mailboxOf procAddr
        · -- target = mailbox: updated engine has same idx
          refine ⟨⟨mboxEng.idx, { mboxEng.engine with env := newMboxEnv }⟩, ?_, ?_⟩
          · rw [h1, engineAt_updateEngineAt_self _ _ _ ⟨_, hmbox₁⟩]
          · rw [h1] at hse_old; rw [hmbox] at hse_old; cases hse_old; exact hidx
        · by_cases h2 : m.target = procAddr
          · -- target = proc address: updated engine has same idx
            refine ⟨⟨i, { procEng with status := .busy v }⟩, ?_, ?_⟩
            · rw [h2, engineAt_updateEngineAt_ne _ _ _ _ (Ne.symm hne),
                   engineAt_updateEngineAt_self _ _ _ ⟨_, hproc⟩]
            · rw [h2] at hse_old; rw [hproc] at hse_old; cases hse_old; exact hidx
          · -- target = neither: lookup unchanged
            refine ⟨se_old, ?_, hidx⟩
            rw [engineAt_updateEngineAt_ne _ _ _ _ h1,
                engineAt_updateEngineAt_ne _ _ _ _ h2]
            exact hse_old
      mailbox_exists := fun addr' se' heng' hmode' => by
        by_cases h1 : addr' = κ.mailboxOf procAddr
        · -- addr' = mailbox: engine mode is mail, contradicts hmode' = process
          subst h1
          rw [engineAt_updateEngineAt_self _ _ _ ⟨_, hmbox₁⟩] at heng'
          cases heng'
          -- mode after {with env := ...} is still mboxEng.engine.mode = mail
          change mboxEng.engine.mode = EngineMode.process at hmode'
          rw [hmboxMode] at hmode'; exact absurd hmode' (by decide)
        · by_cases h2 : addr' = procAddr
          · -- addr' = proc: provide the updated mailbox engine
            rw [h2] at heng'
            rw [engineAt_updateEngineAt_ne _ _ _ _ (Ne.symm hne),
                engineAt_updateEngineAt_self _ _ _ ⟨_, hproc⟩] at heng'
            cases heng'
            refine ⟨⟨mboxEng.idx, { mboxEng.engine with env := newMboxEnv }⟩, ?_, ?_, ?_⟩
            · -- mailboxOf ignores the state, so exact handles definitional eq
              rw [h2]
              exact engineAt_updateEngineAt_self _ _ _ ⟨_, hmbox₁⟩
            · exact hmboxIdx
            · exact hmboxMode
          · -- addr' = neither: engine and mailbox unchanged
            rw [engineAt_updateEngineAt_ne _ _ _ _ h1,
                engineAt_updateEngineAt_ne _ _ _ _ h2] at heng'
            obtain ⟨mboxSe', hmboxSe', hmboxIdx', hmboxMode'⟩ :=
              wt.mailbox_exists addr' se' heng' hmode'
            have hm1 : κ.mailboxOf addr' ≠ κ.mailboxOf procAddr := by
              intro h; exact h2 (mailboxOf_injective κ h)
            have hm2 : κ.mailboxOf addr' ≠ procAddr := by
              intro h; rw [h] at hmboxSe'; rw [hproc] at hmboxSe'; cases hmboxSe'
              rw [hpmode] at hmboxMode'; exact absurd hmboxMode' (by simp)
            refine ⟨mboxSe', ?_, hmboxIdx', hmboxMode'⟩
            exact (engineAt_updateEngineAt_ne _ _ _ _ hm1).trans
              ((engineAt_updateEngineAt_ne _ _ _ _ hm2).trans hmboxSe')
    }

end MailboxActors
