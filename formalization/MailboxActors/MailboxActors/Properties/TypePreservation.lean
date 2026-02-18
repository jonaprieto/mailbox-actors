import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment
import MailboxActors.Properties.EffectPreservation

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
      messages_typed := fun m hm se hse => by
        exact wt.messages_typed m hm se (by rw [key] at hse; exact hse)
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
      messages_typed := fun m hm se' hse' => by
        simp only [SystemState.removeEngineAt_messages] at hm
        -- By MailboxIsolation, messages target mail engines; the cleaned
        -- engine is in process mode, so no message can target it.
        have hne : m.target ≠ addr := by
          intro h; subst h
          exact absurd (hiso m hm se heng) (by simp [hpmode])
        rw [engineAt_removeEngineAt_ne κ addr m.target hne] at hse'
        exact wt.messages_typed m hm se' hse'
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
      messages_typed := fun m hm se_m hse_m => by
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · -- old message: nodes unchanged, so engineAt is the same
          exact wt.messages_typed m hm se_m hse_m
        · -- new message: ⟨sender, κ.mailboxOf target, ⟨targetEng.idx, v⟩⟩
          rw [List.mem_singleton] at hm; subst hm
          -- By mailbox_exists the mailbox has the same type index as targetEng.
          obtain ⟨mboxSe, hmbox, hmboxIdx, _⟩ :=
            wt.mailbox_exists target targetEng htarget hmode
          rw [hmbox] at hse_m; cases hse_m
          exact hmboxIdx.symm
      mailbox_exists := fun addr se heng hmode' =>
        -- nodes unchanged, so engineAt and mailboxOf are the same
        wt.mailbox_exists addr se heng hmode'
    }
  -- ── M-Enqueue: deliver message, mailbox ready→busy ─────────────────────
  | mEnqueue =>
    subst_vars
    rename_i m mboxEng w _ pre post hmsg heng _ hmode _ _
    exact {
      messages_typed := fun m' hm' se_m' hse_m' => by
        simp only [SystemState.withMessages_engineAt] at hse_m'
        have hm'_old : m' ∈ κ.messages := by
          rw [hmsg]; simp only [List.mem_append, List.mem_cons] at hm' ⊢; tauto
        by_cases h : m'.target = m.target
        · subst h
          rw [engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩] at hse_m'
          cases hse_m'
          exact wt.messages_typed m' hm'_old mboxEng heng
        · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at hse_m'
          exact wt.messages_typed m' hm'_old se_m' hse_m'
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
  -- ── S-SpawnWithMailbox: spawn proc + mailbox engine ─────────────────────
  | sSpawnMbox =>
    subst_vars
    rename_i _ nodeId procSe mboxSe hnode hmodeP hmodeM hidxM hfreshP hfreshM
    have hne : κ.mailboxOf ⟨nodeId, κ.nextId⟩ ≠ ⟨nodeId, κ.nextId⟩ :=
      mailboxOf_ne_self κ _
    exact {
      messages_typed := fun m hm se_m hse_m => by
        simp only [SystemState.withNextId_messages, SystemState.addEngineAt_messages] at hm
        have hne_proc : m.target ≠ ⟨nodeId, κ.nextId⟩ := by
          intro h; rw [h, hfreshP] at wt; 
          -- Wait, I can use WellTypedState to show m.target is not a fresh address
          sorry
        have hne_mbox : m.target ≠ κ.mailboxOf ⟨nodeId, κ.nextId⟩ := by
          intro h; rw [h, hfreshM] at wt;
          sorry
        simp only [SystemState.withNextId_engineAt] at hse_m
        rw [engineAt_addEngineAt_ne _ _ _ _ hne_mbox,
            engineAt_addEngineAt_ne _ _ _ _ hne_proc] at hse_m
        exact wt.messages_typed m hm se_m hse_m
      mailbox_exists := fun addr se heng hmode => by
        simp only [SystemState.withNextId_engineAt, SystemState.withNextId_mailboxOf,
          SystemState.addEngineAt_mailboxOf] at heng ⊢
        by_cases hp : addr = ⟨nodeId, κ.nextId⟩
        · -- addr = procAddr: provide the freshly-spawned mailbox engine
          subst hp
          rw [engineAt_addEngineAt_ne _ _ _ _ hne.symm,
              engineAt_addEngineAt_self _ _ _ hfreshP hnode] at heng
          cases heng
          refine ⟨mboxSe, ?_, hidxM, hmodeM⟩
          exact engineAt_addEngineAt_self _ _ _
            (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
            (addEngineAt_node_mem κ _ _ _ hnode)
        · by_cases hm : addr = κ.mailboxOf ⟨nodeId, κ.nextId⟩
          · -- addr = mboxAddr: mode is mail, contradicts hmode = process
            subst hm
            rw [engineAt_addEngineAt_self _ _ _
              (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
              (addEngineAt_node_mem κ _ _ _ hnode)] at heng
            cases heng; rw [hmodeM] at hmode; exact absurd hmode (by decide)
          · -- addr is neither: lookup unchanged, use existing wt
            rw [engineAt_addEngineAt_ne _ _ _ _ hm,
                engineAt_addEngineAt_ne _ _ _ _ hp] at heng
            obtain ⟨mboxSe', hmbox, hmboxIdx, hmboxMode⟩ :=
              wt.mailbox_exists addr se heng hmode
            have hm1 : κ.mailboxOf addr ≠ κ.mailboxOf ⟨nodeId, κ.nextId⟩ := by
              intro h; exact hp (mailboxOf_injective κ h)
            have hm2 : κ.mailboxOf addr ≠ ⟨nodeId, κ.nextId⟩ := by
              intro h; rw [h] at hmbox; rw [hfreshP] at hmbox; exact absurd hmbox (by simp)
            refine ⟨mboxSe', ?_, hmboxIdx, hmboxMode⟩
            rw [engineAt_addEngineAt_ne _ _ _ _ hm1,
                engineAt_addEngineAt_ne _ _ _ _ hm2]
            exact hmbox
    }
  -- ── S-Process: engine processes a message ───────────────────────────────
  | sProcess _ _ _ _ _ _ _ _ _ _ heff hresolve =>
    exact (sProcessPreservesInvariants _ _ _ _ _ _ heff hresolve wt hiso).1
  -- ── M-Dequeue: transition proc→busy, update mailbox ────────────────────
  | mDequeue =>
    subst_vars
    rename_i _ procAddr i procEng mboxEng w v f hproc hpmode _ hmbox _ _ _
    set newMboxEnv : EngineEnv mboxEng.idx :=
      { mboxEng.engine.env with
        localState := EngineSpec.mailboxRemove mboxEng.engine.env.localState w } with hNewMboxEnv
    have hne : κ.mailboxOf procAddr ≠ procAddr := mailboxOf_ne_self κ procAddr
    obtain ⟨mboxSe, hmboxSe, hmboxIdx, hmboxMode⟩ :=
      wt.mailbox_exists procAddr ⟨i, procEng⟩ hproc hpmode
    rw [hmbox] at hmboxSe; cases hmboxSe
    set procEng' : SomeEngine := ⟨i, { procEng with status := .busy v }⟩
    have hmbox₁ : (κ.updateEngineAt procAddr procEng').engineAt
        (κ.mailboxOf procAddr) = some mboxEng := by
      rw [engineAt_updateEngineAt_ne _ _ _ _ hne]; exact hmbox
    exact {
      messages_typed := fun m hm se_m' hse_m' => by
        simp only [SystemState.updateEngineAt_messages] at hm
        by_cases h1 : m.target = κ.mailboxOf procAddr
        · subst h1
          rw [engineAt_updateEngineAt_self _ _ _ ⟨_, hmbox₁⟩] at hse_m'
          cases hse_m'
          exact wt.messages_typed m hm mboxEng hmbox
        · by_cases h2 : m.target = procAddr
          · subst h2
            rw [engineAt_updateEngineAt_ne _ _ _ _ (Ne.symm hne),
                   engineAt_updateEngineAt_self _ _ _ ⟨_, hproc⟩] at hse_m'
            cases hse_m'
            exact wt.messages_typed m hm ⟨i, procEng⟩ hproc
          · rw [engineAt_updateEngineAt_ne _ _ _ _ h1,
                engineAt_updateEngineAt_ne _ _ _ _ h2] at hse_m'
            exact wt.messages_typed m hm se_m' hse_m'
      mailbox_exists := fun addr' se' heng' hmode' => by
        by_cases h1 : addr' = κ.mailboxOf procAddr
        · subst h1
          rw [engineAt_updateEngineAt_self _ _ _ ⟨_, hmbox₁⟩] at heng'
          cases heng'
          change mboxEng.engine.mode = EngineMode.process at hmode'
          rw [hmboxMode] at hmode'; exact absurd hmode' (by decide)
        · by_cases h2 : addr' = procAddr
          · rw [h2] at heng'
            rw [engineAt_updateEngineAt_ne _ _ _ _ (Ne.symm hne),
                engineAt_updateEngineAt_self _ _ _ ⟨_, hproc⟩] at heng'
            cases heng'
            refine ⟨⟨mboxEng.idx, { mboxEng.engine with env := newMboxEnv }⟩, ?_, ?_, ?_⟩
            · rw [h2]
              exact engineAt_updateEngineAt_self _ _ _ ⟨_, hmbox₁⟩
            · exact hmboxIdx
            · exact hmboxMode
          · rw [engineAt_updateEngineAt_ne _ _ _ _ h1,
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
