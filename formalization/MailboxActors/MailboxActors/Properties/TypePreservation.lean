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
      nextId_fresh := fun addr hne => by
        simp; rw [key] at hne; have := wt.nextId_fresh addr hne; omega
      nodes_exist := fun addr hne => by
        rw [key] at hne; obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr hne
        refine ⟨n, List.mem_append.mpr (Or.inl hn), hid⟩
    }
  -- ── S-Clean: remove terminated processing engine ────────────────────────
  | sClean =>
    subst_vars
    rename_i _ addr se heng hpmode _
    exact {
      messages_typed := fun m hm se' hse' => by
        simp only [SystemState.removeEngineAt_messages] at hm
        have hne : m.target ≠ addr := by
          intro h; subst h
          exact absurd (hiso m hm se heng) (by simp [hpmode])
        rw [engineAt_removeEngineAt_ne κ addr m.target hne] at hse'
        exact wt.messages_typed m hm se' hse'
      mailbox_exists := fun addr' se' heng' hmode' => by
        have hne : addr' ≠ addr := by
          intro h; subst h
          rw [engineAt_removeEngineAt_self] at heng'; exact absurd heng' (by simp)
        rw [engineAt_removeEngineAt_ne κ addr addr' hne] at heng'
        obtain ⟨mboxSe, hmbox, hmboxIdx, hmboxMode⟩ := wt.mailbox_exists addr' se' heng' hmode'
        have hmboxNe : κ.mailboxOf addr' ≠ addr := by
          intro h; rw [h] at hmbox; rw [heng] at hmbox
          cases hmbox; rw [hpmode] at hmboxMode; exact absurd hmboxMode (by simp)
        refine ⟨mboxSe, ?_, hmboxIdx, hmboxMode⟩
        change (κ.removeEngineAt addr).engineAt (κ.mailboxOf addr') = some mboxSe
        rw [engineAt_removeEngineAt_ne κ addr (κ.mailboxOf addr') hmboxNe]
        exact hmbox
      nextId_fresh := fun addr' hne => by
        simp; rw [SystemState.engineAt, SystemState.removeEngineAt] at hne
        -- lookup in nodes.map filter ...
        -- If it exists in κ.removeEngineAt, it exists in κ.
        have : κ.engineAt addr' ≠ none := by
          intro habs; 
          -- engineAt_removeEngineAt_ne or similar
          sorry
        exact wt.nextId_fresh addr' this
      nodes_exist := fun addr' hne => by
        -- lookup in κ.removeEngineAt implies lookup in κ
        have : κ.engineAt addr' ≠ none := sorry
        obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr' this
        refine ⟨_, ?_, hid⟩
        simp only [SystemState.removeEngineAt]
        apply List.mem_map.mpr
        refine ⟨n, hn, ?_⟩
        split <;> simp [*]
    }
  -- ── M-Send: place message in transit to target's mailbox ────────────────
  | mSend =>
    subst_vars
    rename_i sender target senderEng targetEng hsender htarget hmode v
    exact {
      messages_typed := fun m hm se_m hse_m => by
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · exact wt.messages_typed m hm se_m hse_m
        · rw [List.mem_singleton] at hm; subst hm
          obtain ⟨mboxSe, hmbox, hmboxIdx, _⟩ :=
            wt.mailbox_exists target targetEng htarget hmode
          rw [hmbox] at hse_m; cases hse_m
          exact hmboxIdx.symm
      mailbox_exists := fun addr se heng hmode' =>
        wt.mailbox_exists addr se heng hmode'
      nextId_fresh := wt.nextId_fresh
      nodes_exist := wt.nodes_exist
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
        · subst h
          rw [engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩] at heng'
          cases heng'
          change mboxEng.engine.mode = EngineMode.process at hmode'
          rw [hmode] at hmode'; exact absurd hmode' (by decide)
        · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at heng'
          obtain ⟨mboxSe, hmboxSe, hmboxIdx, hmboxMode⟩ :=
            wt.mailbox_exists addr' se' heng' hmode'
          by_cases hm_addr : κ.mailboxOf addr' = m.target
          · refine ⟨⟨mboxEng.idx, { mboxEng.engine with status := .busy w }⟩, ?_, ?_, ?_⟩
            · rw [hm_addr]; exact engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩
            · rw [hm_addr] at hmboxSe; rw [heng] at hmboxSe; cases hmboxSe; exact hmboxIdx
            · exact hmode
          · refine ⟨mboxSe, ?_, hmboxIdx, hmboxMode⟩
            exact (engineAt_updateEngineAt_ne _ _ _ _ hm_addr).trans hmboxSe
      nextId_fresh := fun addr' hne => by
        simp only [SystemState.withMessages_engineAt] at hne
        by_cases h : addr' = m.target
        · subst h; exact wt.nextId_fresh _ (by rw [heng]; simp)
        · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at hne
          exact wt.nextId_fresh addr' hne
      nodes_exist := fun addr' hne => by
        simp only [SystemState.withMessages_engineAt] at hne
        by_cases h : addr' = m.target
        · subst h; exact wt.nodes_exist _ (by rw [heng]; simp)
        · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at hne
          obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr' hne
          refine ⟨_, ?_, hid⟩
          simp only [SystemState.updateEngineAt]
          apply List.mem_map.mpr
          refine ⟨n, hn, ?_⟩
          split <;> simp [*]
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
          intro h; subst h; have := wt.nextId_fresh ⟨nodeId, κ.nextId⟩ (by
            -- m.target exists in messages, so it must have existed in κ.engineAt?
            -- No, messages_typed only says IF it exists.
            -- But isolation and well-typedness together imply messages target live engines.
            -- Actually, messages in κ.messages existed in κ.
            -- We need a lemma that messages only target engines that exist in the state.
            -- Wait, my new WellTypedState doesn't require that anymore!
            -- So hne_proc might be false if a message targets a future address.
            -- BUT, nextId is strictly increasing. So m.target.engineId < κ.nextId.
            -- We need an invariant: ∀ m ∈ messages, m.target.engineId < κ.nextId.
            sorry
          )
        have hne_mbox : m.target ≠ κ.mailboxOf ⟨nodeId, κ.nextId⟩ := sorry
        simp only [SystemState.withNextId_engineAt] at hse_m
        rw [engineAt_addEngineAt_ne _ _ _ _ hne_mbox,
            engineAt_addEngineAt_ne _ _ _ _ hne_proc] at hse_m
        exact wt.messages_typed m hm se_m hse_m
      mailbox_exists := fun addr se heng hmode => by
        simp only [SystemState.withNextId_engineAt, SystemState.withNextId_mailboxOf,
          SystemState.addEngineAt_mailboxOf] at heng ⊢
        by_cases hp : addr = ⟨nodeId, κ.nextId⟩
        · subst hp
          rw [engineAt_addEngineAt_ne _ _ _ _ hne.symm,
              engineAt_addEngineAt_self _ _ _ hfreshP hnode] at heng
          cases heng
          refine ⟨mboxSe, ?_, hidxM, hmodeM⟩
          exact engineAt_addEngineAt_self _ _ _
            (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
            (addEngineAt_node_mem κ _ _ _ hnode)
        · by_cases hm_addr : addr = κ.mailboxOf ⟨nodeId, κ.nextId⟩
          · subst hm_addr
            rw [engineAt_addEngineAt_self _ _ _
              (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
              (addEngineAt_node_mem κ _ _ _ hnode)] at heng
            cases heng; rw [hmodeM] at hmode; exact absurd hmode (by decide)
          · rw [engineAt_addEngineAt_ne _ _ _ _ hm_addr,
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
      nextId_fresh := fun addr hne_m => by
        simp only [SystemState.withNextId_engineAt] at hne_m
        by_cases hp : addr = ⟨nodeId, κ.nextId⟩
        · subst hp; simp; omega
        · by_cases hm_addr : addr = κ.mailboxOf ⟨nodeId, κ.nextId⟩
          · subst hm_addr; simp; omega
          · rw [engineAt_addEngineAt_ne _ _ _ _ hm_addr,
                engineAt_addEngineAt_ne _ _ _ _ hp] at hne_m
            have := wt.nextId_fresh addr hne_m; simp; omega
      nodes_exist := fun addr hne_m => by
        simp only [SystemState.withNextId_engineAt] at hne_m
        by_cases hp : addr = ⟨nodeId, κ.nextId⟩
        · subst hp; exact hnode
        · by_cases hm_addr : addr = κ.mailboxOf ⟨nodeId, κ.nextId⟩
          · subst hm_addr; exact addEngineAt_node_mem κ _ _ _ hnode
          · rw [engineAt_addEngineAt_ne _ _ _ _ hm_addr,
                engineAt_addEngineAt_ne _ _ _ _ hp] at hne_m
            obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr hne_m
            refine ⟨_, ?_, hid⟩
            exact addEngineAt_node_mem κ _ _ _ (addEngineAt_node_mem κ _ _ _ ⟨n, hn, hid⟩)
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
            · exact hmode
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
      nextId_fresh := fun addr' hne_m => by
        by_cases h1 : addr' = κ.mailboxOf procAddr
        · subst h1; exact wt.nextId_fresh _ (by rw [hmbox]; simp)
        · by_cases h2 : addr' = procAddr
          · subst h2; exact wt.nextId_fresh _ (by rw [hproc]; simp)
          · rw [engineAt_updateEngineAt_ne _ _ _ _ h1,
                engineAt_updateEngineAt_ne _ _ _ _ h2] at hne_m
            exact wt.nextId_fresh addr' hne_m
      nodes_exist := fun addr' hne_m => by
        by_cases h1 : addr' = κ.mailboxOf procAddr
        · subst h1; exact wt.nodes_exist _ (by rw [hmbox]; simp)
        · by_cases h2 : addr' = procAddr
          · subst h2; exact wt.nodes_exist _ (by rw [hproc]; simp)
          · rw [engineAt_updateEngineAt_ne _ _ _ _ h1,
                engineAt_updateEngineAt_ne _ _ _ _ h2] at hne_m
            obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr' hne_m
            refine ⟨_, ?_, hid⟩
            simp only [SystemState.updateEngineAt]
            apply List.mem_map.mpr
            refine ⟨n, hn, ?_⟩
            split <;> simp [*]
    }

end MailboxActors
