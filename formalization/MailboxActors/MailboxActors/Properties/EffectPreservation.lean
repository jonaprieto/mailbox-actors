import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Effect Preservation

EffectEvalStep preserves well-typedness and mailbox isolation.
These results are used by the S-Process case of type preservation
and mailbox isolation.
-/

namespace MailboxActors

variable [EngineSpec]

-- ── Helper: updateEngineAt with same idx and mode preserves invariants ──

/-- `updateEngineAt` with a replacement engine that has the same `idx` and
    `mode` preserves both `WellTypedState` and `MailboxIsolation`. -/
theorem updateEngineAt_preserves_invariants (κ : SystemState)
    (addr : Address) (se se' : SomeEngine)
    (heng : κ.engineAt addr = some se)
    (hidx : se'.idx = se.idx)
    (hmode : se'.engine.mode = se.engine.mode)
    (wt : WellTypedState κ) (hiso : MailboxIsolation κ) :
    WellTypedState (κ.updateEngineAt addr se') ∧
    MailboxIsolation (κ.updateEngineAt addr se') := by
  constructor
  · -- WellTypedState
    exact {
      messages_typed := fun m hm se_m hse_m => by
        simp only [SystemState.updateEngineAt_messages] at hm
        by_cases h : m.target = addr
        · subst h
          rw [engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩] at hse_m
          cases hse_m
          exact (wt.messages_typed m hm se heng).trans hidx.symm
        · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at hse_m
          exact wt.messages_typed m hm se_m hse_m
      mailbox_exists := fun addr' se'' heng' hmode' => by
        simp only [SystemState.updateEngineAt_mailboxOf] at ⊢
        by_cases h : addr' = addr
        · -- addr' = addr: updated engine, use mailbox from original wt
          rw [h] at heng' ⊢
          rw [engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩] at heng'
          cases heng'
          have hmode_orig : se.engine.mode = EngineMode.process := by
            rw [hmode] at hmode'; exact hmode'
          obtain ⟨mboxSe, hmbox, hmboxIdx, hmboxMode⟩ :=
            wt.mailbox_exists addr se heng hmode_orig
          have hne := mailboxOf_ne_self κ addr
          refine ⟨mboxSe, ?_, ?_, hmboxMode⟩
          · rw [engineAt_updateEngineAt_ne _ _ _ _ hne]; exact hmbox
          · exact hmboxIdx.trans hidx.symm
        · -- addr' ≠ addr: engine unchanged
          rw [engineAt_updateEngineAt_ne _ _ _ _ h] at heng'
          obtain ⟨mboxSe, hmbox, hmboxIdx, hmboxMode⟩ :=
            wt.mailbox_exists addr' se'' heng' hmode'
          by_cases hm : κ.mailboxOf addr' = addr
          · -- mailbox = addr: updated engine, same idx and mode
            refine ⟨se', ?_, ?_, ?_⟩
            · rw [hm]; exact engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩
            · rw [hm] at hmbox; rw [heng] at hmbox; cases hmbox
              rw [hidx]; exact hmboxIdx
            · rw [hm] at hmbox; rw [heng] at hmbox; cases hmbox
              rw [hmode]; exact hmboxMode
          · -- mailbox ≠ addr: unchanged
            refine ⟨mboxSe, ?_, hmboxIdx, hmboxMode⟩
            rw [engineAt_updateEngineAt_ne _ _ _ _ hm]; exact hmbox
      nextId_fresh := fun addr' hne => by
        simp only [SystemState.updateEngineAt_nextId]
        by_cases h : addr' = addr
        · rw [h] at hne ⊢; exact wt.nextId_fresh addr (by rw [heng]; simp)
        · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at hne
          exact wt.nextId_fresh addr' hne
      nextId_messages := fun m hm => by
        simp only [SystemState.updateEngineAt_messages, SystemState.updateEngineAt_nextId]
        exact wt.nextId_messages m hm
      nodes_exist := fun addr' hne => by
        have hne' : κ.engineAt addr' ≠ none := by
          by_cases h : addr' = addr
          · subst h; rw [heng]; simp
          · rwa [engineAt_updateEngineAt_ne _ _ _ _ h] at hne
        obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr' hne'
        simp only [SystemState.updateEngineAt]
        let f := fun n' : Node =>
          if n'.id == addr.nodeId then n'.setEngine addr.engineId se' else n'
        exact ⟨f n, List.mem_map.mpr ⟨n, hn, rfl⟩, by simp only [f]; split <;> exact hid⟩
    }
  · -- MailboxIsolation
    intro m hm se_m hse_m
    simp only [SystemState.updateEngineAt_messages] at hm
    by_cases h : m.target = addr
    · rw [h, engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩] at hse_m
      cases hse_m; rw [hmode]; exact hiso m hm se (by rw [h]; exact heng)
    · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at hse_m
      exact hiso m hm se_m hse_m

-- ── Main theorem: EffectEvalStep preserves both invariants ──────────────

/-- `EffectEvalStep` preserves both `WellTypedState` and `MailboxIsolation`.
    The proof proceeds by induction on the effect evaluation derivation. -/
theorem effectEvalStepPreservesInvariants (κ κ' : SystemState)
    (i : EngineSpec.EngIdx) (E : Effect i) :
    EffectEvalStep κ i E κ' →
    WellTypedState κ → MailboxIsolation κ →
    WellTypedState κ' ∧ MailboxIsolation κ' := by
  intro heff wt hiso
  induction heff with
  | noop => exact ⟨wt, hiso⟩
  | terminate κ_old _ _ addr p heng hκ' =>
    subst hκ'
    split
    · exact updateEngineAt_preserves_invariants κ_old addr ⟨_, p⟩
        ⟨_, { p with status := .terminated }⟩ heng rfl rfl wt hiso
    · exact ⟨wt, hiso⟩
  | update κ_old _ _ addr p _ newEnv heng hκ' =>
    subst hκ'
    exact updateEngineAt_preserves_invariants κ_old addr ⟨_, p⟩
      ⟨_, { p with env := newEnv }⟩ heng rfl rfl wt hiso
  | mfilter κ_old _ _ addr p _ f heng hκ' =>
    subst hκ'
    exact updateEngineAt_preserves_invariants κ_old addr ⟨_, p⟩
      ⟨_, { p with status := .ready f }⟩ heng rfl rfl wt hiso
  | send κ₀ _ _ addr _ _ j target _ heng hκ' =>
    subst hκ'
    -- Case-split on the match discriminant
    generalize h_target : κ₀.engineAt target = result at *
    cases result with
    | none => exact ⟨wt, hiso⟩
    | some se_target =>
      by_cases h_cond : se_target.idx = j ∧ se_target.engine.mode = EngineMode.process
      · -- condition true: messages were appended
        simp only [h_cond, and_self, ite_true]
        obtain ⟨h_idx, h_mode⟩ := h_cond
        obtain ⟨mboxSe, hmbox, hmboxIdx, hmboxMode⟩ :=
          wt.mailbox_exists target se_target h_target h_mode
        constructor
        · exact {
            messages_typed := fun m hm se_m hse_m => by
              rw [List.mem_append] at hm
              rcases hm with hm | hm
              · exact wt.messages_typed m hm se_m hse_m
              · rw [List.mem_singleton] at hm; subst hm
                have hse_m : κ₀.engineAt (κ₀.mailboxOf target) = some se_m := hse_m
                rw [hmbox] at hse_m; cases hse_m
                exact h_idx.symm.trans hmboxIdx.symm
            mailbox_exists := wt.mailbox_exists
            nextId_fresh := wt.nextId_fresh
            nextId_messages := fun m hm => by
              rw [List.mem_append] at hm
              rcases hm with hm | hm
              · exact wt.nextId_messages m hm
              · rw [List.mem_singleton] at hm; subst hm
                exact wt.nextId_fresh (κ₀.mailboxOf target) (by rw [hmbox]; simp)
            nodes_exist := wt.nodes_exist
          }
        · intro m hm se hse
          rw [List.mem_append] at hm
          rcases hm with hm | hm
          · exact hiso m hm se hse
          · rw [List.mem_singleton] at hm; subst hm
            have hse : κ₀.engineAt (κ₀.mailboxOf target) = some se := hse
            rw [hmbox] at hse; cases hse
            exact hmboxMode
      · simp only [h_cond, ite_false]; exact ⟨wt, hiso⟩
  | spawn κ₀ κ₁ _ j cfg env nid procSe mboxSe _ _ hnode hproc hmbox hidxP hidxM hmodeP hmodeM hκ₁ =>
    subst hκ₁; subst hproc; subst hmbox
    -- After subst: procAddr = ⟨nid, κ₀.nextId⟩, mboxAddr = κ₀.mailboxOf ⟨nid, κ₀.nextId⟩
    have hne : κ₀.mailboxOf ⟨nid, κ₀.nextId⟩ ≠ ⟨nid, κ₀.nextId⟩ :=
      mailboxOf_ne_self κ₀ _
    split
    · rename_i hfresh
      obtain ⟨hfreshP, hfreshM⟩ := hfresh
      constructor
      · -- WellTypedState
        exact {
          messages_typed := fun m hm se_m hse_m => by
            simp only [SystemState.addEngineAt_messages] at hm
            simp only [SystemState.withNextId_engineAt] at hse_m
            have hne_proc : m.target ≠ ⟨nid, κ₀.nextId⟩ := by
              intro h; have := wt.nextId_messages m hm; rw [h] at this; simp at this
            have hne_mbox : m.target ≠ κ₀.mailboxOf ⟨nid, κ₀.nextId⟩ := by
              intro h; have h₁ := wt.nextId_messages m hm
              have h₂ : m.target.engineId = κ₀.nextId + 1 := by rw [h]; rfl
              omega
            rw [engineAt_addEngineAt_ne _ _ _ _ hne_mbox,
                engineAt_addEngineAt_ne _ _ _ _ hne_proc] at hse_m
            exact wt.messages_typed m hm se_m hse_m
          mailbox_exists := fun addr se heng hmode => by
            simp only [SystemState.withNextId_engineAt, SystemState.withNextId_mailboxOf,
              SystemState.addEngineAt_mailboxOf] at heng ⊢
            by_cases hp : addr = ⟨nid, κ₀.nextId⟩
            · subst hp
              rw [engineAt_addEngineAt_ne _ _ _ _ hne.symm,
                  engineAt_addEngineAt_self _ _ _ hfreshP hnode] at heng
              cases heng
              refine ⟨mboxSe, ?_, hidxM.trans hidxP.symm, hmodeM⟩
              exact engineAt_addEngineAt_self _ _ _
                (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
                (addEngineAt_node_mem κ₀ _ _ _ hnode)
            · by_cases hm : addr = κ₀.mailboxOf ⟨nid, κ₀.nextId⟩
              · subst hm
                rw [engineAt_addEngineAt_self _ _ _
                  (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
                  (addEngineAt_node_mem κ₀ _ _ _ hnode)] at heng
                cases heng; rw [hmodeM] at hmode; exact absurd hmode (by decide)
              · rw [engineAt_addEngineAt_ne _ _ _ _ hm,
                    engineAt_addEngineAt_ne _ _ _ _ hp] at heng
                obtain ⟨mboxSe', hmbox', hmboxIdx', hmboxMode'⟩ :=
                  wt.mailbox_exists addr se heng hmode
                have hm1 : κ₀.mailboxOf addr ≠ κ₀.mailboxOf ⟨nid, κ₀.nextId⟩ := by
                  intro h; exact hp (mailboxOf_injective κ₀ h)
                have hm2 : κ₀.mailboxOf addr ≠ ⟨nid, κ₀.nextId⟩ := by
                  intro h; rw [h, hfreshP] at hmbox'; simp at hmbox'
                refine ⟨mboxSe', ?_, hmboxIdx', hmboxMode'⟩
                rw [engineAt_addEngineAt_ne _ _ _ _ hm1,
                    engineAt_addEngineAt_ne _ _ _ _ hm2]
                exact hmbox'
          nextId_fresh := fun addr hne_m => by
            simp only [SystemState.withNextId_engineAt] at hne_m
            by_cases hp : addr = ⟨nid, κ₀.nextId⟩
            · subst hp; simp
            · by_cases hm : addr = κ₀.mailboxOf ⟨nid, κ₀.nextId⟩
              · subst hm; simp [SystemState.mailboxOf]
              · rw [engineAt_addEngineAt_ne _ _ _ _ hm,
                    engineAt_addEngineAt_ne _ _ _ _ hp] at hne_m
                have := wt.nextId_fresh addr hne_m; simp; omega
          nextId_messages := fun m hm => by
            simp only [SystemState.addEngineAt_messages] at hm
            have := wt.nextId_messages m hm; simp; omega
          nodes_exist := fun addr hne_m => by
            simp only [SystemState.withNextId_engineAt] at hne_m
            by_cases hp : addr = ⟨nid, κ₀.nextId⟩
            · subst hp
              exact addEngineAt_node_mem _ _ _ _
                (addEngineAt_node_mem κ₀ _ _ _ hnode)
            · by_cases hm : addr = κ₀.mailboxOf ⟨nid, κ₀.nextId⟩
              · subst hm
                exact addEngineAt_node_mem _ _ _ _
                  (addEngineAt_node_mem κ₀ _ _ _ hnode)
              · rw [engineAt_addEngineAt_ne _ _ _ _ hm,
                    engineAt_addEngineAt_ne _ _ _ _ hp] at hne_m
                obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr hne_m
                exact addEngineAt_node_mem _ _ _ _
                  (addEngineAt_node_mem _ _ _ _ ⟨n, hn, hid⟩)
        }
      · -- MailboxIsolation
        intro m hm se hse
        simp only [SystemState.addEngineAt_messages] at hm
        simp only [SystemState.withNextId_engineAt] at hse
        by_cases hp : m.target = ⟨nid, κ₀.nextId⟩
        · exfalso; have h := wt.nextId_messages m hm; rw [hp] at h; simp at h
        · by_cases hm_addr : m.target = κ₀.mailboxOf ⟨nid, κ₀.nextId⟩
          · rw [hm_addr, engineAt_addEngineAt_self _ _ _
              (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
              (addEngineAt_node_mem κ₀ _ _ _ hnode)] at hse
            cases hse; exact hmodeM
          · rw [engineAt_addEngineAt_ne _ _ _ _ hm_addr,
                engineAt_addEngineAt_ne _ _ _ _ hp] at hse
            exact hiso m hm se hse
    · -- if not fresh, just nextId += 2
      constructor
      · exact {
          messages_typed := wt.messages_typed,
          mailbox_exists := wt.mailbox_exists,
          nextId_fresh := fun addr hne => by simp; have := wt.nextId_fresh addr hne; omega,
          nextId_messages := fun m hm => by simp; have := wt.nextId_messages m hm; omega,
          nodes_exist := wt.nodes_exist
        }
      · exact hiso
  | chain _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨wt₁, hiso₁⟩ := ih₁ wt hiso
    exact ih₂ wt₁ hiso₁

-- ── S-Process full preservation ─────────────────────────────────────────

/-- The full S-Process step (effect + resolvePostStatus) preserves both
    `WellTypedState` and `MailboxIsolation`. -/
theorem sProcessPreservesInvariants (κ κ' κ'' : SystemState)
    (addr : Address) (i : EngineSpec.EngIdx) (E : Effect i) :
    EffectEvalStep κ i E κ' →
    (∃ (p' : Engine i),
      κ'.engineAt addr = some ⟨i, p'⟩ ∧
      κ'' = κ'.updateEngineAt addr
        ⟨i, { p' with status := resolvePostStatus p'.status }⟩) →
    WellTypedState κ → MailboxIsolation κ →
    WellTypedState κ'' ∧ MailboxIsolation κ'' := by
  intro heff ⟨p', heng', hκ''⟩ wt hiso
  subst hκ''
  obtain ⟨wt', hiso'⟩ := effectEvalStepPreservesInvariants _ _ _ _ heff wt hiso
  exact updateEngineAt_preserves_invariants _ _ ⟨_, p'⟩
    ⟨_, { p' with status := resolvePostStatus p'.status }⟩
    heng' rfl rfl wt' hiso'

end MailboxActors
