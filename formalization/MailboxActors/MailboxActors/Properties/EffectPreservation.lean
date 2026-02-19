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
          exact hidx.trans (wt.messages_typed m hm se heng)
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
        by_cases h : addr' = addr
        · subst h
          obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr (by rw [heng]; simp)
          refine ⟨_, ?_, hid⟩
          simp only [SystemState.updateEngineAt]
          apply List.mem_map.mpr
          refine ⟨n, hn, ?_⟩
          split <;> simp [*]
        · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at hne
          obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr' hne
          refine ⟨_, ?_, hid⟩
          simp only [SystemState.updateEngineAt]
          apply List.mem_map.mpr
          refine ⟨n, hn, ?_⟩
          split <;> simp [*]
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
  | terminate κ_old _ _ addr p _ heng hκ' =>
    subst hκ'
    -- Note: E-Terminate is now an ITE in Judgment.lean
    split at hκ'
    · subst hκ'
      exact updateEngineAt_preserves_invariants κ_old addr ⟨_, p⟩
        ⟨_, { p with status := .terminated }⟩ heng rfl rfl wt hiso
    · subst hκ'; exact ⟨wt, hiso⟩
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
    constructor
    · -- WellTypedState: only messages changed, engines unchanged
      exact {
        messages_typed := fun m hm se_m hse_m => by
          split at hm
          · rw [List.mem_append] at hm
            rcases hm with hm | hm
            · exact wt.messages_typed m hm se_m hse_m
            · rw [List.mem_singleton] at hm; subst hm
              rename_i se_target h_match
              obtain ⟨h_idx, h_mode⟩ := h_match
              obtain ⟨mboxSe, hmbox, hmboxIdx, _⟩ :=
                wt.mailbox_exists target se_target se_target.beq_self h_mode
              rw [hmbox] at hse_m; cases hse_m
              exact hmboxIdx.symm.trans h_idx
          · exact wt.messages_typed m hm se_m hse_m
        mailbox_exists := fun addr' se heng' hmode' =>
          wt.mailbox_exists addr' se heng' hmode'
        nextId_fresh := wt.nextId_fresh
        nextId_messages := fun m hm => by
          split at hm
          · rw [List.mem_append] at hm
            rcases hm with hm | hm
            · exact wt.nextId_messages m hm
            · rw [List.mem_singleton] at hm; subst hm
              rename_i se_target _
              exact wt.nextId_fresh target (by rw [se_target.2]; simp)
          · exact wt.nextId_messages m hm
        nodes_exist := wt.nodes_exist
      }
    · -- MailboxIsolation
      intro m hm se hse
      split at hm
      · rw [List.mem_append] at hm
        rcases hm with hm | hm
        · exact hiso m hm se hse
        · rw [List.mem_singleton] at hm; subst hm
          rename_i se_target h_match
          obtain ⟨_, h_mode⟩ := h_match
          obtain ⟨mboxSe, hmbox, _, hmboxMode⟩ :=
            wt.mailbox_exists target se_target se_target.beq_self h_mode
          rw [hmbox] at hse; cases hse
          exact hmboxMode
      · exact hiso m hm se hse
  | spawn κ₀ κ₁ _ j cfg env nid procSe mboxSe procAddr mboxAddr hnode hproc hmbox hidxP hidxM hmodeP hmodeM hκ₁ =>
    subst hκ₁
    have hne : κ₀.mailboxOf ⟨nid, κ₀.nextId⟩ ≠ ⟨nid, κ₀.nextId⟩ :=
      mailboxOf_ne_self κ₀ _
    split at hκ₁
    · subst hκ₁
      constructor
      · -- WellTypedState
        exact {
          messages_typed := fun m hm se_m hse_m => by
            simp only [SystemState.addEngineAt_messages] at hm
            simp only [SystemState.withNextId_engineAt] at hse_m
            have hne_proc : m.target ≠ procAddr := by
              intro h; subst h; have := wt.nextId_fresh procAddr (by rw [hse_m]; simp);
              rw [hproc] at this; simp at this; omega
            have hne_mbox : m.target ≠ mboxAddr := by
              intro h; subst h; have := wt.nextId_fresh mboxAddr (by rw [hse_m]; simp);
              rw [hmbox] at this; simp at this; omega
            rw [engineAt_addEngineAt_ne _ _ _ _ hne_mbox,
                engineAt_addEngineAt_ne _ _ _ _ hne_proc] at hse_m
            exact wt.messages_typed m hm se_m hse_m
          mailbox_exists := fun addr se heng hmode => by
            simp only [SystemState.withNextId_engineAt, SystemState.withNextId_mailboxOf,
              SystemState.addEngineAt_mailboxOf] at heng ⊢
            by_cases hp : addr = procAddr
            · subst hp
              rw [engineAt_addEngineAt_ne _ _ _ _ hne.symm,
                  engineAt_addEngineAt_self _ _ _ (by rw [hproc]; rfl) hnode] at heng
              cases heng
              refine ⟨mboxSe, ?_, hidxM, hmodeM⟩
              exact engineAt_addEngineAt_self _ _ _
                (by rw [engineAt_addEngineAt_ne _ _ _ _ hne, hmbox]; rfl)
                (addEngineAt_node_mem κ₀ _ _ _ hnode)
            · by_cases hm : addr = mboxAddr
              · subst hm
                rw [engineAt_addEngineAt_self _ _ _
                  (by rw [engineAt_addEngineAt_ne _ _ _ _ hne, hmbox]; rfl)
                  (addEngineAt_node_mem κ₀ _ _ _ hnode)] at heng
                cases heng; rw [hmodeM] at hmode; exact absurd hmode (by decide)
              · rw [engineAt_addEngineAt_ne _ _ _ _ hm,
                    engineAt_addEngineAt_ne _ _ _ _ hp] at heng
                obtain ⟨mboxSe', hmbox', hmboxIdx', hmboxMode'⟩ :=
                  wt.mailbox_exists addr se heng hmode
                have hm1 : κ₀.mailboxOf addr ≠ mboxAddr := by
                  intro h; rw [hmbox] at h; exact hp (mailboxOf_injective κ₀ h)
                have hm2 : κ₀.mailboxOf addr ≠ procAddr := by
                  intro h; rw [h, hproc] at hmbox'; exact absurd hmbox' (by simp)
                refine ⟨mboxSe', ?_, hmboxIdx', hmboxMode'⟩
                rw [engineAt_addEngineAt_ne _ _ _ _ hm1,
                    engineAt_addEngineAt_ne _ _ _ _ hm2]
                exact hmbox'
          nextId_fresh := fun addr hne_m => by
            simp only [SystemState.withNextId_engineAt] at hne_m
            by_cases hp : addr = procAddr
            · subst hp; rw [hproc]; simp; omega
            · by_cases hm : addr = mboxAddr
              · subst hm; rw [hmbox]; simp; omega
              · rw [engineAt_addEngineAt_ne _ _ _ _ hm,
                    engineAt_addEngineAt_ne _ _ _ _ hp] at hne_m
                have := wt.nextId_fresh addr hne_m; simp; omega
          nextId_messages := fun m hm => by
            simp only [SystemState.addEngineAt_messages] at hm
            have := wt.nextId_messages m hm; simp; omega
          nodes_exist := fun addr hne_m => by
            simp only [SystemState.withNextId_engineAt] at hne_m
            by_cases hp : addr = procAddr
            · subst hp; exact hnode
            · by_cases hm : addr = mboxAddr
              · subst hm; exact addEngineAt_node_mem κ₀ _ _ _ hnode
              · rw [engineAt_addEngineAt_ne _ _ _ _ hm,
                    engineAt_addEngineAt_ne _ _ _ _ hp] at hne_m
                obtain ⟨n, hn, hid⟩ := wt.nodes_exist addr hne_m
                refine ⟨_, ?_, hid⟩
                exact addEngineAt_node_mem κ₀ _ _ _ (addEngineAt_node_mem κ₀ _ _ _ ⟨n, hn, hid⟩)
        }
      · -- MailboxIsolation
        intro m hm se hse
        simp only [SystemState.addEngineAt_messages] at hm
        simp only [SystemState.withNextId_engineAt] at hse
        by_cases hp : m.target = procAddr
        · subst hp; rw [engineAt_addEngineAt_ne _ _ _ _ hne.symm,
                        engineAt_addEngineAt_self _ _ _ (by rw [hproc]; rfl) hnode] at hse
          cases hse; -- mode is process, but isolation wants mail.
          -- Wait, m is in κ₀.messages. So m.target exists in κ₀.
          have := wt.nextId_fresh m.target (by intro h; obtain ⟨se_old, hse_old, _⟩ := wt.messages_typed m hm; rw [h] at hse_old; exact absurd hse_old (by simp))
          -- Actually we know κ₀.engineAt m.target ≠ none
          obtain ⟨se_old, hse_old, _⟩ := wt.messages_typed m hm
          have h_fresh := wt.nextId_fresh m.target (by rw [hse_old]; simp)
          subst_vars; simp [hproc] at h_fresh; omega
        · by_cases hm_addr : m.target = mboxAddr
          · subst hm_addr; rw [engineAt_addEngineAt_self _ _ _ (by rw [engineAt_addEngineAt_ne _ _ _ _ hne, hmbox]; rfl) (addEngineAt_node_mem κ₀ _ _ _ hnode)] at hse
            cases hse; exact hmodeM
          · rw [engineAt_addEngineAt_ne _ _ _ _ hm_addr,
                engineAt_addEngineAt_ne _ _ _ _ hp] at hse
            exact hiso m hm se hse
    · -- if not fresh, just nextId += 2
      subst hκ₁
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
