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
      messages_typed := fun m hm => by
        simp only [SystemState.updateEngineAt_messages] at hm
        obtain ⟨se_old, hse_old, hidx_m⟩ := wt.messages_typed m hm
        by_cases h : m.target = addr
        · refine ⟨se', ?_, ?_⟩
          · rw [h]; exact engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩
          · rw [h] at hse_old; rw [heng] at hse_old; cases hse_old
            rw [hidx]; exact hidx_m
        · exact ⟨se_old, by rw [engineAt_updateEngineAt_ne _ _ _ _ h]; exact hse_old, hidx_m⟩
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
  | terminate κ_old _ _ addr p _ heng _ _ hκ' =>
    subst hκ'
    exact updateEngineAt_preserves_invariants κ_old addr ⟨_, p⟩
      ⟨_, { p with status := .terminated }⟩ heng rfl rfl wt hiso
  | update κ_old _ _ addr p _ newEnv heng _ hκ' =>
    subst hκ'
    exact updateEngineAt_preserves_invariants κ_old addr ⟨_, p⟩
      ⟨_, { p with env := newEnv }⟩ heng rfl rfl wt hiso
  | mfilter κ_old _ _ addr p _ f heng _ hκ' =>
    subst hκ'
    exact updateEngineAt_preserves_invariants κ_old addr ⟨_, p⟩
      ⟨_, { p with status := .ready f }⟩ heng rfl rfl wt hiso
  | spawn =>
    subst_vars
    rename_i _ κ₀ _ nid procSe mboxSe hnode hmodeP hmodeM _ _ hidxM hfreshP hfreshM
    -- After subst_vars, the ℕ-typed nodeId gets dagger suffix, so we use it implicitly
    have hne : κ₀.mailboxOf ⟨nid, κ₀.nextId⟩ ≠ ⟨nid, κ₀.nextId⟩ :=
      mailboxOf_ne_self κ₀ _
    constructor
    · -- WellTypedState (same pattern as sSpawnMbox in TypePreservation)
      exact {
        messages_typed := fun m hm => by
          simp only [SystemState.addEngineAt_messages] at hm
          obtain ⟨se, hse, hidx⟩ := wt.messages_typed m hm
          have hne_proc : m.target ≠ ⟨nid, κ₀.nextId⟩ := by
            intro h; rw [h, hfreshP] at hse; exact absurd hse (by simp)
          have hne_mbox : m.target ≠ κ₀.mailboxOf ⟨nid, κ₀.nextId⟩ := by
            intro h; rw [h, hfreshM] at hse; exact absurd hse (by simp)
          refine ⟨se, ?_, hidx⟩
          simp only [SystemState.withNextId_engineAt]
          rw [engineAt_addEngineAt_ne _ _ _ _ hne_mbox,
              engineAt_addEngineAt_ne _ _ _ _ hne_proc]
          exact hse
        mailbox_exists := fun addr se heng hmode => by
          simp only [SystemState.withNextId_engineAt, SystemState.withNextId_mailboxOf,
            SystemState.addEngineAt_mailboxOf] at heng ⊢
          by_cases hp : addr = ⟨nid, κ₀.nextId⟩
          · -- addr = procAddr: provide the freshly-spawned mailbox engine
            subst hp
            rw [engineAt_addEngineAt_ne _ _ _ _ hne.symm,
                engineAt_addEngineAt_self _ _ _ hfreshP hnode] at heng
            cases heng
            refine ⟨mboxSe, ?_, hidxM, hmodeM⟩
            exact engineAt_addEngineAt_self _ _ _
              (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
              (addEngineAt_node_mem κ₀ _ _ _ hnode)
          · by_cases hm : addr = κ₀.mailboxOf ⟨nid, κ₀.nextId⟩
            · -- addr = mboxAddr: mode is mail, contradicts hmode = process
              subst hm
              rw [engineAt_addEngineAt_self _ _ _
                (by rw [engineAt_addEngineAt_ne _ _ _ _ hne]; exact hfreshM)
                (addEngineAt_node_mem κ₀ _ _ _ hnode)] at heng
              cases heng; rw [hmodeM] at hmode; exact absurd hmode (by decide)
            · -- addr is neither: lookup unchanged, use existing wt
              rw [engineAt_addEngineAt_ne _ _ _ _ hm,
                  engineAt_addEngineAt_ne _ _ _ _ hp] at heng
              obtain ⟨mboxSe', hmbox, hmboxIdx, hmboxMode⟩ :=
                wt.mailbox_exists addr se heng hmode
              have hm1 : κ₀.mailboxOf addr ≠ κ₀.mailboxOf ⟨nid, κ₀.nextId⟩ := by
                intro h; exact hp (mailboxOf_injective κ₀ h)
              have hm2 : κ₀.mailboxOf addr ≠ ⟨nid, κ₀.nextId⟩ := by
                intro h; rw [h] at hmbox; rw [hfreshP] at hmbox; exact absurd hmbox (by simp)
              refine ⟨mboxSe', ?_, hmboxIdx, hmboxMode⟩
              rw [engineAt_addEngineAt_ne _ _ _ _ hm1,
                  engineAt_addEngineAt_ne _ _ _ _ hm2]
              exact hmbox
      }
    · -- MailboxIsolation (same pattern as sSpawnMbox in Isolation)
      intro m hm se hse
      simp only [SystemState.addEngineAt_messages] at hm
      simp only [SystemState.withNextId_engineAt] at hse
      obtain ⟨se_old, hse_old, _⟩ := wt.messages_typed m hm
      have hne_proc : m.target ≠ ⟨nid, κ₀.nextId⟩ := by
        intro h; rw [h, hfreshP] at hse_old; exact absurd hse_old (by simp)
      have hne_mbox : m.target ≠ κ₀.mailboxOf ⟨nid, κ₀.nextId⟩ := by
        intro h; rw [h, hfreshM] at hse_old; exact absurd hse_old (by simp)
      rw [engineAt_addEngineAt_ne _ _ _ _ hne_mbox,
          engineAt_addEngineAt_ne _ _ _ _ hne_proc] at hse
      exact hiso m hm se hse
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
