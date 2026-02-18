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
  | terminate κ_old _ _ addr p _ heng _ hκ' =>
    subst hκ'
    exact updateEngineAt_preserves_invariants κ_old addr ⟨_, p⟩
      ⟨_, { p with status := .terminated }⟩ heng rfl rfl wt hiso
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
              -- m.target = mailboxOf target
              -- se_m is the engine at mailboxOf target
              obtain ⟨mboxSe, hmbox, hmboxIdx, _⟩ :=
                wt.mailbox_exists target se_target se_target.beq_self h_mode
              rw [hmbox] at hse_m; cases hse_m
              exact hmboxIdx.symm.trans h_idx
          · exact wt.messages_typed m hm se_m hse_m
        mailbox_exists := fun addr' se heng' hmode' =>
          wt.mailbox_exists addr' se heng' hmode'
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
  | spawn =>
    -- Spawn logic needs update for if-then-else
    sorry
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
