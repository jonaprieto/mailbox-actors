import MailboxActors.Engine.Behaviour
import MailboxActors.Semantics.Judgment

/-!
# Effect Determinism

Behaviour evaluation is deterministic.  Non-overlapping guards are
guaranteed by `WellFormedBehaviour`, so no explicit hypothesis is needed.
-/

namespace MailboxActors

variable [EngineSpec]

/-- Guard evaluation is deterministic: for a given engine, guarded action,
    and message, the effect is uniquely determined by the guard function. -/
private
lemma guardEvalStep_det
    {i : EngineSpec.EngIdx}
    {p : Engine i}
    {ga : GuardedAction i}
    {v : EngineSpec.MsgType i}
    {E₁ E₂ : Effect i}
    (h₁ : GuardEvalStep i p ga v E₁)
    (h₂ : GuardEvalStep i p ga v E₂)
    : E₁ = E₂
    := by
  cases h₁ with
  | guardMatch inp₁ w₁ hg₁ _ hinp₁ =>
    subst hinp₁
    cases h₂ with
    | guardMatch inp₂ w₂ hg₂ _ hinp₂ =>
      subst hinp₂
      have hw : w₁ = w₂ := by injection hg₁.symm.trans hg₂
      subst hw; rfl
    | guardFail inp₂ _ hinp₂ hg₂ => subst hinp₂; simp_all
  | guardFail inp₁ _ hinp₁ hg₁ =>
    subst hinp₁
    cases h₂ with
    | guardMatch inp₂ _ _ _ hinp₂ => subst hinp₂; simp_all
    | guardFail inp₂ _ hinp₂ _ => rfl

/-- **Effect Determinism**: the effect is unique.

    Non-overlapping guards are guaranteed structurally by
    `WellFormedBehaviour`, so no explicit hypothesis is needed. -/
theorem effectDeterminism
    (i : EngineSpec.EngIdx)
    (p : Engine i)
    (v : EngineSpec.MsgType i)
    (E₁ E₂ : Effect i)
    : EvalStep i p v E₁ →
      EvalStep i p v E₂ →
      E₁ = E₂
    := by
  intro h₁ h₂
  cases h₁ with
  | guardStrategy ga₁ _ _ hga₁mem hge₁ hall₁ =>
    cases h₂ with
    | guardStrategy ga₂ _ _ hga₂mem hge₂ hall₂ =>
      rcases Classical.em (ga₁ = ga₂) with heq | hne
      · subst heq; exact guardEvalStep_det hge₁ hge₂
      · -- ga₁ ≠ ga₂: hall₂ says ga₁ produces noop, so E₁ = noop by det.
        -- Similarly hall₁ says ga₂ produces noop, so E₂ = noop.
        have := guardEvalStep_det hge₁ (hall₂ ga₁ hga₁mem hne)
        have := guardEvalStep_det hge₂ (hall₁ ga₂ hga₂mem (fun h => hne h.symm))
        simp_all
    | allGuardsFail _ hall₂ =>
      -- ga₁ matched in h₁, but hall₂ says ga₁ produces noop → E₁ = noop.
      -- h₂ is allGuardsFail → E₂ = noop. So E₁ = E₂.
      exact guardEvalStep_det hge₁ (hall₂ ga₁ hga₁mem)
  | allGuardsFail _ hall₁ =>
    cases h₂ with
    | guardStrategy ga₂ _ _ hga₂mem hge₂ _ =>
      exact (guardEvalStep_det hge₂ (hall₁ ga₂ hga₂mem)).symm
    | allGuardsFail _ _ => rfl

end MailboxActors
