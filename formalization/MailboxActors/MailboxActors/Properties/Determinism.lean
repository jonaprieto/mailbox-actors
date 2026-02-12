/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Engine.Behaviour
import MailboxActors.Semantics.Judgment

/-!
# Effect Determinism

Under non-overlapping guards, behaviour evaluation is deterministic.
Paper Proposition 3.
-/

namespace MailboxActors

variable [EngineSpec]

/-- Guard evaluation is deterministic: for a given engine, guarded action,
    and message, the effect is uniquely determined by the guard function. -/
private lemma guardEvalStep_det {i : EngineSpec.EngIdx} {p : Engine i}
    {ga : GuardedAction i} {v : EngineSpec.MsgType i} {E₁ E₂ : Effect i}
    (h₁ : GuardEvalStep i p ga v E₁) (h₂ : GuardEvalStep i p ga v E₂) : E₁ = E₂ := by
  cases h₁ with
  | guardMatch inp₁ _ hinp₁ hg₁ =>
    subst hinp₁
    cases h₂ with
    | guardMatch inp₂ _ hinp₂ _ => subst hinp₂; rfl
    | guardFail inp₂ _ hinp₂ hg₂ => subst hinp₂; simp_all
  | guardFail inp₁ _ hinp₁ hg₁ =>
    subst hinp₁
    cases h₂ with
    | guardMatch inp₂ _ hinp₂ hg₂ => subst hinp₂; simp_all
    | guardFail inp₂ _ hinp₂ _ => rfl

/-- **Effect Determinism**: under non-overlapping guards, the effect is unique.
    Paper Proposition 3. -/
theorem effectDeterminism (i : EngineSpec.EngIdx)
    (p : Engine i) (v : EngineSpec.MsgType i) (E₁ E₂ : Effect i) :
    NonOverlappingGuards p.behaviour →
    EvalStep i p v E₁ →
    EvalStep i p v E₂ →
    E₁ = E₂ := by
  intro _ h₁ h₂
  cases h₁ with
  | guardStrategy ga₁ _ _ hga₁mem hge₁ hne₁ hall₁ =>
    cases h₂ with
    | guardStrategy ga₂ _ _ hga₂mem hge₂ hne₂ hall₂ =>
      rcases Classical.em (ga₁ = ga₂) with heq | hne
      · subst heq; exact guardEvalStep_det hge₁ hge₂
      · exact absurd (guardEvalStep_det hge₂ (hall₁ ga₂ hga₂mem (Ne.symm hne))) hne₂
    | allGuardsFail _ hall₂ =>
      exact absurd (guardEvalStep_det hge₁ (hall₂ ga₁ hga₁mem)) hne₁
  | allGuardsFail _ hall₁ =>
    cases h₂ with
    | guardStrategy ga₂ _ _ hga₂mem hge₂ hne₂ _ =>
      exact absurd (guardEvalStep_det hge₂ (hall₁ ga₂ hga₂mem)) hne₂
    | allGuardsFail _ _ => rfl

end MailboxActors
