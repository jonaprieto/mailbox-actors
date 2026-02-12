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

/-- **Effect Determinism**: under non-overlapping guards, the effect is unique.
    Paper Proposition 3. -/
theorem effectDeterminism (i : EngineSpec.EngIdx)
    (p : Engine i) (v : EngineSpec.MsgType i) (E₁ E₂ : Effect i) :
    NonOverlappingGuards p.behaviour →
    EvalStep i p v E₁ →
    EvalStep i p v E₂ →
    E₁ = E₂ := by
  sorry

end MailboxActors
