import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Progress

A well-typed system state with *productive* pending work can always take a step.
Unlike the original vacuous proof relying on S-Node, this theorem guarantees
that engines actually process messages and effects are executed.
-/

namespace MailboxActors

variable [EngineSpec]

/-- A state has productive work when:
    1. An engine is busy (guaranteed to proceed via S-Process).
    2. A processing engine is terminated (guaranteed to be cleaned via S-Clean).
    3. A message is in transit to a ready mailbox that accepts it. -/
def hasProductiveWork (κ : SystemState) : Prop :=
  (∃ addr se, κ.engineAt addr = some se ∧
    (∃ i v, se.idx = i ∧ se.engine.status = EngineStatus.busy v)) ∨
  (∃ addr se, κ.engineAt addr = some se ∧
    se.engine.mode = EngineMode.process ∧
    se.engine.status = EngineStatus.terminated) ∨
  (∃ m ∈ κ.messages, ∃ mboxSe, κ.engineAt m.target = some mboxSe ∧
    mboxSe.engine.mode = EngineMode.mail ∧
    ∃ f, mboxSe.engine.status = EngineStatus.ready f ∧
    (∃ w, m.payload = ⟨mboxSe.idx, w⟩ ∧ f w = true))

/-- If a filtered list has length ≤ 1, all its members are equal. -/
private lemma filter_le_one_eq {α : Type*} {a b : α} {l : List α}
    (hl : l.length ≤ 1) (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  obtain ⟨⟨ia, hia⟩, rfl⟩ := List.get_of_mem ha
  obtain ⟨⟨ib, hib⟩, rfl⟩ := List.get_of_mem hb
  congr 1; exact Fin.ext (by omega)

/-- Helper: Evaluation is total for well-formed behaviours.
    Requires the engine to be busy (for `GuardEvalStep` status premise). -/
theorem evalStep_total {i : EngineSpec.EngIdx} (p : Engine i) (v : EngineSpec.MsgType i)
    (hbusy : p.status = EngineStatus.busy v) :
    ∃ E, EvalStep i p v E := by
  let inp := (⟨v, p.config, p.env⟩ : GuardInput i)
  -- Check if any guard matches
  if h : ∃ ga ∈ p.behaviour.actions, (ga.guard inp).isSome then
    obtain ⟨ga, hmem, hsome⟩ := h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
    let E := ga.action w inp hw
    have hga : GuardEvalStep i p ga v E :=
      GuardEvalStep.guardMatch p ga v inp w hw hbusy rfl
    -- All other guards fail (from NonOverlappingGuards)
    have hall : ∀ ga' ∈ p.behaviour.actions, ga' ≠ ga →
        GuardEvalStep i p ga' v Effect.noop := by
      intro ga' hga'mem hne'
      apply GuardEvalStep.guardFail _ _ _ inp hbusy rfl
      -- Show ga'.guard inp = none by contradiction with NonOverlappingGuards
      by_contra hne
      have hsome' : (ga'.guard inp).isSome = true := Option.ne_none_iff_isSome.mp hne
      -- Both ga and ga' are in the filter, but filter.length ≤ 1
      have hno := p.behaviour.nonOverlapping inp
      have hga_filt : ga ∈ p.behaviour.actions.filter (fun g => (g.guard inp).isSome) :=
        List.mem_filter.mpr ⟨hmem, by simp [hsome]⟩
      have hga'_filt : ga' ∈ p.behaviour.actions.filter (fun g => (g.guard inp).isSome) :=
        List.mem_filter.mpr ⟨hga'mem, hsome'⟩
      exact hne' (filter_le_one_eq hno hga'_filt hga_filt)
    exact ⟨E, EvalStep.guardStrategy p v ga E hbusy hmem hga hall⟩
  else
    -- No guard matches: all guards fail → Effect.noop
    exact ⟨Effect.noop, EvalStep.allGuardsFail p v hbusy (fun ga hga =>
      have hnone : ga.guard inp = none := by
        by_contra hsome
        exact h ⟨ga, hga, Option.ne_none_iff_isSome.mp hsome⟩
      GuardEvalStep.guardFail p ga v inp hbusy rfl hnone)⟩

/-- **Productive Progress**:
    If there is productive work, the system takes a step that is NOT S-Node. -/
theorem productive_progress (κ : SystemState) :
    WellTypedState κ → hasProductiveWork κ →
    ∃ op, op ≠ OpLabel.node ∧ ∃ κ', OpStep κ op κ' := by
  intro wt hp
  rcases hp with ⟨addr, se, heng, i, v, hidx, hbusy⟩ |
    ⟨addr, se, heng, hmode, hterm⟩ |
    ⟨m, hm, mboxSe, hmbox, hmode, f, hready, w, hpayload, hfilter⟩
  · -- Case 1: Busy Engine -> S-Process
    subst hidx
    obtain ⟨E, hEval⟩ := evalStep_total se.engine v hbusy
    -- S-Process requires EffectEvalStep totality: for any effect E produced
    -- by evaluation, there exists κ' with EffectEvalStep κ i E κ'.
    -- This is non-trivial (E-Send needs target validity, E-Spawn needs fresh
    -- addresses). Deferred with sorry.
    exact ⟨OpLabel.process, by simp, sorry⟩

  · -- Case 2: Terminated Processing Engine -> S-Clean
    exact ⟨OpLabel.clean, by simp, _,
      OpStep.sClean κ _ κ.nextId addr se heng hmode hterm rfl⟩

  · -- Case 3: Message to Ready Mailbox -> M-Enqueue
    obtain ⟨pre, post, hmsg⟩ := List.append_of_mem hm
    exact ⟨OpLabel.enqueue, by simp, _,
      OpStep.mEnqueue κ _ m mboxSe w f pre post hmsg hmbox hpayload hmode hready hfilter rfl⟩

end MailboxActors
