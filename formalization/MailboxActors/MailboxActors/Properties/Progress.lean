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

/-- Helper: Evaluation is total for well-formed behaviours.
    Requires the engine to be busy (for `GuardEvalStep` status premise). -/
theorem evalStep_total {i : EngineSpec.EngIdx} (p : Engine i) (v : EngineSpec.MsgType i)
    (hbusy : p.status = EngineStatus.busy v) :
    ∃ E, EvalStep i p v E := by
  let actions := p.behaviour.actions
  -- Check if any guard matches
  if h : ∃ ga ∈ actions, (ga.guard ⟨v, p.config, p.env⟩).isSome then
    obtain ⟨ga, hmem, hsome⟩ := h
    have : ∃ w, ga.guard ⟨v, p.config, p.env⟩ = some w := Option.isSome_iff_exists.mp hsome
    obtain ⟨w, hw⟩ := this
    -- Use guardMatch to construct the effect
    let E := ga.action w ⟨v, p.config, p.env⟩ hw
    -- The guard evaluation step
    have hga : GuardEvalStep i p ga v E :=
      GuardEvalStep.guardMatch p ga v ⟨v, p.config, p.env⟩ w hw hbusy rfl
    -- Constructing the full EvalStep requires proving uniqueness (from
    -- NonOverlappingGuards) and E ≠ noop (or removing that constraint).
    -- This is deferred — see plan notes on E ≠ noop gap.
    exact ⟨E, sorry⟩
  else
    -- No guard matches: all guards fail → Effect.noop
    exact ⟨Effect.noop, EvalStep.allGuardsFail p v hbusy (fun ga hga =>
      have hnone : ga.guard ⟨v, p.config, p.env⟩ = none := by
        by_contra hsome
        exact h ⟨ga, hga, Option.ne_none_iff_isSome.mp hsome⟩
      GuardEvalStep.guardFail p ga v ⟨v, p.config, p.env⟩ hbusy rfl hnone)⟩

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
    -- S-Process requires EffectEvalStep totality (E-Noop, E-Send, etc.)
    -- which is non-trivial. Deferred with sorry.
    exact ⟨OpLabel.process, by simp, sorry⟩

  · -- Case 2: Terminated Processing Engine -> S-Clean
    exact ⟨OpLabel.clean, by simp, _,
      OpStep.sClean κ _ κ.nextId addr se heng hmode hterm rfl⟩

  · -- Case 3: Message to Ready Mailbox -> M-Enqueue
    obtain ⟨pre, post, hmsg⟩ := List.append_of_mem hm
    exact ⟨OpLabel.enqueue, by simp, _,
      OpStep.mEnqueue κ _ m mboxSe w f pre post hmsg hmbox hpayload hmode hready hfilter rfl⟩

end MailboxActors
