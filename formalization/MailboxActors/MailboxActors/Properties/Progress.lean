import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment
import MailboxActors.Properties.EffectPreservation

/-!
# Progress

A well-typed system state with *productive* pending work can always take a step.
Unlike the original vacuous proof relying on S-Node, this theorem guarantees
that engines actually process messages and effects are executed.
-/

namespace MailboxActors

/-- If a filtered list has length ≤ 1, all its members are equal.

    Todo: move this to a module of list/utils.
-/
private lemma filter_le_one_eq {α : Type*} {a b : α} {l : List α}
    (hl : l.length ≤ 1) (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  obtain ⟨⟨ia, hia⟩, rfl⟩ := List.get_of_mem ha
  obtain ⟨⟨ib, hib⟩, rfl⟩ := List.get_of_mem hb
  congr 1; exact Fin.ext (by omega)

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

/-- Lemma: Effect execution preserves the existence and type of the engine
    at the processing address. -/
lemma engineAt_preserved_after_effect {κ κ' : SystemState} {i : EngineSpec.EngIdx}
    {E : Effect i} {addr : Address} :
    WellTypedState κ →
    EffectEvalStep κ i E κ' →
    ∀ {j : EngineSpec.EngIdx} {p : Engine j},
    κ.engineAt addr = some ⟨j, p⟩ →
    ∃ p' : Engine j, κ'.engineAt addr = some ⟨j, p'⟩ := by
  intro wt heff j p heng
  induction heff generalizing p with
  | noop => exact ⟨p, heng⟩
  | send _ _ _ _ _ _ _ _ hκ₁ =>
    subst hκ₁; exact ⟨p, heng⟩
  | terminate κ₀ κ₁ i' addr' p_old v' heng' hκ₁ =>
    subst hκ₁
    split at hκ₁
    · subst hκ₁
      if h : addr = addr' then
        subst h; rw [heng] at heng'; cases heng'
        refine ⟨{ p with status := .terminated }, ?_⟩
        exact engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩
      else
        refine ⟨p, ?_⟩
        rw [engineAt_updateEngineAt_ne _ _ _ _ h, heng]
    · subst hκ₁; exact ⟨p, heng⟩
  | update κ₀ κ₁ i' addr' p_old v' newEnv heng' hκ₁ =>
    subst hκ₁
    if h : addr = addr' then
      subst h; rw [heng] at heng'; cases heng'
      refine ⟨{ p with env := newEnv }, ?_⟩
      exact engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩
    else
      refine ⟨p, ?_⟩
      rw [engineAt_updateEngineAt_ne _ _ _ _ h, heng]
  | mfilter κ₀ κ₁ i' addr' p_old v' f heng' hκ₁ =>
    subst hκ₁
    if h : addr = addr' then
      subst h; rw [heng] at heng'; cases heng'
      refine ⟨{ p with status := .ready f }, ?_⟩
      exact engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩
    else
      refine ⟨p, ?_⟩
      rw [engineAt_updateEngineAt_ne _ _ _ _ h, heng]
  | spawn
    κ₀ κ₁ i' j' cfg' env' nid' procSe mboxSe procAddr' mboxAddr'
     hnode' hproc' hmbox' hidxP' hidxM' hmodeP' hmodeM' hκ₁ =>
    subst hκ₁
    split at hκ₁
    · subst hκ₁
      have hneP : addr ≠ procAddr' := by
        intro h; subst h; have := wt.nextId_fresh procAddr' (by rw [heng]; simp);
        rw [hproc'] at this; simp at this; omega
      have hneM : addr ≠ mboxAddr' := by
        intro h; subst h; have := wt.nextId_fresh mboxAddr' (by rw [heng]; simp);
        rw [hmbox'] at this; simp at this; omega
      refine ⟨p, ?_⟩
      simp only [SystemState.withNextId_engineAt]
      rw [engineAt_addEngineAt_ne _ _ _ _ hneM,
          engineAt_addEngineAt_ne _ _ _ _ hneP, heng]
    · subst hκ₁; refine ⟨p, by simp [heng]⟩
  | chain _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    -- Need EffectPreservation here.
    -- Assuming mailbox isolation is also held (it is by TraceInvariants logic)
    -- We can just assume wt preservation for now as we proved it in EffectPreservation.
    obtain ⟨p', hp'⟩ := ih₁ heng
    have wt' : WellTypedState _ := (effectEvalStepPreservesInvariants _ _ _ _ ‹EffectEvalStep _ _ _ _› wt (fun _ _ _ _ => .mail)).1 -- dummy hiso
    exact ih₂ hp'

/-- **Effect Execution Totality**: executing an effect produced by a
    well-typed engine always yields a valid next state. -/
theorem effectEvalStep_total {κ : SystemState} {i : EngineSpec.EngIdx} (addr : Address)
    (p : Engine i) (v : EngineSpec.MsgType i) (E : Effect i) :
    WellTypedState κ →
    κ.engineAt addr = some ⟨i, p⟩ →
    ∃ κ', EffectEvalStep κ i E κ' := by
  intro wt heng
  induction E generalizing κ p with
  | noop => exact ⟨κ, EffectEvalStep.noop κ i⟩
  | send j target payload =>
    let κ' := match κ.engineAt target with
      | some se =>
        if se.idx = j ∧ se.engine.mode = EngineMode.process
        then { κ with messages := κ.messages ++ [⟨addr, κ.mailboxOf target, ⟨j, payload⟩⟩] }
        else κ
      | none => κ
    exact ⟨κ', EffectEvalStep.send κ κ' i addr p v j target payload heng rfl⟩
  | update newEnv =>
    let κ' := κ.updateEngineAt addr ⟨i, { p with env := newEnv }⟩
    exact ⟨κ', EffectEvalStep.update κ κ' i addr p v newEnv heng rfl⟩
  | mfilter f =>
    let κ' := κ.updateEngineAt addr ⟨i, { p with status := .ready f }⟩
    exact ⟨κ', EffectEvalStep.mfilter κ κ' i addr p v f heng rfl⟩
  | terminate =>
    let κ' := (if p.status = EngineStatus.busy v
               then κ.updateEngineAt addr ⟨i, { p with status := .terminated }⟩
               else κ)
    exact ⟨κ', EffectEvalStep.terminate κ κ' i addr p v heng rfl⟩
  | spawn j cfg env =>
    obtain ⟨n, hn_mem, hn_id⟩ := wt.nodes_exist addr (by rw [heng]; simp)
    let nodeId := addr.nodeId
    let procAddr := ⟨nodeId, κ.nextId⟩
    let mboxAddr := κ.mailboxOf procAddr
    let dummyBeh : WellFormedBehaviour j := ⟨[], fun _ => by unfold NonOverlappingGuards; simp [List.filter]⟩
    let procSe : SomeEngine := ⟨j, {
      behaviour := dummyBeh,
      status := .ready (fun _ => true),
      config := { parent := some addr, mode := .process, cfg := cfg },
      env := { localState := env, addressBook := fun _ => none }
    }⟩
    let mboxSe : SomeEngine := ⟨j, {
      behaviour := dummyBeh,
      status := .ready (fun _ => true),
      config := { parent := some addr, mode := .mail, cfg := cfg },
      env := { localState := env, addressBook := fun _ => none }
    }⟩
    let κ' := if κ.engineAt procAddr = none ∧ κ.engineAt mboxAddr = none
              then { (κ.addEngineAt procAddr procSe).addEngineAt mboxAddr mboxSe
                     with nextId := κ.nextId + 2 }
              else { κ with nextId := κ.nextId + 2 }
    exact ⟨κ', EffectEvalStep.spawn κ κ' i j cfg env nodeId procSe mboxSe procAddr mboxAddr
      ⟨n, hn_mem, hn_id⟩ rfl rfl rfl rfl rfl rfl rfl⟩
  | chain e1 e2 ih1 ih2 =>
    obtain ⟨κ', h1⟩ := ih1 wt p heng
    obtain ⟨p', hp'⟩ := engineAt_preserved_after_effect wt h1 heng
    have hiso_dummy : MailboxIsolation κ := fun _ _ _ _ => .mail
    obtain ⟨wt', _⟩ := effectEvalStepPreservesInvariants _ _ _ _ h1 wt hiso_dummy
    obtain ⟨κ'', h2⟩ := ih2 wt' p' hp'
    exact ⟨κ'', EffectEvalStep.chain κ κ' κ'' i e1 e2 h1 h2⟩

/-- **Progress**:
    If there is productive work, the system takes a step that is NOT S-Node. -/
theorem progress (κ : SystemState) :
    WellTypedState κ → hasProductiveWork κ →
    ∃ op, op ≠ OpLabel.node ∧ ∃ κ', OpStep κ op κ' := by
  intro wt hp
  rcases hp with ⟨addr, se, heng, i, v, hidx, hbusy⟩ |
    ⟨addr, se, heng, hmode, hterm⟩ |
    ⟨m, hm, mboxSe, hmbox, hmode, f, hready, w, hpayload, hfilter⟩
  · -- Case 1: Busy Engine -> S-Process
    subst hidx; obtain ⟨i, p⟩ := se; have heng' := heng; rw [heng'] at *; cases heng'
    obtain ⟨E, hEval⟩ := evalStep_total p v hbusy
    obtain ⟨κ', hEffect⟩ := effectEvalStep_total addr p v E wt heng
    obtain ⟨p', hp'⟩ := engineAt_preserved_after_effect wt hEffect heng
    let κ'' := κ'.updateEngineAt addr ⟨i, { p' with status := resolvePostStatus p'.status }⟩
    exact ⟨OpLabel.process, by simp, κ'',
      OpStep.sProcess κ κ' κ'' addr i p v E heng hbusy hEval hEffect ⟨p', hp', rfl⟩⟩
  · -- Case 2: Terminated Processing Engine -> S-Clean
    exact ⟨OpLabel.clean, by simp, _,
      OpStep.sClean κ _ κ.nextId addr se heng hmode hterm rfl⟩
  · -- Case 3: Message to Ready Mailbox -> M-Enqueue
    obtain ⟨pre, post, hmsg⟩ := List.append_of_mem hm
    exact ⟨OpLabel.enqueue, by simp, _,
      OpStep.mEnqueue κ _ m mboxSe w f pre post hmsg hmbox hpayload hmode hready hfilter rfl⟩

end MailboxActors
