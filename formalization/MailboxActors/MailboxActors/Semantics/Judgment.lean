/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.State

/-!
# Judgment Forms

The five judgment forms of the operational semantics, each defined as an
inductive proposition.

1. `OpStep`        — system-level operations
2. `EvalStep`      — behaviour evaluation
3. `GuardEvalStep` — guarded action evaluation
4. `EffectEvalStep`— effect execution
5. `ProcessStep`   — engine processing coordination
-/

namespace MailboxActors

variable [EngineSpec]

-- ============================================================================
-- § Guarded Action Evaluation
-- ============================================================================

/-- `GuardEvalStep i p ga v E` :  in the context of engine `p` of type `i`,
    guarded action `ga` processing message `v` produces effect `E`.

    Rules: B-GuardedActionEval, B-NoMatchingGuard. -/
inductive GuardEvalStep (i : EngineSpec.EngIdx) :
    Engine i → GuardedAction i → EngineSpec.MsgType i → Effect i → Prop where
  /-- B-GuardedActionEval: guard matches, action fires. -/
  | guardMatch (p : Engine i) (ga : GuardedAction i) (v : EngineSpec.MsgType i)
      (inp : GuardInput i) (h : ga.guard inp = true) :
      p.status = EngineStatus.busy v →
      inp = ⟨v, p.config, p.env⟩ →
      GuardEvalStep i p ga v (ga.action inp h)
  /-- B-NoMatchingGuard: guard fails, produce `noop`. -/
  | guardFail (p : Engine i) (ga : GuardedAction i) (v : EngineSpec.MsgType i)
      (inp : GuardInput i) :
      p.status = EngineStatus.busy v →
      inp = ⟨v, p.config, p.env⟩ →
      ga.guard inp = false →
      GuardEvalStep i p ga v Effect.noop

-- ============================================================================
-- § Behaviour Evaluation
-- ============================================================================

/-- `EvalStep i p v E` : engine `p` of type `i`, processing message `v`,
    produces effect `E`.

    Rules: B-GuardStrategy, B-AllGuardsFail. -/
inductive EvalStep (i : EngineSpec.EngIdx) :
    Engine i → EngineSpec.MsgType i → Effect i → Prop where
  /-- B-GuardStrategy: exactly one guard matches. -/
  | guardStrategy (p : Engine i) (v : EngineSpec.MsgType i)
      (ga : GuardedAction i) (E : Effect i) :
      p.status = EngineStatus.busy v →
      ga ∈ p.behaviour.actions →
      GuardEvalStep i p ga v E →
      E ≠ Effect.noop →
      (∀ ga' ∈ p.behaviour.actions, ga' ≠ ga →
        GuardEvalStep i p ga' v Effect.noop) →
      EvalStep i p v E
  /-- B-AllGuardsFail: no guard matches, produce `noop`. -/
  | allGuardsFail (p : Engine i) (v : EngineSpec.MsgType i) :
      p.status = EngineStatus.busy v →
      (∀ ga ∈ p.behaviour.actions,
        GuardEvalStep i p ga v Effect.noop) →
      EvalStep i p v Effect.noop

-- ============================================================================
-- § Effect Execution
-- ============================================================================

/-- `EffectEvalStep κ E κ'` : executing effect `E` in state `κ` produces `κ'`.

    Rules: E-Send, E-Update, E-MFilter, E-Spawn, E-Chain, E-Terminate, E-Noop. -/
inductive EffectEvalStep :
    SystemState → (i : EngineSpec.EngIdx) → Effect i → SystemState → Prop where
  /-- E-Noop: no change. -/
  | noop (κ : SystemState) (i : EngineSpec.EngIdx) :
      EffectEvalStep κ i Effect.noop κ
  /-- E-Terminate: set engine status to `terminated`. -/
  | terminate (κ κ' : SystemState) (i : EngineSpec.EngIdx)
      (addr : Address) (p : Engine i) (v : EngineSpec.MsgType i) :
      κ.engineAt addr = some ⟨i, p⟩ →
      p.status = EngineStatus.busy v →
      EvalStep i p v Effect.terminate →
      κ' = κ.updateEngineAt addr ⟨i, { p with status := .terminated }⟩ →
      EffectEvalStep κ i Effect.terminate κ'
  /-- E-Update: replace engine environment. -/
  | update (κ κ' : SystemState) (i : EngineSpec.EngIdx)
      (addr : Address) (p : Engine i) (v : EngineSpec.MsgType i)
      (newEnv : EngineEnv i) :
      κ.engineAt addr = some ⟨i, p⟩ →
      EvalStep i p v (Effect.update newEnv) →
      κ' = κ.updateEngineAt addr ⟨i, { p with env := newEnv }⟩ →
      EffectEvalStep κ i (Effect.update newEnv) κ'
  /-- E-MFilter: transition engine to `ready` with new filter. -/
  | mfilter (κ κ' : SystemState) (i : EngineSpec.EngIdx)
      (addr : Address) (p : Engine i) (v : EngineSpec.MsgType i)
      (f : EngineSpec.MsgType i → Bool) :
      κ.engineAt addr = some ⟨i, p⟩ →
      EvalStep i p v (Effect.mfilter f) →
      κ' = κ → -- placeholder
      EffectEvalStep κ i (Effect.mfilter f) κ'
  /-- E-Chain: sequence two effects. -/
  | chain (κ κ' κ'' : SystemState) (i : EngineSpec.EngIdx)
      (e₁ e₂ : Effect i) :
      EffectEvalStep κ i e₁ κ' →
      EffectEvalStep κ' i e₂ κ'' →
      EffectEvalStep κ i (Effect.chain e₁ e₂) κ''

-- ============================================================================
-- § System-Level Operations
-- ============================================================================

/-- Labels for system-level operations. -/
inductive OpLabel where
  | node : OpLabel
  | spawn : OpLabel
  | spawnMbox : OpLabel
  | clean : OpLabel
  | send : OpLabel
  | enqueue : OpLabel
  | dequeue : OpLabel
  | process : OpLabel
  deriving DecidableEq, Repr

/-- `OpStep κ op κ'` : operation `op` transforms `κ` into `κ'`.

    This combines all system-level, message-passing, and processing rules. -/
inductive OpStep : SystemState → OpLabel → SystemState → Prop where
  /-- S-Node: create a new node. -/
  | sNode (κ κ' : SystemState) (newId : Nat) :
      κ.nextId = newId →
      κ' = { κ with
        nodes := κ.nodes ++ [{ id := newId, engines := [] : Node }],
        nextId := newId + 1 } →
      OpStep κ OpLabel.node κ'
  /-- S-Clean: remove a terminated engine. -/
  | sClean (κ κ' : SystemState) (nodeIdx : Nat) (addr : Address)
      (se : SomeEngine) :
      κ.engineAt addr = some se →
      (∃ _ : se.idx = se.idx, se.engine.status = EngineStatus.terminated) →
      κ' = κ → -- placeholder: remove engine from node's engine map
      OpStep κ OpLabel.clean κ'
  /-- M-Send: place a message in transit to the target's mailbox. -/
  | mSend (κ κ' : SystemState) (sender target : Address)
      (i : EngineSpec.EngIdx) (v : EngineSpec.MsgType i)
      (senderEng targetEng : SomeEngine) :
      κ.engineAt sender = some senderEng →
      κ.engineAt target = some targetEng →
      targetEng.engine.mode = EngineMode.process →
      targetEng.idx = i →
      κ' = { κ with
        messages := κ.messages ++ [⟨sender, κ.mailboxOf target, ⟨i, v⟩⟩] } →
      OpStep κ OpLabel.send κ'
  /-- M-Enqueue: deliver a message to a ready mailbox engine.
      The message `m` is removed from `κ.messages`. -/
  | mEnqueue (κ κ' : SystemState) (m : Message) (mboxEng : SomeEngine)
      (pre post : List Message) :
      κ.messages = pre ++ m :: post →
      κ.engineAt m.target = some mboxEng →
      mboxEng.engine.mode = EngineMode.mail →
      κ' = { κ with messages := pre ++ post } →
      OpStep κ OpLabel.enqueue κ'
  /-- M-Dequeue: transfer a message from mailbox to processing engine. -/
  | mDequeue (κ κ' : SystemState) (procAddr : Address)
      (procEng mboxEng : SomeEngine) :
      κ.engineAt procAddr = some procEng →
      procEng.engine.mode = EngineMode.process →
      κ.engineAt (κ.mailboxOf procAddr) = some mboxEng →
      -- processing engine is ready, mailbox has matching message
      κ' = κ → -- placeholder: transition proc to Busy(v), update mailbox
      OpStep κ OpLabel.dequeue κ'

-- ============================================================================
-- § Engine Processing
-- ============================================================================

/-- `ProcessStep κ addr i v κ'` : engine at `addr` of type `i` processes
    message `v`, yielding new state `κ'`. -/
inductive ProcessStep :
    SystemState → Address → (i : EngineSpec.EngIdx) →
    EngineSpec.MsgType i → SystemState → Prop where
  | process (κ κ' κ'' : SystemState) (addr : Address)
      (i : EngineSpec.EngIdx) (p : Engine i) (v : EngineSpec.MsgType i)
      (E : Effect i) :
      κ.engineAt addr = some ⟨i, p⟩ →
      p.status = EngineStatus.busy v →
      EvalStep i p v E →
      EffectEvalStep κ i E κ' →
      -- κ'' is κ' with engine status updated:
      --   if still Busy → Ready(λ_.tt)
      --   otherwise preserve (MFilter or Terminated already changed it)
      κ'' = κ' → -- placeholder
      ProcessStep κ addr i v κ''

-- ============================================================================
-- § System Step  (top-level reduction)
-- ============================================================================

/-- A single system step: there exists some operation that transforms the state. -/
def SysStep (κ κ' : SystemState) : Prop :=
  ∃ op, OpStep κ op κ'

end MailboxActors
