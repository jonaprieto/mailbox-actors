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
      (inp : GuardInput i) (w : ga.Witness) (h : ga.guard inp = some w) :
      p.status = EngineStatus.busy v →
      inp = ⟨v, p.config, p.env⟩ →
      GuardEvalStep i p ga v (ga.action w inp h)
  /-- B-NoMatchingGuard: guard fails, produce `noop`. -/
  | guardFail (p : Engine i) (ga : GuardedAction i) (v : EngineSpec.MsgType i)
      (inp : GuardInput i) :
      p.status = EngineStatus.busy v →
      inp = ⟨v, p.config, p.env⟩ →
      ga.guard inp = none →
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
  /-- E-Send: place a message in transit.
      Target validity premises ensure preservation can show the new message
      is well-typed (target has a mailbox with matching type index). -/
  | send (κ κ' : SystemState) (i : EngineSpec.EngIdx)
      (addr : Address) (p : Engine i) (v : EngineSpec.MsgType i)
      (j : EngineSpec.EngIdx) (target : Address) (payload : EngineSpec.MsgType j)
      (targetEng : SomeEngine) :
      κ.engineAt addr = some ⟨i, p⟩ →
      κ.engineAt target = some targetEng →
      targetEng.engine.mode = EngineMode.process →
      targetEng.idx = j →
      κ' = { κ with messages := κ.messages ++ [⟨addr, κ.mailboxOf target, ⟨j, payload⟩⟩] } →
      EffectEvalStep κ i (Effect.send j target payload) κ'
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
      κ' = κ.updateEngineAt addr ⟨i, { p with status := .ready f }⟩ →
      EffectEvalStep κ i (Effect.mfilter f) κ'
  /-- E-Spawn: executing a `spawn` effect creates a child engine via
      S-SpawnWithMailbox, ensuring it is paired with a mailbox engine. -/
  | spawn (κ κ' : SystemState) (i : EngineSpec.EngIdx)
      (j : EngineSpec.EngIdx) (cfg : EngineSpec.CfgData j)
      (env : EngineSpec.LocalState j)
      (nodeId : Nat) (procSe mboxSe : SomeEngine)
      (procAddr mboxAddr : Address) :
      (∃ n ∈ κ.nodes, n.id = nodeId) →
      procAddr = ⟨nodeId, κ.nextId⟩ →
      mboxAddr = κ.mailboxOf procAddr →
      procSe.idx = j →
      mboxSe.idx = j →
      procSe.engine.mode = EngineMode.process →
      mboxSe.engine.mode = EngineMode.mail →
      κ.engineAt procAddr = none →
      κ.engineAt mboxAddr = none →
      κ' = { (κ.addEngineAt procAddr procSe).addEngineAt mboxAddr mboxSe
             with nextId := κ.nextId + 2 } →
      EffectEvalStep κ i (Effect.spawn j cfg env) κ'
  /-- E-Chain: sequence two effects. -/
  | chain (κ κ' κ'' : SystemState) (i : EngineSpec.EngIdx)
      (e₁ e₂ : Effect i) :
      EffectEvalStep κ i e₁ κ' →
      EffectEvalStep κ' i e₂ κ'' →
      EffectEvalStep κ i (Effect.chain e₁ e₂) κ''

-- ============================================================================
-- § Post-Processing Status Resolution
-- ============================================================================

/-- Post-processing status resolution: if the effect left the engine `busy`,
    reset to `ready(λ_.true)`; otherwise preserve the status set by the effect
    (e.g. `terminated` from E-Terminate, `ready(f)` from E-MFilter). -/
def resolvePostStatus {i : EngineSpec.EngIdx} (s : EngineStatus i) : EngineStatus i :=
  match s with
  | .busy _ => .ready (fun _ => true)
  | other => other

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
  /-- S-Clean: remove a terminated processing engine.  The mailbox persists
      to absorb in-transit messages (Remark 4.4 in the paper). -/
  | sClean (κ κ' : SystemState) (nodeIdx : Nat) (addr : Address)
      (se : SomeEngine) :
      κ.engineAt addr = some se →
      se.engine.mode = EngineMode.process →
      se.engine.status = EngineStatus.terminated →
      κ' = κ.removeEngineAt addr →
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
  /-- M-Enqueue: deliver an in-transit message to a ready mailbox engine.
      The mailbox transitions from `ready(f)` to `busy(w)` and the message
      `m` is removed from `κ.messages`. -/
  | mEnqueue (κ κ' : SystemState) (m : Message) (mboxEng : SomeEngine)
      (w : EngineSpec.MsgType mboxEng.idx)
      (f : EngineSpec.MsgType mboxEng.idx → Bool)
      (pre post : List Message) :
      κ.messages = pre ++ m :: post →
      κ.engineAt m.target = some mboxEng →
      m.payload = ⟨mboxEng.idx, w⟩ →
      mboxEng.engine.mode = EngineMode.mail →
      mboxEng.engine.status = EngineStatus.ready f →
      f w = true →
      κ' = { κ.updateEngineAt m.target
               ⟨mboxEng.idx, { mboxEng.engine with status := .busy w }⟩
             with messages := pre ++ post } →
      OpStep κ OpLabel.enqueue κ'
  /-- S-SpawnWithMailbox: spawn a processing engine paired with its
      dedicated mailbox engine on an existing node. -/
  | sSpawnMbox (κ κ' : SystemState) (nodeId : Nat)
      (k : EngineSpec.EngIdx)
      (procSe mboxSe : SomeEngine)
      (procAddr mboxAddr : Address) :
      (∃ n ∈ κ.nodes, n.id = nodeId) →
      procAddr = ⟨nodeId, κ.nextId⟩ →
      mboxAddr = κ.mailboxOf procAddr →
      procSe.idx = k →
      mboxSe.idx = k →
      procSe.engine.mode = EngineMode.process →
      mboxSe.engine.mode = EngineMode.mail →
      κ.engineAt procAddr = none →
      κ.engineAt mboxAddr = none →
      κ' = { (κ.addEngineAt procAddr procSe).addEngineAt mboxAddr mboxSe
             with nextId := κ.nextId + 2 } →
      OpStep κ OpLabel.spawnMbox κ'
  /-- M-Dequeue: transfer a message from mailbox to processing engine.
      The processing engine transitions from `ready(f)` to `busy(v)` where
      `f v = true`, and the mailbox engine's environment is updated. -/
  | mDequeue (κ κ' : SystemState) (procAddr : Address)
      (i : EngineSpec.EngIdx) (procEng : Engine i)
      (mboxEng : SomeEngine)
      (w : EngineSpec.MsgType mboxEng.idx)
      (v : EngineSpec.MsgType i) (f : EngineSpec.MsgType i → Bool)
      (mboxEnv : EngineEnv mboxEng.idx)
      (newMboxEnv : EngineEnv mboxEng.idx) :
      κ.engineAt procAddr = some ⟨i, procEng⟩ →
      procEng.mode = EngineMode.process →
      procEng.status = EngineStatus.ready f →
      κ.engineAt (κ.mailboxOf procAddr) = some mboxEng →
      mboxEng.engine.env = mboxEnv →
      EngineSpec.mailboxContains mboxEnv.localState w →
      EngineSpec.unwrap w = some v →
      newMboxEnv = { mboxEnv with localState := EngineSpec.mailboxRemove mboxEnv.localState w } →
      f v = true →
      κ' = SystemState.updateEngineAt
              (κ.updateEngineAt procAddr ⟨i, { procEng with status := .busy v }⟩)
              (κ.mailboxOf procAddr)
              ⟨mboxEng.idx, { mboxEng.engine with env := newMboxEnv }⟩ →
      OpStep κ OpLabel.dequeue κ'
  /-- S-Process: engine processing — a busy engine evaluates its behaviour,
      executes the resulting effect, and resolves post-processing status. -/
  | sProcess (κ κ' κ'' : SystemState) (addr : Address)
      (i : EngineSpec.EngIdx) (p : Engine i) (v : EngineSpec.MsgType i)
      (E : Effect i) :
      κ.engineAt addr = some ⟨i, p⟩ →
      p.status = EngineStatus.busy v →
      EvalStep i p v E →
      EffectEvalStep κ i E κ' →
      (∃ (p' : Engine i),
        κ'.engineAt addr = some ⟨i, p'⟩ ∧
        κ'' = κ'.updateEngineAt addr
          ⟨i, { p' with status := resolvePostStatus p'.status }⟩) →
      OpStep κ OpLabel.process κ''

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
      -- κ'' is κ' with engine status resolved:
      --   if still Busy → Ready(λ_.tt)
      --   otherwise preserve (MFilter or Terminated already changed it)
      (∃ (p' : Engine i),
        κ'.engineAt addr = some ⟨i, p'⟩ ∧
        κ'' = κ'.updateEngineAt addr
          ⟨i, { p' with status := resolvePostStatus p'.status }⟩) →
      ProcessStep κ addr i v κ''

-- ============================================================================
-- § System Step  (top-level reduction)
-- ============================================================================

/-- A single system step: there exists some operation that transforms the state. -/
def SysStep (κ κ' : SystemState) : Prop :=
  ∃ op, OpStep κ op κ'

end MailboxActors
