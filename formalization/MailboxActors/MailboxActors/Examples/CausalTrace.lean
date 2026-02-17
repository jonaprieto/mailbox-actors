import MailboxActors.Examples.CausalMailbox
import MailboxActors.Properties.TypePreservation

/-!
# Causal Trace Consistency

Proof that the CausalInvariant is preserved globally across system execution.
-/

namespace MailboxActors.Examples.CausalMailbox

-- Use the concrete PubSubSpec instance
open PubSubSpec

/-- The global causal invariant:
    For every broker in the system, its local state satisfies CausalInvariant. -/
def GlobalCausalInvariant (κ : SystemState) : Prop :=
  ∀ addr se, κ.engineAt addr = some se →
    ∀ (h : se.idx = PubSubIdx.broker),
    -- Cast localState to CausalState using the type equality
    let s : CausalState := cast (by rw [h]; rfl) se.engine.env.localState
    CausalInvariant s

/-- CausalInvariant is preserved when removing a message from ready:
    fewer messages to check, delivered set unchanged. -/
private lemma causalInvariant_erase (s : CausalState) (w : TopicMsg) :
    CausalInvariant s → CausalInvariant { s with ready := s.ready.erase w } := by
  intro hinv msg hmem
  exact hinv msg (List.mem_of_mem_erase hmem)

/-- mailboxRemove preserves CausalInvariant: removing a message from a broker's
    ready list preserves the invariant. Taking `idx` as a free variable lets
    `subst` eliminate it so the cast and mailboxRemove both reduce. -/
private lemma mailboxRemove_preserves_causalInvariant
    {idx : EngineSpec.EngIdx} {localState : EngineSpec.LocalState idx}
    {w : EngineSpec.MsgType idx}
    (hidx : idx = PubSubIdx.broker)
    (hinv : CausalInvariant (cast (by rw [hidx]; rfl) localState)) :
    CausalInvariant (cast (by rw [hidx]; rfl)
      (EngineSpec.mailboxRemove localState w)) := by
  subst hidx
  exact causalInvariant_erase _ _ hinv

theorem causal_invariant_preserved (κ κ' : SystemState) (op : OpLabel) :
    WellTypedState κ →
    GlobalCausalInvariant κ →
    -- Broker-safety for the transition: every broker engine in κ' that was
    -- not identically present in κ satisfies CausalInvariant.
    -- In the PubSub system this is discharged by:
    --   (a) freshly spawned brokers start with CausalState.empty, and
    --   (b) causalAction preserves the invariant.
    (∀ addr' se', κ'.engineAt addr' = some se' → κ.engineAt addr' ≠ some se' →
      ∀ (h : se'.idx = PubSubIdx.broker),
      CausalInvariant (cast (by rw [h]; rfl) se'.engine.env.localState)) →
    OpStep κ op κ' →
    GlobalCausalInvariant κ' := by
  intro wt inv hbt step addr' se' heng' hidx'
  cases step with
  -- ── S-Node: new empty node, no engine changes ────────────────────────
  | sNode =>
    subst_vars
    rw [engineAt_append_emptyNode] at heng'
    exact inv addr' se' heng' hidx'
  -- ── S-Clean: remove terminated engine ─────────────────────────────────
  | sClean =>
    subst_vars
    rename_i addr _ heng _ _
    by_cases h : addr' = addr
    · subst h; rw [engineAt_removeEngineAt_self] at heng'; simp at heng'
    · rw [engineAt_removeEngineAt_ne _ _ _ h] at heng'
      exact inv addr' se' heng' hidx'
  -- ── M-Send: only messages change, engines unchanged ───────────────────
  | mSend =>
    subst_vars
    -- engineAt is independent of messages (definitional by withMessages_engineAt)
    exact inv addr' se' heng' hidx'
  -- ── M-Enqueue: mailbox status changes (ready→busy), env unchanged ────
  | mEnqueue =>
    subst_vars
    rename_i m mboxEng _ _ _ _ _ heng _ _ _ _
    simp only [SystemState.withMessages_engineAt] at heng'
    by_cases h : addr' = m.target
    · -- Updated engine: only status changed, env/localState identical
      subst h
      rw [engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩] at heng'
      cases heng'
      exact inv m.target mboxEng heng hidx'
    · rw [engineAt_updateEngineAt_ne _ _ _ _ h] at heng'
      exact inv addr' se' heng' hidx'
  -- ── S-SpawnWithMailbox: fresh engines at new addresses ────────────────
  | sSpawnMbox =>
    rcases Classical.em (κ.engineAt addr' = some se') with heq | heq
    · exact inv addr' se' heq hidx'
    · exact hbt addr' se' heng' heq hidx'
  -- ── M-Dequeue: proc status changes, mailbox env changes ──────────────
  | mDequeue =>
    subst_vars
    rename_i procAddr i procEng mboxEng _ v _ hproc _ _ hmbox _ _ _
    have hne : κ.mailboxOf procAddr ≠ procAddr := mailboxOf_ne_self κ procAddr
    -- Intermediate state after updating procAddr preserves the mailbox
    have hmbox₁ : (κ.updateEngineAt procAddr
        ⟨i, { procEng with status := .busy v }⟩).engineAt
        (κ.mailboxOf procAddr) = some mboxEng := by
      rw [engineAt_updateEngineAt_ne _ _ _ _ hne]; exact hmbox
    by_cases h1 : addr' = κ.mailboxOf procAddr
    · -- addr' = mailbox: env changes via mailboxRemove
      subst h1
      rw [engineAt_updateEngineAt_self _ _ _ ⟨_, hmbox₁⟩] at heng'
      simp only [Option.some.injEq] at heng'
      subst heng'
      -- Provide explicit idx and localState to match the OLD engine state
      exact mailboxRemove_preserves_causalInvariant
        (idx := mboxEng.idx) (localState := mboxEng.engine.env.localState)
        hidx' (inv _ mboxEng hmbox hidx')
    · by_cases h2 : addr' = procAddr
      · -- addr' = procAddr: only status changed, env unchanged
        subst h2
        rw [engineAt_updateEngineAt_ne _ _ _ _ (Ne.symm hne),
            engineAt_updateEngineAt_self _ _ _ ⟨_, hproc⟩] at heng'
        cases heng'
        exact inv addr' ⟨_, procEng⟩ hproc hidx'
      · -- addr' = neither: engine unchanged
        rw [engineAt_updateEngineAt_ne _ _ _ _ h1,
            engineAt_updateEngineAt_ne _ _ _ _ h2] at heng'
        exact inv addr' se' heng' hidx'
  -- ── S-Process: effect may modify engine state ─────────────────────────
  | sProcess =>
    rcases Classical.em (κ.engineAt addr' = some se') with heq | heq
    · exact inv addr' se' heq hidx'
    · exact hbt addr' se' heng' heq hidx'

end MailboxActors.Examples.CausalMailbox
