import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment
import MailboxActors.Properties.TypePreservation
import MailboxActors.Properties.Isolation
import Mathlib.Data.List.Basic

/-!
# Eventual Delivery

Under a fairness assumption, every in-transit message addressed to a
non-terminated processing engine is eventually enqueued in its mailbox.
-/

namespace MailboxActors

variable [EngineSpec]

/-- An execution trace is an infinite sequence of system states. -/
abbrev Trace := Nat → SystemState

/-- Weak fairness (TLA⁺-style): every continuously enabled transition
    predicate is eventually taken. -/
def WeaklyFair (trace : Trace) : Prop :=
  ∀ (P : SystemState → SystemState → Prop) n,
    (∀ k ≥ n, ∃ κ', P (trace k) κ') →
    ∃ k ≥ n, P (trace k) (trace (k + 1))

/-- Strong fairness: every infinitely often enabled transition
    predicate is eventually taken. -/
def StronglyFair (trace : Trace) : Prop :=
  ∀ (P : SystemState → SystemState → Prop) n,
    (∀ k ≥ n, ∃ l ≥ k, ∃ κ', P (trace l) κ') →
    ∃ k ≥ n, P (trace k) (trace (k + 1))

/-- Consecutive states in the trace are related by a system step. -/
def IsExecution (trace : Trace) : Prop :=
  ∀ n, SysStep (trace n) (trace (n + 1))

/-- Message `m` appears at most once in the in-transit list at every
    step from `n` onwards (each sent message is a unique packet). -/
def UniqueInTransit (trace : Trace) (m : Message) (n : Nat) : Prop :=
  ∀ k ≥ n, ∀ pre post : List Message,
    (trace k).messages = pre ++ m :: post → m ∉ pre ∧ m ∉ post

/-- **Safety**: well-typedness and mailbox isolation are jointly preserved
    along any execution trace starting from a well-typed state. -/
theorem invariants_trace (trace : Trace) (hexec : IsExecution trace) (n : Nat)
    (hwt : WellTypedState (trace n)) (hiso : MailboxIsolation (trace n))
    (k : Nat) (hk : n ≤ k) :
    WellTypedState (trace k) ∧ MailboxIsolation (trace k) := by
  induction k with
  | zero =>
    have : n = 0 := by omega
    subst this; exact ⟨hwt, hiso⟩
  | succ k ih =>
    by_cases h : n ≤ k
    · obtain ⟨hwt_k, hiso_k⟩ := ih h
      obtain ⟨op, hstep⟩ := hexec k
      exact ⟨typePreservation _ _ op hwt_k hiso_k hstep,
             mailboxIsolation _ _ op hwt_k hiso_k hstep⟩
    · have : n = k + 1 := by omega
      subst this; exact ⟨hwt, hiso⟩

/-- The target mailbox eventually accepts the message.
    This is a liveness property required for Eventual Delivery:
    the mailbox must not permanently block the message via filters. -/
def EventuallyAccepts (trace : Trace) (m : Message) (n : Nat) : Prop :=
  ∀ k ≥ n, m ∈ (trace k).messages →
    ∃ l ≥ k, ∃ se, (trace l).engineAt m.target = some se ∧
      se.engine.mode = EngineMode.mail ∧
      ∃ f w, se.engine.status = EngineStatus.ready f ∧
      m.payload = ⟨se.idx, w⟩ ∧ f w = true

lemma effect_preserves_messages (κ κ' : SystemState) (i : EngineSpec.EngIdx) (E : Effect i) :
    EffectEvalStep κ i E κ' → ∀ m, m ∈ κ.messages → m ∈ κ'.messages := by
  intro h m hm
  induction h
  case noop => exact hm
  case send hκ' => rw [hκ']; split <;> [split <;> simp [List.mem_append, hm]; exact hm]
  case terminate hκ' => rw [hκ']; split <;> simp [SystemState.updateEngineAt_messages, hm]
  case update hκ' => rw [hκ']; simp [SystemState.updateEngineAt_messages, hm]
  case mfilter hκ' => rw [hκ']; simp [SystemState.updateEngineAt_messages, hm]
  case spawn hκ' => rw [hκ']; split <;> simp [SystemState.addEngineAt_messages, hm]
  case chain ih1 ih2 => exact ih2 (ih1 hm)

/-- If message `m` is in the trace at step `k` and not in step `k+1`,
    then an `M-Enqueue` operation for `m` must have occurred. -/
lemma message_removal (trace : Trace) (hexec : IsExecution trace) (m : Message) (k : Nat) :
    m ∈ (trace k).messages → m ∉ (trace (k + 1)).messages →
    ∃ mboxEng w f pre post,
      (trace k).messages = pre ++ m :: post ∧
      OpStep (trace k) OpLabel.enqueue (trace (k + 1)) ∧
      (trace k).engineAt m.target = some mboxEng ∧
      m.payload = ⟨mboxEng.idx, w⟩ ∧
      mboxEng.engine.mode = EngineMode.mail ∧
      mboxEng.engine.status = EngineStatus.ready f ∧
      f w = true := by
  intro hk hnk
  obtain ⟨op, hstep⟩ := hexec k
  cases hstep
  case sNode hκ' =>
    rw [hκ'] at hnk; simp at hnk; contradiction
  case sClean h_eng h_mode h_term hκ' =>
    rw [hκ'] at hnk; simp at hnk; contradiction
  case mSend h1 h2 h3 h4 hκ' =>
    rw [hκ'] at hnk; simp [List.mem_append] at hnk
    have := hnk.left; contradiction
  case mEnqueue m' mboxEng w f pre post hmsg heng hpay hmode hstat hf hκ' =>
    by_cases hm : m = m'
    · subst hm
      use mboxEng, w, f, pre, post
      refine ⟨hmsg, OpStep.mEnqueue _ _ _ _ _ _ _ _ hmsg heng hpay hmode hstat hf hκ',
              heng, hpay, hmode, hstat, hf⟩
    · exfalso
      rw [hκ'] at hnk; simp [List.mem_append] at hnk
      have hmem : m ∈ pre ++ post := by
        rw [hmsg] at hk
        simp only [List.mem_append, List.mem_cons] at hk
        rcases hk with h | h | h
        · exact List.mem_append.mpr (Or.inl h)
        · contradiction
        · exact List.mem_append.mpr (Or.inr h)
      rcases List.mem_append.mp hmem with h | h
      · exact hnk.left h
      · exact hnk.right h
  case sSpawnMbox h1 h2 h3 h4 h5 h6 h7 h8 h9 hκ' =>
    rw [hκ'] at hnk; simp [SystemState.addEngineAt_messages] at hnk; contradiction
  case mDequeue h1 h2 h3 h4 h5 h6 h7 h8 h9 hκ' =>
    rw [hκ'] at hnk; simp [SystemState.updateEngineAt_messages] at hnk; contradiction
  case sProcess heff hres =>
    obtain ⟨p', hp', hκ''⟩ := hres
    rw [hκ''] at hnk; simp [SystemState.updateEngineAt_messages] at hnk
    have hm' : m ∈ _ := effect_preserves_messages _ _ _ _ heff m hk
    contradiction

omit [EngineSpec] in
lemma list_split_of_mem {α : Type} (m : α) (l : List α) (h : m ∈ l) :
    ∃ (pre post : List α), l = pre ++ m :: post := by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | h_in
    · use [], tl; simp
    · obtain ⟨pre', post', hsplit'⟩ := ih h_in
      use hd :: pre', post'; rw [hsplit']; simp

/-- **Eventual Delivery**: under strong fairness every in-transit message is
    eventually consumed, PROVIDED the target mailbox eventually accepts it.

    **Hypotheses:**
    * `MailboxIsolation` — target is a mailbox.
    * `UniqueInTransit` — message uniqueness.
    * `EventuallyAccepts` — filters do not permanently block.
    * `StronglyFair` — scheduler is fair. -/
theorem eventualDelivery (trace : Trace) (m : Message) (n : Nat) :
    IsExecution trace →
    StronglyFair trace →
    WellTypedState (trace n) →
    MailboxIsolation (trace n) →
    UniqueInTransit trace m n →
    EventuallyAccepts trace m n →
    m ∈ (trace n).messages →
    ∃ k ≥ n, m ∉ (trace k).messages := by
  intro hexec hfair hwt hiso huniq haccepts hm
  let P (κ κ' : SystemState) : Prop :=
    ∃ mboxEng w f pre post,
      κ.messages = pre ++ m :: post ∧
      κ.engineAt m.target = some mboxEng ∧
      m.payload = ⟨mboxEng.idx, w⟩ ∧
      mboxEng.engine.mode = EngineMode.mail ∧
      mboxEng.engine.status = EngineStatus.ready f ∧
      f w = true ∧
      κ' = { κ.updateEngineAt m.target ⟨mboxEng.idx, { mboxEng.engine with status := .busy w }⟩
             with messages := pre ++ post }
  
  by_contra hnever
  push_neg at hnever
  -- hnever : ∀ (k : ℕ), n ≤ k → m ∈ (trace k).messages
  
  have henabled : ∀ k ≥ n, ∃ l ≥ k, ∃ κ', P (trace l) κ' := by
    intro k hk
    obtain ⟨l, hl_ge, se, hse, hmode, f, w, hstat, hpay, hf⟩ := haccepts k hk (hnever k hk)
    have hl_ge_n : l ≥ n := by omega
    have hmem_l : m ∈ (trace l).messages := hnever l hl_ge_n
    obtain ⟨pre, post, hsplit⟩ := list_split_of_mem m (trace l).messages hmem_l
    let κ' := { (trace l).updateEngineAt m.target ⟨se.idx, { se.engine with status := .busy w }⟩
                with messages := pre ++ post }
    use l, hl_ge, κ', se, w, f, pre, post
  obtain ⟨k, hk_ge, hPk⟩ := hfair P n henabled
  obtain ⟨mboxEng, w, f, pre, post, hsplit, heng, hpay, hmode, hstat, hf, hnext⟩ := hPk
  
  have hnk : m ∉ (trace (k + 1)).messages := by
    rw [hnext]
    simp only [List.mem_append, not_or]
    have huniq_k : UniqueInTransit trace m n := huniq
    specialize huniq_k k hk_ge
    exact huniq_k pre post hsplit
  exact hnk (hnever (k + 1) (by omega))

end MailboxActors
