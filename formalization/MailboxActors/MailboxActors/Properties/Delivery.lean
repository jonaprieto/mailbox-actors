/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment
import MailboxActors.Properties.TypePreservation
import MailboxActors.Properties.Isolation

/-!
# Eventual Delivery

Under a weak fairness assumption, every in-transit message addressed to a
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

/-- Consecutive states in the trace are related by a system step. -/
def IsExecution (trace : Trace) : Prop :=
  ∀ n, SysStep (trace n) (trace (n + 1))

/-- Message `m` appears at most once in the in-transit list at every
    step from `n` onwards (each sent message is a unique packet). -/
def UniqueInTransit (trace : Trace) (m : Message) (n : Nat) : Prop :=
  ∀ k ≥ n, ∀ pre post : List Message,
    (trace k).messages = pre ++ m :: post → m ∉ pre ∧ m ∉ post

/-- Well-typedness and mailbox isolation are jointly preserved along
    any execution trace. -/
private lemma invariants_trace (trace : Trace) (hexec : IsExecution trace) (n : Nat)
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

/-- The mailbox engine for `m` is ready to accept a message at every step
    where `m` is in transit. This holds when the mailbox filter is
    `λ_.true` (the default) and the mailbox is not permanently busy. -/
def EnqueueReady (trace : Trace) (m : Message) (n : Nat) : Prop :=
  ∀ k ≥ n, m ∈ (trace k).messages →
    ∀ se : SomeEngine, (trace k).engineAt m.target = some se →
      ∃ (f : EngineSpec.MsgType se.idx → Bool)
        (w : EngineSpec.MsgType se.idx),
        se.engine.status = EngineStatus.ready f ∧ f w = true

/-- **Eventual Delivery**: under weak fairness every in-transit message is
    eventually consumed.

    **Hypotheses beyond the original statement:**
    * `MailboxIsolation` — every message targets a mailbox-mode engine
      (proved preserved by `mailboxIsolation`).
    * `UniqueInTransit` — the message `m` appears at most once in the
      in-transit list at every step (each sent message is a unique packet).
    * `EnqueueReady` — the target mailbox engine is in `ready(f)` state
      with a value `w` passing the filter `f` whenever `m` is in transit.
    * `WeaklyFair` uses predicate-level fairness (TLA⁺-style) so that
      fairness applies to the specific enqueue transition for `m`. -/
theorem eventualDelivery (trace : Trace) (m : Message) (n : Nat) :
    IsExecution trace →
    WeaklyFair trace →
    WellTypedState (trace n) →
    MailboxIsolation (trace n) →
    UniqueInTransit trace m n →
    EnqueueReady trace m n →
    m ∈ (trace n).messages →
    ∃ k ≥ n, m ∉ (trace k).messages := by
  intro hexec hfair hwt hiso huniq henqready hm
  -- By contradiction: assume m is always in transit from n onwards.
  by_contra hall
  push_neg at hall
  -- hall : ∀ k ≥ n, m ∈ (trace k).messages
  -- Define P: "enqueue message m via M-Enqueue (mailbox ready→busy,
  -- message removed from transit)."
  let P : SystemState → SystemState → Prop := fun κ κ' =>
    ∃ (mboxEng : SomeEngine) (pre post : List Message),
      κ.messages = pre ++ m :: post ∧
      κ.engineAt m.target = some mboxEng ∧
      mboxEng.engine.mode = EngineMode.mail ∧
      κ'.messages = pre ++ post
  -- P is continuously enabled from n onwards.
  have henabled : ∀ k ≥ n, ∃ κ', P (trace k) κ' := by
    intro k hk
    have hm_k := hall k hk
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hm_k
    obtain ⟨hwt_k, hiso_k⟩ := invariants_trace trace hexec n hwt hiso k hk
    obtain ⟨se, hse, _⟩ := hwt_k.messages_typed m hm_k
    have hmode := hiso_k m hm_k se hse
    obtain ⟨f, w, _, hfilter⟩ := henqready k hk hm_k se hse
    exact ⟨{ (trace k).updateEngineAt m.target
               ⟨se.idx, { se.engine with status := .busy w }⟩
             with messages := pre ++ post },
           se, pre, post, hsplit, hse, hmode, rfl⟩
  -- By weak fairness, P fires at some step k₀ ≥ n.
  obtain ⟨k₀, hk₀, hP⟩ := hfair P n henabled
  obtain ⟨_, pre, post, hsplit, _, _, hmsg⟩ := hP
  -- By UniqueInTransit, m appears only once, so m ∉ pre ∧ m ∉ post.
  obtain ⟨hpre, hpost⟩ := huniq k₀ hk₀ pre post hsplit
  -- Therefore m ∉ (trace (k₀ + 1)).messages.
  have : m ∉ (trace (k₀ + 1)).messages := by
    rw [hmsg, List.mem_append]; push_neg; exact ⟨hpre, hpost⟩
  -- Contradiction: hall says m ∈ (trace (k₀ + 1)).messages.
  exact this (hall (k₀ + 1) (by omega))

end MailboxActors
