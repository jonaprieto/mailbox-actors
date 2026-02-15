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

/-- **Eventual Delivery**: under weak fairness every in-transit message is
    eventually consumed, PROVIDED the target mailbox eventually accepts it.

    **Hypotheses:**
    * `MailboxIsolation` — target is a mailbox.
    * `UniqueInTransit` — message uniqueness.
    * `EventuallyAccepts` — filters do not permanently block.
    * `WeaklyFair` — scheduler is fair. -/
theorem eventualDelivery (trace : Trace) (m : Message) (n : Nat) :
    IsExecution trace →
    WeaklyFair trace →
    WellTypedState (trace n) →
    MailboxIsolation (trace n) →
    UniqueInTransit trace m n →
    EventuallyAccepts trace m n →
    m ∈ (trace n).messages →
    ∃ k ≥ n, m ∉ (trace k).messages := by
  intro hexec hfair hwt hiso huniq haccepts hm
  -- Strategy: EventuallyAccepts gives a step l ≥ n where M-Enqueue is enabled
  -- (mailbox ready + filter accepts). WeaklyFair then gives a step where M-Enqueue
  -- actually fires, removing m from messages.
  --
  -- Gap: WeaklyFair requires *continuous* enablement from some point, but the
  -- mailbox may oscillate between ready/busy states. A stronger fairness
  -- assumption (strong fairness) or an explicit "mailbox eventually stabilises"
  -- hypothesis would close this. Left as sorry per Phase 3 plan.
  sorry

end MailboxActors
