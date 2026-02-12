/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Eventual Delivery

Under a weak fairness assumption, every in-transit message addressed to a
non-terminated processing engine is eventually enqueued in its mailbox.
Paper Proposition 5.
-/

namespace MailboxActors

variable [EngineSpec]

/-- An execution trace is an infinite sequence of system states. -/
abbrev Trace := Nat → SystemState

/-- Weak fairness: every continuously applicable operation is eventually taken. -/
def WeaklyFair (trace : Trace) : Prop :=
  ∀ n op, (∀ m ≥ n, ∃ κ', OpStep (trace m) op κ') →
    ∃ m ≥ n, OpStep (trace m) op (trace (m + 1))

/-- Consecutive states in the trace are related by a system step. -/
def IsExecution (trace : Trace) : Prop :=
  ∀ n, SysStep (trace n) (trace (n + 1))

/-- **Eventual Delivery**: under weak fairness, messages are eventually consumed.
    Paper Proposition 5.

    **Status: blocked on placeholder rules.**  The current `mEnqueue` rule uses
    `κ' = κ` (a placeholder), so it does not actually remove the message from the
    in-transit list.  In fact, `mSend` is the only rule that modifies `κ.messages`
    (by appending), while all other rules leave messages unchanged.  This makes
    `κ.messages` monotonically non-decreasing, so the conclusion
    `∃ k ≥ n, m ∉ (trace k).messages` is **refutable** in the current formalization.

    To prove this theorem, `mEnqueue` must be updated to produce
    `κ' = { κ with messages := κ.messages.erase m }` (or an equivalent removal),
    and the `WeaklyFair` definition may need refinement to ensure fairness at the
    level of individual messages rather than just operation labels. -/
theorem eventualDelivery (trace : Trace) (m : Message) (n : Nat) :
    IsExecution trace →
    WeaklyFair trace →
    WellTypedState (trace n) →
    m ∈ (trace n).messages →
    ∃ k ≥ n, m ∉ (trace k).messages := by
  sorry

end MailboxActors
