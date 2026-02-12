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
    Paper Proposition 5. -/
theorem eventualDelivery (trace : Trace) (m : Message) (n : Nat) :
    IsExecution trace →
    WeaklyFair trace →
    WellTypedState (trace n) →
    m ∈ (trace n).messages →
    ∃ k ≥ n, m ∉ (trace k).messages := by
  sorry

end MailboxActors
