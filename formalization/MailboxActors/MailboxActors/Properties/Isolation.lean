/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Mailbox Isolation

Processing engines never directly receive messages from the message set.
All messages are mediated by the corresponding mailbox engine.
Paper Proposition 4.
-/

namespace MailboxActors

variable [EngineSpec]

/-- All messages in transit target mailbox engines (not processing engines). -/
def MailboxIsolation (κ : SystemState) : Prop :=
  ∀ m ∈ κ.messages,
    ∀ se : SomeEngine,
      κ.engineAt m.target = some se →
      se.engine.mode = EngineMode.mail

/-- **Mailbox Isolation**: M-Send is the only rule that creates messages,
    and it always targets a mailbox engine.
    Paper Proposition 4. -/
theorem mailboxIsolation (κ κ' : SystemState) (op : OpLabel) :
    MailboxIsolation κ → OpStep κ op κ' → MailboxIsolation κ' := by
  sorry

end MailboxActors
