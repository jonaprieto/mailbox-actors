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
    and it always targets a mailbox engine.  Requires well-typedness so that
    `mailbox_exists` guarantees the paired mailbox is in `mail` mode. -/
theorem mailboxIsolation (κ κ' : SystemState) (op : OpLabel) :
    WellTypedState κ → MailboxIsolation κ → OpStep κ op κ' → MailboxIsolation κ' := by
  intro wt hiso step
  cases step with
  | sNode =>
    subst_vars
    have key := engineAt_append_emptyNode κ
    intro m hm se hse
    rw [key] at hse
    exact hiso m hm se hse
  | sClean =>
    subst_vars
    rename_i _ addr _ _ _ _ hnomsgs
    intro m hm se hse
    simp only [SystemState.removeEngineAt_messages] at hm
    have hne := hnomsgs m hm
    rw [engineAt_removeEngineAt_ne κ addr m.target hne] at hse
    exact hiso m hm se hse
  | mSend =>
    subst_vars
    rename_i sender target senderEng targetEng hsender htarget hmode hidx
    intro m hm se hse
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · exact hiso m hm se hse
    · rw [List.mem_singleton] at hm; subst hm
      obtain ⟨mboxSe, hmbox, _, hmboxMode⟩ :=
        wt.mailbox_exists target targetEng htarget hmode
      have hse' : κ.engineAt (κ.mailboxOf target) = some se := hse
      rw [hmbox] at hse'
      cases hse'
      exact hmboxMode
  | mEnqueue =>
    subst_vars
    rename_i pre post hmsg _ _
    intro m' hm' se hse
    apply hiso m' _ se hse
    rw [hmsg]
    simp only [List.mem_append, List.mem_cons] at hm' ⊢
    tauto
  | mDequeue => subst_vars; sorry

end MailboxActors
