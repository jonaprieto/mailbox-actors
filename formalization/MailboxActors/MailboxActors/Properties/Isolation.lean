import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment
import MailboxActors.Properties.EffectPreservation

/-!
# Mailbox Isolation

Processing engines never directly receive messages from the message set.
All messages are mediated by the corresponding mailbox engine.
-/

namespace MailboxActors

variable [EngineSpec]


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
    rename_i _ addr _ _ _ _
    intro m hm se hse
    simp only [SystemState.removeEngineAt_messages] at hm
    by_cases htarget : m.target = addr
    · -- Impossible: removal makes engineAt return none
      have := engineAt_removeEngineAt_self κ addr
      rw [htarget] at hse; rw [this] at hse; exact absurd hse (by simp)
    · -- Different address: engineAt unchanged
      rw [engineAt_removeEngineAt_ne κ addr m.target htarget] at hse
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
  | sSpawnMbox =>
    subst_vars
    rename_i _ nodeId procSe mboxSe hnode _ _ _ hfreshP hfreshM
    intro m hm se hse
    simp only [SystemState.addEngineAt_messages] at hm
    simp only [SystemState.withNextId_engineAt] at hse
    have hne_proc : m.target ≠ ⟨nodeId, κ.nextId⟩ := by
      intro h; have := wt.nextId_messages m hm; rw [h] at this; simp at this
    have hne_mbox : m.target ≠ κ.mailboxOf ⟨nodeId, κ.nextId⟩ := by
      intro h; have h₁ := wt.nextId_messages m hm
      have h₂ : m.target.engineId = κ.nextId + 1 := by rw [h]; rfl
      omega
    rw [engineAt_addEngineAt_ne _ _ _ _ hne_mbox,
        engineAt_addEngineAt_ne _ _ _ _ hne_proc] at hse
    exact hiso m hm se hse
  | sProcess _ _ _ _ _ _ _ _ _ _ heff hresolve =>
    exact (sProcessPreservesInvariants _ _ _ _ _ _ heff hresolve wt hiso).2
  | mEnqueue =>
    subst_vars
    rename_i m mboxEng _ _ pre post hmsg heng _ hmode _ _
    intro m' hm' se hse
    simp only [SystemState.withMessages_engineAt] at hse
    have hm'_old : m' ∈ κ.messages := by
      rw [hmsg]; simp only [List.mem_append, List.mem_cons] at hm' ⊢; tauto
    by_cases h : m'.target = m.target
    · -- target = m.target: updated engine still has mode mail
      rw [h, engineAt_updateEngineAt_self _ _ _ ⟨_, heng⟩] at hse
      cases hse; exact hmode
    · -- target ≠ m.target: engine unchanged
      rw [engineAt_updateEngineAt_ne _ _ _ _ h] at hse
      exact hiso m' hm'_old se hse
  | mDequeue =>
    subst_vars
    rename_i _ procAddr i procEng mboxEng _ _ _ hproc hpmode _ hmbox _ _ _
    have hne : κ.mailboxOf procAddr ≠ procAddr := mailboxOf_ne_self κ procAddr
    intro m hm se hse
    simp only [SystemState.updateEngineAt_messages] at hm
    by_cases h1 : m.target = κ.mailboxOf procAddr
    · -- target = mailbox: mode preserved (only env changed)
      rw [h1, engineAt_updateEngineAt_self _ _ _ ⟨_, by
        rw [engineAt_updateEngineAt_ne _ _ _ _ hne]; exact hmbox⟩] at hse
      cases hse
      exact hiso m hm mboxEng (by rw [h1]; exact hmbox)
    · rw [engineAt_updateEngineAt_ne _ _ _ _ h1] at hse
      by_cases h2 : m.target = procAddr
      · -- target = proc engine: mode = process contradicts hiso (mode = mail)
        rw [h2, engineAt_updateEngineAt_self _ _ _ ⟨_, hproc⟩] at hse
        cases hse
        exact absurd (hiso m hm ⟨i, procEng⟩ (by rw [h2]; exact hproc)) (by simp [hpmode])
      · -- target = neither: lookup unchanged
        rw [engineAt_updateEngineAt_ne _ _ _ _ h2] at hse
        exact hiso m hm se hse

-- ── Mailbox Persistence ──────────────────────────────────────────────────

/-- **Mailbox persistence after cleanup** (Remark 4.4): when S-Clean removes
    a terminated processing engine, its paired mailbox engine survives.
    This prevents in-flight messages from being orphaned. -/
theorem mailboxPersistence (κ : SystemState) (addr : Address) (se : SomeEngine)
    (_heng : κ.engineAt addr = some se)
    (_hmode : se.engine.mode = EngineMode.process)
    (_hterm : se.engine.status = EngineStatus.terminated) :
    (κ.removeEngineAt addr).engineAt (κ.mailboxOf addr) =
      κ.engineAt (κ.mailboxOf addr) := by
  exact engineAt_removeEngineAt_ne κ addr (κ.mailboxOf addr) (mailboxOf_ne_self κ addr)

/-- After S-Clean, a well-typed state's paired mailbox still exists. -/
theorem mailboxSurvivesClean (κ : SystemState) (wt : WellTypedState κ)
    (addr : Address) (se : SomeEngine)
    (heng : κ.engineAt addr = some se)
    (hmode : se.engine.mode = EngineMode.process)
    (hterm : se.engine.status = EngineStatus.terminated) :
    ∃ mboxSe : SomeEngine,
      (κ.removeEngineAt addr).engineAt (κ.mailboxOf addr) = some mboxSe ∧
      mboxSe.idx = se.idx ∧
      mboxSe.engine.mode = EngineMode.mail := by
  obtain ⟨mboxSe, hmbox, hidx, hmboxMode⟩ := wt.mailbox_exists addr se heng hmode
  exact ⟨mboxSe, by rw [mailboxPersistence κ addr se heng hmode hterm]; exact hmbox,
    hidx, hmboxMode⟩

end MailboxActors
