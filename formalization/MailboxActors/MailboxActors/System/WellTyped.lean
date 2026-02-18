import MailboxActors.System.State

/-!
# Well-Typed System State

The well-typedness predicate used in the metatheoretic properties.
-/

namespace MailboxActors

variable [EngineSpec]

/-- A system state is well-typed when:
    1. Every message payload conforms to its target's interface.
    2. Every processing engine has a valid paired mailbox.
    3. All engine components are consistently typed. -/
structure WellTypedState (κ : SystemState) : Prop where
  /-- Every in-transit message has a payload whose engine type index matches
      the target engine's type (if it exists). -/
  messages_typed :
    ∀ m ∈ κ.messages,
      ∀ se : SomeEngine,
        κ.engineAt m.target = some se → m.payload.1 = se.idx
  /-- Every processing engine has a paired mailbox engine in the system
      whose type index matches and whose mode is `mail`. -/
  mailbox_exists :
    ∀ (addr : Address) (se : SomeEngine),
      κ.engineAt addr = some se →
      se.engine.mode = EngineMode.process →
      ∃ mboxSe : SomeEngine,
        κ.engineAt (κ.mailboxOf addr) = some mboxSe ∧ mboxSe.idx = se.idx ∧
        mboxSe.engine.mode = EngineMode.mail

/-- All messages in transit target mailbox engines (not processing engines). -/
def MailboxIsolation (κ : SystemState) : Prop :=
  ∀ m ∈ κ.messages,
    ∀ se : SomeEngine,
      κ.engineAt m.target = some se →
      se.engine.mode = EngineMode.mail

-- ── Corollaries ──────────────────────────────────────────────────────────

/-- **Spawn pairing**: every processing engine has a paired mailbox engine
    with matching type index in `mail` mode.  Restates `mailbox_exists`
    as a standalone theorem for clarity. -/
theorem spawnPairing (κ : SystemState) (wt : WellTypedState κ)
    (addr : Address) (se : SomeEngine)
    (heng : κ.engineAt addr = some se) (hmode : se.engine.mode = EngineMode.process) :
    ∃ mboxSe : SomeEngine,
      κ.engineAt (κ.mailboxOf addr) = some mboxSe ∧
      mboxSe.idx = se.idx ∧
      mboxSe.engine.mode = EngineMode.mail :=
  wt.mailbox_exists addr se heng hmode

end MailboxActors
