/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment

/-!
# Type Preservation

If a well-typed state takes a step, the resulting state is well-typed.
Paper Proposition 1.
-/

namespace MailboxActors

variable [EngineSpec]

-- ============================================================================
-- § Helper lemmas
-- ============================================================================

/-- `match`-over-`find?` is stable under appending a node with empty engines. -/
private lemma find?_match_append_emptyEngines (nodes : List Node) (emptyNode : Node)
    (hn : emptyNode.engines = []) (p : Node → Bool) (eid : Nat) :
    (match (nodes ++ [emptyNode]).find? p with
     | some node => node.getEngine eid
     | none => none) =
    (match nodes.find? p with
     | some node => node.getEngine eid
     | none => none) := by
  induction nodes with
  | nil =>
    simp only [List.nil_append, List.find?_nil]
    cases hp : p emptyNode
    · simp [hp]
    · simp [hp, Node.getEngine, hn]
  | cons hd tl ih =>
    simp only [List.cons_append]
    cases hp : p hd
    · simp only [List.find?_cons, hp]; exact ih
    · simp only [List.find?_cons, hp]

/-- Appending a node with empty engines preserves all engine lookups. -/
private lemma engineAt_append_emptyNode (κ : SystemState) (addr : Address) :
    SystemState.engineAt
      ⟨κ.nodes ++ [{ id := κ.nextId, engines := [] }], κ.messages, κ.nextId + 1⟩ addr =
    κ.engineAt addr := by
  unfold SystemState.engineAt
  exact find?_match_append_emptyEngines κ.nodes ⟨κ.nextId, []⟩ rfl _ _

-- ============================================================================
-- § Main theorem
-- ============================================================================

/-- **Type Preservation**: transitions preserve well-typedness.
    Paper Proposition 1. -/
theorem typePreservation (κ κ' : SystemState) (op : OpLabel) :
    WellTypedState κ → OpStep κ op κ' → WellTypedState κ' := by
  intro wt step
  cases step with
  -- ── S-Node: create a new empty node ──────────────────────────────────────
  | sNode =>
    subst_vars
    -- engineAt is preserved because the new node has no engines.
    have key := engineAt_append_emptyNode κ
    exact {
      messages_typed := fun m hm => by
        obtain ⟨se, hse, hidx⟩ := wt.messages_typed m hm
        exact ⟨se, by rw [key]; exact hse, hidx⟩
      mailbox_exists := fun addr se heng hmode => by
        rw [key] at heng
        obtain ⟨mboxSe, hmbox, hmboxIdx⟩ := wt.mailbox_exists addr se heng hmode
        exact ⟨mboxSe, by rw [key]; exact hmbox, hmboxIdx⟩
    }
  -- ── S-Clean: placeholder κ' = κ ─────────────────────────────────────────
  | sClean => subst_vars; exact wt
  -- ── M-Send: place message in transit to target's mailbox ────────────────
  | mSend =>
    subst_vars
    rename_i sender target senderEng targetEng hsender htarget hmode v
    exact {
      messages_typed := fun m hm => by
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · -- old message: nodes unchanged, so engineAt is the same
          exact wt.messages_typed m hm
        · -- new message: ⟨sender, κ.mailboxOf target, ⟨targetEng.idx, v⟩⟩
          rw [List.mem_singleton] at hm; subst hm
          -- By mailbox_exists the mailbox has the same type index as targetEng.
          obtain ⟨mboxSe, hmbox, hmboxIdx⟩ :=
            wt.mailbox_exists target targetEng htarget hmode
          exact ⟨mboxSe, hmbox, hmboxIdx.symm⟩
      mailbox_exists := fun addr se heng hmode' =>
        -- nodes unchanged, so engineAt and mailboxOf are the same
        wt.mailbox_exists addr se heng hmode'
    }
  -- ── M-Enqueue: placeholder κ' = κ ──────────────────────────────────────
  | mEnqueue => subst_vars; exact wt
  -- ── M-Dequeue: placeholder κ' = κ ──────────────────────────────────────
  | mDequeue => subst_vars; exact wt

end MailboxActors
