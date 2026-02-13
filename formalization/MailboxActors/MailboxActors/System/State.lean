/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.Node
import MailboxActors.Engine.Message

/-!
# System State
-/

namespace MailboxActors

variable [EngineSpec]

/-- System state `κ = (N, M, Ω)`. -/
structure SystemState where
  nodes : List Node
  messages : List Message
  /-- Monotonic counter for fresh identifier generation. -/
  nextId : Nat

/-- Generate a fresh identifier and advance the counter. -/
def SystemState.freshId (κ : SystemState) : Nat × SystemState :=
  (κ.nextId, { κ with nextId := κ.nextId + 1 })

/-- The `mailboxOf` mapping: returns the mailbox address for a processing
    engine.  Modelled as a total function on addresses. -/
def SystemState.mailboxOf (_κ : SystemState) (addr : Address) : Address :=
  -- Convention: the paired mailbox has engineId = addr.engineId + 1
  -- on the same node (matching S-SpawnWithMailbox's sequential allocation).
  { addr with engineId := addr.engineId + 1 }

lemma mailboxOf_ne_self (κ : SystemState) (addr : Address) :
    κ.mailboxOf addr ≠ addr := by
  intro h
  have : (κ.mailboxOf addr).engineId = addr.engineId := by rw [h]
  simp [SystemState.mailboxOf] at this

lemma mailboxOf_injective (κ : SystemState) {addr addr' : Address}
    (h : κ.mailboxOf addr = κ.mailboxOf addr') : addr = addr' := by
  have h1 : (κ.mailboxOf addr).nodeId = (κ.mailboxOf addr').nodeId := by rw [h]
  have h2 : (κ.mailboxOf addr).engineId = (κ.mailboxOf addr').engineId := by rw [h]
  simp [SystemState.mailboxOf] at h1 h2
  cases addr; cases addr'; simp only [Address.mk.injEq]; exact ⟨h1, h2⟩

/-- Look up an engine globally by its address. -/
def SystemState.engineAt (κ : SystemState) (addr : Address) : Option SomeEngine :=
  match κ.nodes.find? (fun n => n.id == addr.nodeId) with
  | some node => node.getEngine addr.engineId
  | none => none

/-- The initial (empty) system state. -/
def SystemState.initial : SystemState :=
  { nodes := [], messages := [], nextId := 0 }

/-- `find?`-then-`getEngine` is stable under appending a node with empty engines. -/
lemma find?_match_append_emptyEngines (nodes : List Node) (emptyNode : Node)
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
lemma engineAt_append_emptyNode (κ : SystemState) (addr : Address) :
    SystemState.engineAt
      ⟨κ.nodes ++ [{ id := κ.nextId, engines := [] }], κ.messages, κ.nextId + 1⟩ addr =
    κ.engineAt addr := by
  unfold SystemState.engineAt
  exact find?_match_append_emptyEngines κ.nodes ⟨κ.nextId, []⟩ rfl _ _

-- ============================================================================
-- § Engine Update Operations
-- ============================================================================

/-- Replace the engine at `localId` in a node's engine map.
    If `localId` is not present, the node is unchanged. -/
def Node.setEngine (n : Node) (localId : Nat) (se : SomeEngine) : Node :=
  { n with engines := n.engines.map fun p =>
      if p.1 == localId then (localId, se) else p }

@[simp] lemma Node.setEngine_id (n : Node) (localId : Nat) (se : SomeEngine) :
    (n.setEngine localId se).id = n.id := rfl

/-- Update the engine at a given address in the system state. -/
def SystemState.updateEngineAt (κ : SystemState) (addr : Address)
    (se : SomeEngine) : SystemState :=
  { κ with nodes := κ.nodes.map fun n =>
      if n.id == addr.nodeId then n.setEngine addr.engineId se else n }

@[simp] lemma SystemState.updateEngineAt_messages (κ : SystemState)
    (addr : Address) (se : SomeEngine) :
    (κ.updateEngineAt addr se).messages = κ.messages := rfl

@[simp] lemma SystemState.updateEngineAt_nextId (κ : SystemState)
    (addr : Address) (se : SomeEngine) :
    (κ.updateEngineAt addr se).nextId = κ.nextId := rfl

-- ── BEq helper ──

private lemma beq_false_of_ne [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) :
    (a == b) = false := by
  match h' : a == b with
  | true => exact absurd (eq_of_beq h') h
  | false => rfl

-- ── List-level helpers for setEngine ──

private lemma map_find_setEngine_self (engines : EngineMap) (id : Nat)
    (se : SomeEngine) :
    engines.find? (fun p => p.1 == id) ≠ none →
    (engines.map fun p => if p.1 == id then (id, se) else p).find?
      (fun p => p.1 == id) = some (id, se) := by
  intro h
  induction engines with
  | nil => exact absurd rfl h
  | cons e es ih =>
    simp only [List.map_cons, List.find?_cons]
    match he : e.1 == id with
    | true =>
      simp only [he, ↓reduceIte, beq_self_eq_true]
    | false =>
      simp only [he, ↓reduceIte, Bool.false_eq_true]
      simp only [List.find?_cons, he, Bool.false_eq_true, ↓reduceIte] at h
      exact ih h

private lemma map_find_setEngine_ne (engines : EngineMap) (id id' : Nat)
    (se : SomeEngine) (h : id' ≠ id) :
    (engines.map fun p => if p.1 == id then (id, se) else p).find?
      (fun p => p.1 == id') = engines.find? (fun p => p.1 == id') := by
  induction engines with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.find?_cons]
    match he : e.1 == id with
    | true =>
      simp only [he, ↓reduceIte]
      have hne : (id == id') = false := beq_false_of_ne (Ne.symm h)
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have : (e.1 == id') = false := by
        rw [eq_of_beq he]; exact beq_false_of_ne (Ne.symm h)
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact ih
    | false =>
      match he' : e.1 == id' with
      | true => rfl
      | false => exact ih

-- ── System-level engineAt after updateEngineAt ──

/-- `engineAt` traversal for `updateEngineAt`: induction on the node list. -/
private lemma engineAt_updateEngineAt_aux (nodes : List Node)
    (nodeId engId : Nat) (se : SomeEngine) (targetNodeId targetEngId : Nat) :
    (match (nodes.map fun n =>
        if n.id == nodeId then n.setEngine engId se else n).find?
        (fun n => n.id == targetNodeId) with
      | some node => node.getEngine targetEngId
      | none => none) =
    if nodeId == targetNodeId then
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => (node.setEngine engId se).getEngine targetEngId
        | none => none)
    else
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => node.getEngine targetEngId
        | none => none) := by
  induction nodes with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.find?_cons]
    match hn : n.id == nodeId with
    | true =>
      simp only [hn, ↓reduceIte]
      match ht : n.id == targetNodeId with
      | true =>
        have hnt : (nodeId == targetNodeId) = true := by
          have := eq_of_beq hn; have := eq_of_beq ht; subst_vars
          exact beq_self_eq_true _
        simp [hnt]
      | false => exact ih
    | false =>
      match ht : n.id == targetNodeId with
      | true =>
        match hnt : nodeId == targetNodeId with
        | true =>
          exfalso
          have := eq_of_beq hnt; have := eq_of_beq ht; subst_vars
          simp at hn
        | false => rfl
      | false => exact ih

/-- After updating the engine at `addr` to `se`, looking up `addr` yields `se`,
    provided the engine existed before. -/
theorem engineAt_updateEngineAt_self (κ : SystemState) (addr : Address)
    (se : SomeEngine) (h : ∃ old, κ.engineAt addr = some old) :
    (κ.updateEngineAt addr se).engineAt addr = some se := by
  obtain ⟨old, hold⟩ := h
  simp only [SystemState.engineAt, SystemState.updateEngineAt] at *
  rw [engineAt_updateEngineAt_aux]
  simp only [beq_self_eq_true, ↓reduceIte]
  cases hfind : κ.nodes.find? (fun n => n.id == addr.nodeId) with
  | none => rw [hfind] at hold; simp at hold
  | some node =>
    rw [hfind] at hold
    simp only [Node.getEngine, Node.setEngine] at *
    rw [map_find_setEngine_self]
    · simp
    · intro habs; simp [habs] at hold

/-- Updating the engine at `addr` does not affect lookups at a different address. -/
theorem engineAt_updateEngineAt_ne (κ : SystemState) (addr addr' : Address)
    (se : SomeEngine) (h : addr' ≠ addr) :
    (κ.updateEngineAt addr se).engineAt addr' = κ.engineAt addr' := by
  simp only [SystemState.engineAt, SystemState.updateEngineAt] at *
  rw [engineAt_updateEngineAt_aux]
  match hnode : addr.nodeId == addr'.nodeId with
  | true =>
    simp only [hnode, ↓reduceIte]
    cases hfind : κ.nodes.find? (fun n => n.id == addr'.nodeId) with
    | none => rfl
    | some node =>
      simp only [Node.getEngine, Node.setEngine]
      rw [map_find_setEngine_ne]
      intro heq
      exact absurd (show addr' = addr by
        rcases addr with ⟨n1, e1⟩; rcases addr' with ⟨n2, e2⟩
        simp only [Address.mk.injEq]; dsimp only at *
        exact ⟨(eq_of_beq hnode).symm, heq⟩) h
  | false =>
    simp [hnode]

-- ============================================================================
-- § Engine Removal Operations
-- ============================================================================

/-- Remove the engine at `localId` from a node's engine map. -/
def Node.removeEngine (n : Node) (localId : Nat) : Node :=
  { n with engines := n.engines.filter fun p => !(p.1 == localId) }

@[simp] lemma Node.removeEngine_id (n : Node) (localId : Nat) :
    (n.removeEngine localId).id = n.id := rfl

/-- Remove the engine at a given address from the system state. -/
def SystemState.removeEngineAt (κ : SystemState) (addr : Address) : SystemState :=
  { κ with nodes := κ.nodes.map fun n =>
      if n.id == addr.nodeId then n.removeEngine addr.engineId else n }

@[simp] lemma SystemState.removeEngineAt_messages (κ : SystemState)
    (addr : Address) :
    (κ.removeEngineAt addr).messages = κ.messages := rfl

@[simp] lemma SystemState.removeEngineAt_nextId (κ : SystemState)
    (addr : Address) :
    (κ.removeEngineAt addr).nextId = κ.nextId := rfl

-- ── List-level helpers for removeEngine ──

private lemma filter_find_removeEngine_self (engines : EngineMap) (id : Nat) :
    (engines.filter fun p => !(p.1 == id)).find? (fun p => p.1 == id) = none := by
  induction engines with
  | nil => simp
  | cons e es ih =>
    simp only [List.filter_cons]
    match he : e.1 == id with
    | true =>
      simp only [he, Bool.not_true, ↓reduceIte]
      exact ih
    | false =>
      simp only [he, Bool.not_false, ↓reduceIte, List.find?_cons, he]
      exact ih

private lemma filter_find_removeEngine_ne (engines : EngineMap) (id id' : Nat)
    (h : id' ≠ id) :
    (engines.filter fun p => !(p.1 == id)).find? (fun p => p.1 == id') =
    engines.find? (fun p => p.1 == id') := by
  induction engines with
  | nil => simp
  | cons e es ih =>
    simp only [List.filter_cons, List.find?_cons]
    match he : e.1 == id with
    | true =>
      simp only [he, Bool.not_true, ↓reduceIte]
      have : (e.1 == id') = false := by
        rw [eq_of_beq he]; exact beq_false_of_ne (Ne.symm h)
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact ih
    | false =>
      simp only [he, Bool.not_false, ↓reduceIte, List.find?_cons]
      match he' : e.1 == id' with
      | true => simp only [he']
      | false =>
        simp only [he', Bool.false_eq_true, ↓reduceIte]
        exact ih

-- ── System-level engineAt after removeEngineAt ──

/-- `engineAt` traversal for `removeEngineAt`: induction on the node list. -/
private lemma engineAt_removeEngineAt_aux (nodes : List Node)
    (nodeId engId : Nat) (targetNodeId targetEngId : Nat) :
    (match (nodes.map fun n =>
        if n.id == nodeId then n.removeEngine engId else n).find?
        (fun n => n.id == targetNodeId) with
      | some node => node.getEngine targetEngId
      | none => none) =
    if nodeId == targetNodeId then
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => (node.removeEngine engId).getEngine targetEngId
        | none => none)
    else
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => node.getEngine targetEngId
        | none => none) := by
  induction nodes with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.find?_cons]
    match hn : n.id == nodeId with
    | true =>
      simp only [hn, ↓reduceIte]
      match ht : n.id == targetNodeId with
      | true =>
        have hnt : (nodeId == targetNodeId) = true := by
          have := eq_of_beq hn; have := eq_of_beq ht
          subst_vars; exact beq_self_eq_true _
        simp [hnt]
      | false => exact ih
    | false =>
      match ht : n.id == targetNodeId with
      | true =>
        match hnt : nodeId == targetNodeId with
        | true =>
          exfalso
          have := eq_of_beq hnt; have := eq_of_beq ht; subst_vars
          simp at hn
        | false => rfl
      | false => exact ih

/-- After removing the engine at `addr`, looking up `addr` yields `none`. -/
theorem engineAt_removeEngineAt_self (κ : SystemState) (addr : Address) :
    (κ.removeEngineAt addr).engineAt addr = none := by
  simp only [SystemState.engineAt, SystemState.removeEngineAt]
  rw [engineAt_removeEngineAt_aux]
  simp only [beq_self_eq_true, ↓reduceIte]
  cases hfind : κ.nodes.find? (fun n => n.id == addr.nodeId) with
  | none => rfl
  | some node =>
    simp only [Node.getEngine, Node.removeEngine]
    rw [filter_find_removeEngine_self]
    simp

/-- Removing the engine at `addr` does not affect lookups at a different address. -/
theorem engineAt_removeEngineAt_ne (κ : SystemState) (addr addr' : Address)
    (h : addr' ≠ addr) :
    (κ.removeEngineAt addr).engineAt addr' = κ.engineAt addr' := by
  simp only [SystemState.engineAt, SystemState.removeEngineAt]
  rw [engineAt_removeEngineAt_aux]
  match hnode : addr.nodeId == addr'.nodeId with
  | true =>
    simp only [hnode, ↓reduceIte]
    cases hfind : κ.nodes.find? (fun n => n.id == addr'.nodeId) with
    | none => rfl
    | some node =>
      simp only [Node.getEngine, Node.removeEngine]
      rw [filter_find_removeEngine_ne]
      intro heq
      exact absurd (show addr' = addr by
        rcases addr with ⟨n1, e1⟩; rcases addr' with ⟨n2, e2⟩
        simp only [Address.mk.injEq]; dsimp only at *
        exact ⟨(eq_of_beq hnode).symm, heq⟩) h
  | false =>
    simp [hnode]

end MailboxActors
