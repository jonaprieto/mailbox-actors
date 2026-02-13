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

/-- After updating the engine at `addr` to `se`, looking up `addr` yields `se`,
    provided the engine existed before. -/
theorem engineAt_updateEngineAt_self (κ : SystemState) (addr : Address)
    (se : SomeEngine) (h : ∃ old, κ.engineAt addr = some old) :
    (κ.updateEngineAt addr se).engineAt addr = some se := by
  sorry

/-- Updating the engine at `addr` does not affect lookups at a different address. -/
theorem engineAt_updateEngineAt_ne (κ : SystemState) (addr addr' : Address)
    (se : SomeEngine) (h : addr' ≠ addr) :
    (κ.updateEngineAt addr se).engineAt addr' = κ.engineAt addr' := by
  sorry

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

/-- After removing the engine at `addr`, looking up `addr` yields `none`. -/
theorem engineAt_removeEngineAt_self (κ : SystemState) (addr : Address) :
    (κ.removeEngineAt addr).engineAt addr = none := by
  sorry

/-- Removing the engine at `addr` does not affect lookups at a different address. -/
theorem engineAt_removeEngineAt_ne (κ : SystemState) (addr addr' : Address)
    (h : addr' ≠ addr) :
    (κ.removeEngineAt addr).engineAt addr' = κ.engineAt addr' := by
  sorry

end MailboxActors
