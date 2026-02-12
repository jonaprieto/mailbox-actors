/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.System.Node
import MailboxActors.Engine.Message

/-!
# System State

Paper Definition 20 and §3.7.
-/

namespace MailboxActors

variable [EngineSpec]

/-- System state `κ = (N, M, Ω)`.  Paper §3.7. -/
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

end MailboxActors
