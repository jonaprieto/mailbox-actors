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

end MailboxActors
