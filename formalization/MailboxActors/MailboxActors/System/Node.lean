/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Engine.Engine

/-!
# Nodes

Paper Definition 19.
-/

namespace MailboxActors

variable [EngineSpec]

/-- An existentially-typed engine: we know it has *some* engine type index
    but the index is packed inside. -/
structure SomeEngine where
  idx : EngineSpec.EngIdx
  engine : Engine idx

/-- An engine map maps local identifiers to engine instances. -/
abbrev EngineMap := List (Nat × SomeEngine)

/-- A node is a triple `(id, engineMap, plugins)`.  Paper Definition 19. -/
structure Node where
  id : Nat
  engines : EngineMap

/-- Look up an engine by its local identifier within a node. -/
def Node.getEngine (n : Node) (localId : Nat) : Option SomeEngine :=
  (n.engines.find? (fun p => p.1 == localId)).map (·.2)

end MailboxActors
