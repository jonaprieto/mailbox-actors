/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Basic

/-!
# Execution Environment

Paper Definition 9.
-/

namespace MailboxActors

variable [EngineSpec]

/-- Execution environment of an engine of type `i`.
    Components: type-specific local state and an address book. -/
structure EngineEnv (i : EngineSpec.EngIdx) where
  localState : EngineSpec.LocalState i
  addressBook : String → Option Address

end MailboxActors
