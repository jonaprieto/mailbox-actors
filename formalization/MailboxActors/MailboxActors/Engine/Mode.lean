/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Basic

/-!
# Engine Mode

Paper Definition 7.
-/

namespace MailboxActors

/-- Operational mode of an engine. Fixed at creation, opaque to the engine. -/
inductive EngineMode where
  | process : EngineMode
  | mail : EngineMode
  deriving DecidableEq, Repr

end MailboxActors
