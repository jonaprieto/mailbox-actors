import MailboxActors.Basic

/-!
# Engine Mode
-/

namespace MailboxActors

/-- Operational mode of an engine. Fixed at creation, opaque to the engine. -/
inductive EngineMode where
  | process : EngineMode
  | mail : EngineMode
  deriving DecidableEq, Repr

end MailboxActors
