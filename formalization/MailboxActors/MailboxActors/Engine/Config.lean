import MailboxActors.Basic
import MailboxActors.Engine.Mode

/-!
# Engine Configuration
-/

namespace MailboxActors

variable [EngineSpec]

/-- Configuration of an engine of type `i`.
    Components: optional parent address, operational mode, type-specific data. -/
structure EngineConfig (i : EngineSpec.EngIdx) where
  parent : Option Address
  mode : EngineMode
  cfg : EngineSpec.CfgData i

end MailboxActors
