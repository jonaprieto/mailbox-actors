/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Basic

/-!
# Engine Lifecycle Status

Paper Definition 6.
-/

namespace MailboxActors

variable [EngineSpec]

/-- Engine lifecycle status, indexed by engine type.
    - `ready f`: accepting messages filtered by `f`
    - `busy m`: processing message `m`
    - `terminated`: stopped, awaiting cleanup -/
inductive EngineStatus (i : EngineSpec.EngIdx) where
  | ready (f : EngineSpec.MsgType i → Bool) : EngineStatus i
  | busy (m : EngineSpec.MsgType i) : EngineStatus i
  | terminated : EngineStatus i

end MailboxActors
