/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Basic
import MailboxActors.Engine.Env

/-!
# Effect System
-/

namespace MailboxActors

variable [EngineSpec]

/-- Effects produced by behaviour evaluation.
    Each constructor corresponds to a system action. -/
inductive Effect (i : EngineSpec.EngIdx) where
  | noop : Effect i
  | send (j : EngineSpec.EngIdx) (target : Address)
         (payload : EngineSpec.MsgType j) : Effect i
  | update (env : EngineEnv i) : Effect i
  | spawn (j : EngineSpec.EngIdx) (cfg : EngineSpec.CfgData j)
          (env : EngineSpec.LocalState j) : Effect i
  | mfilter (f : EngineSpec.MsgType i → Bool) : Effect i
  | terminate : Effect i
  | chain (e₁ e₂ : Effect i) : Effect i

end MailboxActors
