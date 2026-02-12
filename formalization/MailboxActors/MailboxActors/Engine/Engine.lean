/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Engine.Status
import MailboxActors.Engine.Config
import MailboxActors.Engine.Env
import MailboxActors.Engine.Behaviour

/-!
# Engine

Paper Definitions 16–17.
-/

namespace MailboxActors

variable [EngineSpec]

/-- An engine of type `i` is a 5-tuple matching the paper's
    `⟨Msg_i, b, o, c, s⟩`.  Paper Definition 17. -/
structure Engine (i : EngineSpec.EngIdx) where
  behaviour : Behaviour i
  status : EngineStatus i
  config : EngineConfig i
  env : EngineEnv i

/-- The message interface is determined by the engine type index. -/
def Engine.msgType (_e : Engine i) : Type := EngineSpec.MsgType i

/-- Retrieve the operational mode from the engine's configuration. -/
def Engine.mode (e : Engine i) : EngineMode := e.config.mode

end MailboxActors
