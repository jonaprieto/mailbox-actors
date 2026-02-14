import MailboxActors.Engine.Status
import MailboxActors.Engine.Config
import MailboxActors.Engine.Env
import MailboxActors.Engine.Behaviour

/-!
# Engine
-/

namespace MailboxActors

variable [EngineSpec]

/-- An engine of type `i` is a 5-tuple `⟨Msg_i, b, o, c, s⟩`.

    The behaviour field uses `WellFormedBehaviour`, bundling the guard list
    with a proof of non-overlapping guards. -/
structure Engine (i : EngineSpec.EngIdx) where
  behaviour : WellFormedBehaviour i
  status : EngineStatus i
  config : EngineConfig i
  env : EngineEnv i

/-- The message interface is determined by the engine type index. -/
def Engine.msgType (_e : Engine i) : Type := EngineSpec.MsgType i

/-- Retrieve the operational mode from the engine's configuration. -/
def Engine.mode (e : Engine i) : EngineMode := e.config.mode

end MailboxActors
