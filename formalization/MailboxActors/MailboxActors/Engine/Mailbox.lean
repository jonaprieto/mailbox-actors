import MailboxActors.Engine.Engine
import MailboxActors.Engine.Message

/-!
# Mailbox Engine

A mailbox engine is a specialised engine whose:
- operational mode is `mail`
- parent reference points to the paired processing engine
- message interface wraps the processing engine's messages in `Append`
- default behaviour extracts payloads and stores them via `Update`
-/

namespace MailboxActors

variable [EngineSpec]

/-- Predicate: an engine is a mailbox engine when its mode is `mail`. -/
def Engine.isMailbox (e : Engine i) : Prop :=
  e.mode = EngineMode.mail

/-- Predicate: an engine is a processing engine when its mode is `process`. -/
def Engine.isProcessing (e : Engine i) : Prop :=
  e.mode = EngineMode.process

end MailboxActors
