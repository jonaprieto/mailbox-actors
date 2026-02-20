import MailboxActors.Examples.Anoma.EngIdx

/-!
# Logging Engine — Types

The logging engine maintains an append-only log of string entries.
-/

namespace MailboxActors.Examples.Anoma.Infra

/-- Messages for the logging engine.
- `append`: Append a string entry to the log. -/
inductive LoggingMsg where
  | append : String → LoggingMsg
  deriving DecidableEq, BEq

abbrev LoggingCfg := Unit

/-- Local state for the logging engine.
- `entries`: The log entries.
- `position`: Current write position (= entries.length). -/
structure LoggingState where
  entries : List String
  position : Nat

end MailboxActors.Examples.Anoma.Infra
