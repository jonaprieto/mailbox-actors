import MailboxActors.Examples.Anoma.EngIdx

/-!
# WallClock Engine — Types

The wall-clock engine provides real-time clock functionality.
It tracks the current epoch and responds to time queries.
-/

namespace MailboxActors.Examples.Anoma.Infra

variable (A : AnomaTypes)

/-- Messages for the wall-clock engine.
- `getTime`: Query the current time.
- `timeReply`: Response with the current epoch. -/
inductive WallClockMsg where
  | getTime : WallClockMsg
  | timeReply : A.Epoch → WallClockMsg
  deriving DecidableEq, BEq

abbrev WallClockCfg := Unit

/-- Local state for the wall-clock engine.
- `currentEpoch`: The last known epoch value. -/
structure WallClockState where
  currentEpoch : A.Epoch

end MailboxActors.Examples.Anoma.Infra
