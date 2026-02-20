import MailboxActors.Examples.Anoma.EngIdx

/-!
# Ticker Engine — Types

A simple counter engine used as a reference example. Supports
increment, query, and count-reply messages.
-/

namespace MailboxActors.Examples.Anoma.Infra

/-- Messages for the ticker engine.
- `increment`: Increment the counter.
- `getCount`: Query the current count.
- `count`: Reply with the current count value. -/
inductive TickerMsg where
  | increment : TickerMsg
  | getCount : TickerMsg
  | count : Nat → TickerMsg
  deriving DecidableEq, BEq

abbrev TickerCfg := Unit

/-- Local state for the ticker engine.
- `counter`: The current count value. -/
structure TickerState where
  counter : Nat

end MailboxActors.Examples.Anoma.Infra
