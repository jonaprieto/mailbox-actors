import MailboxActors.Examples.Anoma.EngIdx

/-!
# TSStore Engine — Types

The local time-series storage engine manages historical data
with record, query, and delete operations.
-/

namespace MailboxActors.Examples.Anoma.Infra

variable (A : AnomaTypes)

/-- Messages for the time-series store engine.
- `recordReq`: Record a key-value pair with timestamp.
- `recordReply`: Confirmation of record operation.
- `queryReq`: Query time-series data for a key.
- `queryReply`: Response with query result.
- `deleteReq`: Delete time-series data for a key.
- `deleteReply`: Confirmation of delete operation. -/
inductive TSStoreMsg where
  | recordReq : A.StorageKey → A.StorageValue → TSStoreMsg
  | recordReply : Bool → TSStoreMsg
  | queryReq : A.StorageKey → TSStoreMsg
  | queryReply : A.StorageKey → Bool → TSStoreMsg
  | deleteReq : A.StorageKey → TSStoreMsg
  | deleteReply : Bool → TSStoreMsg
  deriving DecidableEq, BEq

abbrev TSStoreCfg := Unit

/-- Local state for the time-series store engine.
- `seriesCount`: Number of stored time-series. -/
structure TSStoreState where
  seriesCount : Nat

end MailboxActors.Examples.Anoma.Infra
