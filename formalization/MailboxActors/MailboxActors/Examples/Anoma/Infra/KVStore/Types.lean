import MailboxActors.Examples.Anoma.EngIdx

/-!
# KVStore Engine — Types

The local key-value storage engine provides persistent state storage
with get, set, and delete operations.
-/

namespace MailboxActors.Examples.Anoma.Infra

variable (A : AnomaTypes)

/-- Messages for the key-value store engine.
- `getReq`: Request the value for a key.
- `getReply`: Response with lookup result.
- `setReq`: Set a key-value pair.
- `setReply`: Confirmation of set operation.
- `deleteReq`: Delete a key.
- `deleteReply`: Confirmation of delete operation. -/
inductive KVStoreMsg where
  | getReq : A.StorageKey → KVStoreMsg
  | getReply : A.StorageKey → Bool → KVStoreMsg
  | setReq : A.StorageKey → A.StorageValue → KVStoreMsg
  | setReply : Bool → KVStoreMsg
  | deleteReq : A.StorageKey → KVStoreMsg
  | deleteReply : Bool → KVStoreMsg
  deriving DecidableEq, BEq

abbrev KVStoreCfg := Unit

/-- Local state for the key-value store engine.
- `entryCount`: Number of stored entries. -/
structure KVStoreState where
  entryCount : Nat

end MailboxActors.Examples.Anoma.Infra
