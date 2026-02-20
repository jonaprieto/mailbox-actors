import MailboxActors.Examples.Anoma.EngIdx

/-!
# Infrastructure Subsystem — Message, Config, and State Types

Engines: `ticker`, `wallClock`, `logging`, `kvStore`, `tsStore`, `storage`.
-/

namespace MailboxActors.Examples.Anoma.Infra

variable (A : AnomaTypes)

-- ============================================================================
-- § Ticker
-- ============================================================================

/-- Messages for the ticker engine. -/
inductive TickerMsg where
  | increment : TickerMsg
  | getCount  : TickerMsg
  | count     : Nat → TickerMsg
  deriving DecidableEq, BEq

/-- Configuration for the ticker engine. -/
abbrev TickerCfg := Unit

/-- Local state for the ticker engine. -/
structure TickerState where
  counter : Nat

-- ============================================================================
-- § WallClock
-- ============================================================================

/-- Messages for the wall-clock engine. -/
inductive WallClockMsg where
  | getTime    : WallClockMsg
  | timeReply  : A.Epoch → WallClockMsg
  deriving DecidableEq, BEq

/-- Configuration for the wall-clock engine. -/
abbrev WallClockCfg := Unit

/-- Local state for the wall-clock engine. -/
structure WallClockState where
  currentEpoch : A.Epoch

-- ============================================================================
-- § Logging
-- ============================================================================

/-- Messages for the logging engine. -/
inductive LoggingMsg where
  | append : String → LoggingMsg
  deriving DecidableEq, BEq

/-- Configuration for the logging engine. -/
abbrev LoggingCfg := Unit

/-- Local state for the logging engine. -/
structure LoggingState where
  entries : List String
  position : Nat

-- ============================================================================
-- § KVStore (local key-value storage)
-- ============================================================================

/-- Messages for the key-value store engine. -/
inductive KVStoreMsg where
  | getReq    : A.StorageKey → KVStoreMsg
  | getReply  : A.StorageKey → Bool → KVStoreMsg
  | setReq    : A.StorageKey → A.StorageValue → KVStoreMsg
  | setReply  : Bool → KVStoreMsg
  | deleteReq : A.StorageKey → KVStoreMsg
  | deleteReply : Bool → KVStoreMsg
  deriving DecidableEq, BEq

/-- Configuration for the key-value store engine. -/
abbrev KVStoreCfg := Unit

/-- Local state for the key-value store engine. -/
structure KVStoreState where
  entryCount : Nat

-- ============================================================================
-- § TSStore (local time-series storage)
-- ============================================================================

/-- Messages for the time-series store engine. -/
inductive TSStoreMsg where
  | recordReq    : A.StorageKey → A.StorageValue → TSStoreMsg
  | recordReply  : Bool → TSStoreMsg
  | queryReq     : A.StorageKey → TSStoreMsg
  | queryReply   : A.StorageKey → Bool → TSStoreMsg
  | deleteReq    : A.StorageKey → TSStoreMsg
  | deleteReply  : Bool → TSStoreMsg
  deriving DecidableEq, BEq

/-- Configuration for the time-series store engine. -/
abbrev TSStoreCfg := Unit

/-- Local state for the time-series store engine. -/
structure TSStoreState where
  seriesCount : Nat

-- ============================================================================
-- § Storage (distributed chunk storage)
-- ============================================================================

/-- Messages for the distributed storage engine. -/
inductive StorageMsg where
  | chunkGet      : A.ChunkID → StorageMsg
  | chunkGetReply : A.ChunkID → Bool → StorageMsg
  | chunkPut      : A.ChunkID → A.Chunk → StorageMsg
  | chunkPutReply : A.ChunkID → Bool → StorageMsg
  deriving DecidableEq, BEq

/-- Configuration for the distributed storage engine. -/
abbrev StorageCfg := Unit

/-- Local state for the distributed storage engine. -/
structure StorageState where
  chunkCount : Nat

end MailboxActors.Examples.Anoma.Infra
