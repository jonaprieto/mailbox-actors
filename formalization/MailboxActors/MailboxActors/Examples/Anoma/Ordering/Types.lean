import MailboxActors.Examples.Anoma.EngIdx

/-!
# Ordering Subsystem — Message, Config, and State Types

Engines: `txOrdering`, `shard`, `executor`.
-/

namespace MailboxActors.Examples.Anoma.Ordering

variable (A : AnomaTypes)

-- ============================================================================
-- § TxOrdering (mempool worker)
-- ============================================================================

/-- Messages for the transaction-ordering engine. -/
inductive TxOrderingMsg where
  | submitTx         : A.TxFingerprint → A.Executable → TxOrderingMsg
  | lockAcquired     : A.TxFingerprint → A.KVSKey → TxOrderingMsg
  | executorFinished  : A.TxFingerprint → TxOrderingMsg
  deriving DecidableEq, BEq

/-- Configuration for the transaction-ordering engine. -/
structure TxOrderingCfg where
  keyToShard : A.KVSKey → Nat

/-- Local state for the transaction-ordering engine. -/
structure TxOrderingState where
  nextFingerprint : A.TxFingerprint

-- ============================================================================
-- § Shard
-- ============================================================================

/-- Messages for the shard engine. -/
inductive ShardMsg where
  | acquireLock   : A.TxFingerprint → A.KVSKey → ShardMsg
  | readRequest   : A.TxFingerprint → A.KVSKey → ShardMsg
  | write         : A.TxFingerprint → A.KVSKey → A.KVSDatum → ShardMsg
  | updateSeenAll : A.TxFingerprint → ShardMsg
  deriving DecidableEq, BEq

/-- Configuration for the shard engine. -/
abbrev ShardCfg := Unit

/-- Local state for the shard engine.
    The shard manages a multi-version store keyed by transaction fingerprint. -/
structure ShardState where
  heardAllReads : A.TxFingerprint
  heardAllWrites : A.TxFingerprint

-- ============================================================================
-- § Executor
-- ============================================================================

/-- Messages for the executor engine. -/
inductive ExecutorMsg where
  | readReply : A.KVSKey → A.KVSDatum → ExecutorMsg
  deriving DecidableEq, BEq

/-- Configuration for the executor engine.
    Fixed at spawn time by the txOrdering engine. -/
structure ExecutorCfg where
  fingerprint : A.TxFingerprint
  executable : A.Executable

/-- Local state for the executor engine. -/
structure ExecutorState where
  programState : A.ProgramState

end MailboxActors.Examples.Anoma.Ordering
