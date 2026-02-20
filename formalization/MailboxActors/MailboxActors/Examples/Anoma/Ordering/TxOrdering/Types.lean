import MailboxActors.Examples.Anoma.EngIdx

/-!
# TxOrdering Engine (Mempool Worker) — Types

The transaction-ordering engine coordinates transaction submission,
lock acquisition, and executor lifecycle. It maintains a gensym-based
fingerprint counter for transaction ordering.
-/

namespace MailboxActors.Examples.Anoma.Ordering

variable (A : AnomaTypes)

/-- Messages for the transaction-ordering engine.

- `submitTx`: A new transaction arrives with a fingerprint and executable.
  The worker assigns it a position in the ordering via the gensym counter,
  sends lock-acquire requests to relevant shards, and spawns an executor.
- `lockAcquired`: A shard confirms that a lock has been acquired for a
  given transaction and key.
- `executorFinished`: An executor reports that a transaction has completed. -/
inductive TxOrderingMsg where
  | submitTx : A.TxFingerprint → A.Executable → TxOrderingMsg
  | lockAcquired : A.TxFingerprint → A.KVSKey → TxOrderingMsg
  | executorFinished : A.TxFingerprint → TxOrderingMsg
  deriving DecidableEq, BEq

/-- Configuration for the transaction-ordering engine.

- `keyToShard`: Maps each KVS key to the shard index responsible for it.
  This determines which shard receives lock-acquire requests for a given key. -/
structure TxOrderingCfg where
  keyToShard : A.KVSKey → Nat

/-- Local state for the transaction-ordering engine.

- `nextFingerprint`: Gensym counter for assigning unique transaction
  fingerprints. Incremented on each `submitTx` via `A.fingerprintSucc`.
- `pendingLocks`: Transaction fingerprints awaiting lock confirmation
  from shards. Entries are added on `submitTx` and removed when all
  locks for a transaction have been acquired. -/
structure TxOrderingState where
  nextFingerprint : A.TxFingerprint
  pendingLocks : List A.TxFingerprint

end MailboxActors.Examples.Anoma.Ordering
