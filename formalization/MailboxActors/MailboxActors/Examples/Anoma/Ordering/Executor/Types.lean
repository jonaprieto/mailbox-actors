import MailboxActors.Examples.Anoma.EngIdx

/-!
# Executor Engine — Types

Each executor is spawned by the mempool worker to execute a single
transaction. The executor receives read replies from shards, steps
through the transaction program, and sends write/read requests back
to shards. When execution completes, it notifies the mempool worker.
-/

namespace MailboxActors.Examples.Anoma.Ordering

variable (A : AnomaTypes)

/-- Messages for the executor engine.

- `readReply`: A shard delivers the value for a previously requested
  key at a given fingerprint. The executor uses this to step its
  program forward. -/
inductive ExecutorMsg where
  | readReply : A.KVSKey → A.KVSDatum → ExecutorMsg
  deriving DecidableEq, BEq

/-- Configuration for the executor engine.
    Fixed at spawn time by the txOrdering engine.

- `fingerprint`: The transaction's position in the ordering.
- `executable`: The transaction program to execute.
- `lazyReadKeys`: Keys that the transaction may read.
- `eagerReadKeys`: Keys that the transaction will definitely read.
- `willWriteKeys`: Keys that the transaction will definitely write.
- `mayWriteKeys`: Keys that the transaction may write. -/
structure ExecutorCfg where
  fingerprint : A.TxFingerprint
  executable : A.Executable
  lazyReadKeys : List A.KVSKey
  eagerReadKeys : List A.KVSKey
  willWriteKeys : List A.KVSKey
  mayWriteKeys : List A.KVSKey

/-- Local state for the executor engine.

- `programState`: The current state of the transaction program.
- `completedReads`: Keys for which read values have been received.
- `completedWrites`: Keys for which write operations have been sent. -/
structure ExecutorState where
  programState : A.ProgramState
  completedReads : List A.KVSKey
  completedWrites : List A.KVSKey

end MailboxActors.Examples.Anoma.Ordering
