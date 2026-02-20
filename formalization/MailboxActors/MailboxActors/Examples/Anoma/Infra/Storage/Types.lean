import MailboxActors.Examples.Anoma.EngIdx

/-!
# Storage Engine — Types

The distributed storage engine manages chunk-based object storage
using convergent encryption and Merkle-tree organization.
-/

namespace MailboxActors.Examples.Anoma.Infra

variable (A : AnomaTypes)

/-- Messages for the distributed storage engine.
- `chunkGet`: Request a chunk by ID.
- `chunkGetReply`: Response with chunk lookup result.
- `chunkPut`: Store a chunk.
- `chunkPutReply`: Confirmation of chunk storage. -/
inductive StorageMsg where
  | chunkGet : A.ChunkID → StorageMsg
  | chunkGetReply : A.ChunkID → Bool → StorageMsg
  | chunkPut : A.ChunkID → A.Chunk → StorageMsg
  | chunkPutReply : A.ChunkID → Bool → StorageMsg
  deriving DecidableEq, BEq

abbrev StorageCfg := Unit

/-- Local state for the distributed storage engine.
- `chunkCount`: Number of stored chunks. -/
structure StorageState where
  chunkCount : Nat

end MailboxActors.Examples.Anoma.Infra
