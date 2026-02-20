import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Storage Engine — Behaviour

The storage engine manages chunk-based object storage. It processes
chunk get and put requests, maintaining a count of stored chunks.
-/

namespace MailboxActors.Examples.Anoma.Infra

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

@[simp] def storageChunkGetGuard
    (inp : @GuardInput (S A) AnomaIdx.storage) :
    Option A.ChunkID :=
  match @GuardInput.msg (S A) _ inp with
  | .chunkGet cid => some cid
  | _ => none

/-- Action for `chunkGet`: in a full implementation, would look up the
    chunk and reply with it. -/
def storageChunkGetAction
    (w : A.ChunkID)
    (inp : @GuardInput (S A) AnomaIdx.storage)
    (_ : storageChunkGetGuard A inp = some w) :
    @Effect (S A) AnomaIdx.storage :=
  letI := S A; Effect.noop

@[simp] def storageChunkPutGuard
    (inp : @GuardInput (S A) AnomaIdx.storage) :
    Option (A.ChunkID × A.Chunk) :=
  match @GuardInput.msg (S A) _ inp with
  | .chunkPut cid chunk => some (cid, chunk)
  | _ => none

/-- Action for `chunkPut`: store the chunk and increment the count. -/
def storageChunkPutAction
    (w : A.ChunkID × A.Chunk)
    (inp : @GuardInput (S A) AnomaIdx.storage)
    (_ : storageChunkPutGuard A inp = some w) :
    @Effect (S A) AnomaIdx.storage :=
  letI := S A
  let env := inp.env
  Effect.update { env with
    localState := { chunkCount := env.localState.chunkCount + 1 } }

def storageActions : @Behaviour (S A) AnomaIdx.storage :=
  letI := S A
  [ { Witness := A.ChunkID
      guard := storageChunkGetGuard A
      action := storageChunkGetAction A }
  , { Witness := A.ChunkID × A.Chunk
      guard := storageChunkPutGuard A
      action := storageChunkPutAction A } ]

private theorem storageNonOverlapping :
    @NonOverlappingGuards (S A) _ (storageActions A) := by
  letI := S A; intro inp
  simp only [storageActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def storageBehaviour : @WellFormedBehaviour (S A) AnomaIdx.storage :=
  letI := S A
  { actions := storageActions A
    nonOverlapping := storageNonOverlapping A }

end MailboxActors.Examples.Anoma.Infra
