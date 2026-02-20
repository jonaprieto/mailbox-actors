/-!
# Anoma Types — Opaque Type Bundle

Parametric type bundle for the Anoma protocol formalization.
All domain-specific types (crypto, identity, storage, network, time)
are kept opaque so the specification is independent of concrete
representations. Each field carries `DecidableEq` so that
message types can derive `DecidableEq`/`BEq`.
-/

namespace MailboxActors.Examples.Anoma

/-- Opaque type bundle for the Anoma protocol.
    Engines are parameterised over `AnomaTypes` so that the
    specification is representation-independent. -/
structure AnomaTypes where
  -- Crypto
  Signature       : Type
  Ciphertext      : Type
  Plaintext       : Type
  Signable        : Type
  -- Identity
  ExternalIdentity : Type
  Backend         : Type
  IdentityName    : Type
  -- Evidence (delegation / naming)
  SignEvidence    : Type
  ReadEvidence   : Type
  NameEvidence   : Type
  -- Ordering
  KVSKey          : Type
  KVSDatum        : Type
  TxFingerprint   : Type
  Executable      : Type
  ProgramState    : Type
  -- Storage
  StorageKey      : Type
  StorageValue    : Type
  ChunkID         : Type
  Chunk           : Type
  -- Network
  NodeID          : Type
  TransportAddr   : Type
  TopicID         : Type
  ByteString      : Type
  -- Time
  Epoch           : Type
  -- DecidableEq instances for all types
  [decEqSignature       : DecidableEq Signature]
  [decEqCiphertext      : DecidableEq Ciphertext]
  [decEqPlaintext       : DecidableEq Plaintext]
  [decEqSignable        : DecidableEq Signable]
  [decEqExternalIdentity : DecidableEq ExternalIdentity]
  [decEqBackend         : DecidableEq Backend]
  [decEqIdentityName    : DecidableEq IdentityName]
  [decEqSignEvidence    : DecidableEq SignEvidence]
  [decEqReadEvidence    : DecidableEq ReadEvidence]
  [decEqNameEvidence    : DecidableEq NameEvidence]
  [decEqKVSKey          : DecidableEq KVSKey]
  [decEqKVSDatum        : DecidableEq KVSDatum]
  [decEqTxFingerprint   : DecidableEq TxFingerprint]
  [decEqExecutable      : DecidableEq Executable]
  [decEqProgramState    : DecidableEq ProgramState]
  [decEqStorageKey      : DecidableEq StorageKey]
  [decEqStorageValue    : DecidableEq StorageValue]
  [decEqChunkID         : DecidableEq ChunkID]
  [decEqChunk           : DecidableEq Chunk]
  [decEqNodeID          : DecidableEq NodeID]
  [decEqTransportAddr   : DecidableEq TransportAddr]
  [decEqTopicID         : DecidableEq TopicID]
  [decEqByteString      : DecidableEq ByteString]
  [decEqEpoch           : DecidableEq Epoch]

-- Expose DecidableEq instances
attribute [instance] AnomaTypes.decEqSignature AnomaTypes.decEqCiphertext
  AnomaTypes.decEqPlaintext AnomaTypes.decEqSignable
  AnomaTypes.decEqExternalIdentity AnomaTypes.decEqBackend
  AnomaTypes.decEqIdentityName AnomaTypes.decEqSignEvidence
  AnomaTypes.decEqReadEvidence AnomaTypes.decEqNameEvidence
  AnomaTypes.decEqKVSKey AnomaTypes.decEqKVSDatum
  AnomaTypes.decEqTxFingerprint AnomaTypes.decEqExecutable
  AnomaTypes.decEqProgramState AnomaTypes.decEqStorageKey
  AnomaTypes.decEqStorageValue AnomaTypes.decEqChunkID
  AnomaTypes.decEqChunk AnomaTypes.decEqNodeID
  AnomaTypes.decEqTransportAddr AnomaTypes.decEqTopicID
  AnomaTypes.decEqByteString AnomaTypes.decEqEpoch

end MailboxActors.Examples.Anoma
