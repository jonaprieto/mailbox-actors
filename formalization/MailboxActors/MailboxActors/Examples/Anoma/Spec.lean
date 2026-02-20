import MailboxActors.Engine.Engine
import MailboxActors.Examples.Anoma.Ordering.Types
import MailboxActors.Examples.Anoma.Identity.Types
import MailboxActors.Examples.Anoma.Network.Types
import MailboxActors.Examples.Anoma.Infra.Types

/-!
# Anoma Engine Specification

Defines the type families `MsgType`, `CfgData`, `LocalState`
and the `EngineSpec` instance for `AnomaIdx`.
-/

namespace MailboxActors.Examples.Anoma

open Ordering Identity Network Infra

-- ============================================================================
-- § Type Families
-- ============================================================================

/-- Message type family for Anoma engines. -/
def AnomaSpec.MsgType (A : AnomaTypes) : AnomaIdx → Type
  -- Ordering
  | .txOrdering   => TxOrderingMsg A
  | .shard        => ShardMsg A
  | .executor     => ExecutorMsg A
  -- Identity
  | .identity     => IdentityMsg A
  | .commitment   => CommitmentMsg A
  | .decryption   => DecryptionMsg A
  | .verification => VerificationMsg A
  | .encryption   => EncryptionMsg A
  | .signDeleg    => SignDelegMsg A
  | .readDeleg    => ReadDelegMsg A
  | .nameRegistry => NameRegistryMsg A
  -- Network
  | .router       => RouterMsg A
  | .transport    => TransportMsg A
  | .protocol     => ProtocolMsg A
  | .connection   => ConnectionMsg A
  | .peerRegistry => PeerRegistryMsg A
  | .pubsub       => PubSubMsg A
  -- Infrastructure
  | .ticker       => TickerMsg
  | .wallClock    => WallClockMsg A
  | .logging      => LoggingMsg
  | .kvStore      => KVStoreMsg A
  | .tsStore      => TSStoreMsg A
  | .storage      => StorageMsg A

/-- Configuration data family for Anoma engines. -/
def AnomaSpec.CfgData (A : AnomaTypes) : AnomaIdx → Type
  | .txOrdering   => TxOrderingCfg A
  | .shard        => ShardCfg
  | .executor     => ExecutorCfg A
  | .identity     => IdentityCfg
  | .commitment   => CommitmentCfg A
  | .decryption   => DecryptionCfg A
  | .verification => VerificationCfg A
  | .encryption   => EncryptionCfg A
  | .signDeleg    => SignDelegCfg
  | .readDeleg    => ReadDelegCfg
  | .nameRegistry => NameRegistryCfg
  | .router       => RouterCfg A
  | .transport    => TransportCfg
  | .protocol     => ProtocolCfg
  | .connection   => ConnectionCfg A
  | .peerRegistry => PeerRegistryCfg
  | .pubsub       => PubSubCfg A
  | .ticker       => TickerCfg
  | .wallClock    => WallClockCfg
  | .logging      => LoggingCfg
  | .kvStore      => KVStoreCfg
  | .tsStore      => TSStoreCfg
  | .storage      => StorageCfg

/-- Local state family for Anoma engines. -/
def AnomaSpec.LocalState (A : AnomaTypes) : AnomaIdx → Type
  | .txOrdering   => TxOrderingState A
  | .shard        => ShardState A
  | .executor     => ExecutorState A
  | .identity     => IdentityState
  | .commitment   => CommitmentState
  | .decryption   => DecryptionState
  | .verification => VerificationState
  | .encryption   => EncryptionState
  | .signDeleg    => SignDelegState
  | .readDeleg    => ReadDelegState
  | .nameRegistry => NameRegistryState
  | .router       => RouterState
  | .transport    => TransportState
  | .protocol     => ProtocolState
  | .connection   => ConnectionState
  | .peerRegistry => PeerRegistryState
  | .pubsub       => PubSubState
  | .ticker       => TickerState
  | .wallClock    => WallClockState A
  | .logging      => LoggingState
  | .kvStore      => KVStoreState
  | .tsStore      => TSStoreState
  | .storage      => StorageState

-- ============================================================================
-- § Unwrap (same-type identity)
-- ============================================================================

/-- Unwrap: if sender and receiver have the same engine type, cast;
    otherwise `none`. -/
def AnomaSpec.unwrap (A : AnomaTypes) {i j : AnomaIdx}
    (m : AnomaSpec.MsgType A i) : Option (AnomaSpec.MsgType A j) :=
  if h : i = j then some (h ▸ m) else none

-- ============================================================================
-- § EngineSpec Instance
-- ============================================================================

/-- Anoma engine specification: 23 engine types with trivial mailbox
    semantics (all engines use FIFO pass-through mailboxes). -/
instance anomaEngineSpec (A : AnomaTypes) : EngineSpec where
  EngIdx := AnomaIdx
  MsgType := AnomaSpec.MsgType A
  CfgData := AnomaSpec.CfgData A
  LocalState := AnomaSpec.LocalState A
  mailboxContains := fun {_} _ _ => True
  mailboxRemove := fun {_} s _ => s
  unwrap := fun {_ _} m => AnomaSpec.unwrap A m

end MailboxActors.Examples.Anoma
