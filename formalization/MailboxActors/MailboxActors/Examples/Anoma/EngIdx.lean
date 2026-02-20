import MailboxActors.Examples.Anoma.AnomaTypes
import Mathlib.Data.Fintype.Basic

/-!
# Engine Index — Anoma Engine Types

The finite index type enumerating all Anoma engine types,
grouped into four subsystems: Ordering, Identity, Network,
and Infrastructure.
-/

namespace MailboxActors.Examples.Anoma

/-- The Anoma engine types. -/
inductive AnomaIdx where
  -- Ordering (3)
  | txOrdering | shard | executor
  -- Identity (8)
  | identity | commitment | decryption
  | verification | encryption
  | signDeleg | readDeleg | nameRegistry
  -- Network (6)
  | router | transport | protocol
  | connection | peerRegistry | pubsub
  -- Infrastructure (6)
  | ticker | wallClock | logging
  | kvStore | tsStore | storage
  deriving DecidableEq, Repr

instance : Fintype AnomaIdx where
  elems := { .txOrdering, .shard, .executor,
             .identity, .commitment, .decryption,
             .verification, .encryption,
             .signDeleg, .readDeleg, .nameRegistry,
             .router, .transport, .protocol,
             .connection, .peerRegistry, .pubsub,
             .ticker, .wallClock, .logging,
             .kvStore, .tsStore, .storage }
  complete x := by cases x <;> simp

end MailboxActors.Examples.Anoma
