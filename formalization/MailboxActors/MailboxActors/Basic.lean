import Mathlib.Data.Fintype.Basic

/-!
# Basic Definitions

The engine type index `EngIdx`, addresses, and the indexed type families
that parameterise the entire formalization.
-/

namespace MailboxActors

-- ============================================================================
-- § Address
-- ============================================================================

/-- An address identifies an engine as a `(nodeId, engineId)` pair. -/
structure Address where
  nodeId : Nat
  engineId : Nat
  deriving DecidableEq, Repr, BEq, Hashable

-- ============================================================================
-- § Engine Specification (the parametric context)
-- ============================================================================

/-- The system is parametric over a finite type of engine indices and
    associated type families. -/
class EngineSpec where
  /-- Finite type of engine type indices (`𝕀`). -/
  EngIdx : Type
  [fintype : Fintype EngIdx]
  [decEq : DecidableEq EngIdx]
  /-- Message interface for engine type `i` (`Msg_i`). -/
  MsgType : EngIdx → Type
  /-- Type-specific configuration data (`C_i`). -/
  CfgData : EngIdx → Type
  /-- Type-specific local state (`L_i`). -/
  LocalState : EngIdx → Type
  /-- Mailbox contains predicate: used for mDequeue. -/
  mailboxContains : {i : EngIdx} → LocalState i → MsgType i → Prop
  /-- Mailbox remove operation: used for mDequeue. -/
  mailboxRemove : {i : EngIdx} → LocalState i → MsgType i → LocalState i
  /-- Unwrap message payload: relates mailbox message to processing message. -/
  unwrap : {i j : EngIdx} → MsgType i → Option (MsgType j)

attribute [instance] EngineSpec.fintype EngineSpec.decEq

end MailboxActors
