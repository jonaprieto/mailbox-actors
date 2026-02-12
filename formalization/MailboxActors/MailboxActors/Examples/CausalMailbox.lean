/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Engine.Engine
import MailboxActors.Engine.Behaviour
import MailboxActors.Engine.Mailbox
import Mathlib.Data.Finset.Basic

/-!
# Example: Causal Delivery Mailbox for Pub/Sub

A concrete instantiation of `EngineSpec` for a distributed pub/sub system
with two engine types — a topic relay (FIFO mailbox) and a local broker
(causal-delivery mailbox). The broker's mailbox buffers messages whose
causal dependencies have not yet been delivered and releases them via
`Effect.chain` when all dependencies are met.
-/

namespace MailboxActors.Examples.CausalMailbox

-- ============================================================================
-- § Engine Type Indices
-- ============================================================================

/-- Two engine types: `relay` forwards between nodes, `broker` delivers
    to local subscribers with causal ordering. -/
inductive PubSubIdx where
  | relay  : PubSubIdx
  | broker : PubSubIdx
  deriving DecidableEq, Repr

instance : Fintype PubSubIdx where
  elems := {.relay, .broker}
  complete x := by cases x <;> simp

-- ============================================================================
-- § Message Types
-- ============================================================================

/-- Simplified hash type for message identification. -/
abbrev MsgHash := Nat

/-- A pub/sub topic message with causal dependency metadata. -/
structure TopicMsg where
  publisher : Address
  deps      : Finset MsgHash    -- hashes of causal predecessors
  content   : Nat               -- simplified payload
  sig       : Nat               -- simplified signature
  msgHash   : MsgHash           -- this message's own hash

-- ============================================================================
-- § Configuration Types
-- ============================================================================

/-- Relay configuration: signature validation parameters. -/
structure RelayConfig where
  maxEpoch : Nat
  deriving Repr

/-- Broker configuration: subscriber list. -/
structure BrokerConfig where
  subscribers : List Address
  deriving Repr

-- ============================================================================
-- § Local State Types
-- ============================================================================

/-- Relay local state: set of processed message hashes. -/
structure RelayState where
  processed : Finset MsgHash

/-- Causal delivery mailbox state. -/
structure CausalState where
  delivered : Finset MsgHash           -- hashes of delivered messages
  pending   : List (MsgHash × TopicMsg) -- buffered messages with unmet deps
  ready     : List TopicMsg            -- messages ready for delivery

/-- The empty initial state. -/
def CausalState.empty : CausalState :=
  { delivered := ∅, pending := [], ready := [] }

-- ============================================================================
-- § Concrete Type Families
-- ============================================================================

/-- Message interface: both engine types use `TopicMsg`. -/
def PubSub.MsgType : PubSubIdx → Type
  | .relay  => TopicMsg
  | .broker => TopicMsg

/-- Configuration data per engine type. -/
def PubSub.CfgData : PubSubIdx → Type
  | .relay  => RelayConfig
  | .broker => BrokerConfig

/-- Local state per engine type. -/
def PubSub.LocalState : PubSubIdx → Type
  | .relay  => RelayState
  | .broker => CausalState

-- ============================================================================
-- § EngineSpec Instance
-- ============================================================================

/-- Concrete engine specification for the pub/sub system. -/
instance PubSubSpec : EngineSpec where
  EngIdx     := PubSubIdx
  MsgType    := PubSub.MsgType
  CfgData    := PubSub.CfgData
  LocalState := PubSub.LocalState

-- ============================================================================
-- § Causal Mailbox Guard and Action
-- ============================================================================

/-- Check whether all dependencies of a message are in the delivered set. -/
def dependenciesMet (msg : TopicMsg) (delivered : Finset MsgHash) : Bool :=
  decide (msg.deps ⊆ delivered)

/-- Find pending messages whose dependencies are now met. -/
def findCascade (pending : List (MsgHash × TopicMsg))
    (delivered : Finset MsgHash) : List TopicMsg :=
  (pending.filter (fun (_, m) => dependenciesMet m delivered)).map (·.2)

/-- Remove cascaded messages from the pending list. -/
def removeCascaded (pending : List (MsgHash × TopicMsg))
    (delivered : Finset MsgHash) : List (MsgHash × TopicMsg) :=
  pending.filter (fun (_, m) => !dependenciesMet m delivered)

/-- The causal broker guard: always matches (extracts the payload). -/
def causalGuard : GuardInput PubSubIdx.broker → Bool :=
  fun _ => true

/-- The causal broker action: branches on dependency satisfaction.
    - Dependencies met: store in ready, record hash, cascade pending.
    - Dependencies not met: buffer in pending.

    Uses `Effect.chain` for the cascade. -/
def causalAction (inp : GuardInput PubSubIdx.broker) (_ : causalGuard inp = true) :
    Effect PubSubIdx.broker :=
  let msg : TopicMsg := inp.msg
  let q : CausalState := inp.env.localState
    if dependenciesMet msg q.delivered then
      -- Dependencies satisfied: deliver and cascade
      let newDelivered := q.delivered ∪ {msg.msgHash}
      let cascaded := findCascade q.pending newDelivered
      let remainingPending := removeCascaded q.pending newDelivered
      Effect.chain
        -- First: add this message to ready, update delivered set
        (Effect.update ⟨
          { delivered := newDelivered
            pending := q.pending
            ready := q.ready ++ [msg] },
          inp.env.addressBook ⟩)
        -- Second: move cascaded messages from pending to ready
        (if cascaded.isEmpty then
           Effect.noop
         else
           Effect.update ⟨
             { delivered := newDelivered
               pending := remainingPending
               ready := q.ready ++ [msg] ++ cascaded },
             inp.env.addressBook ⟩)
    else
      -- Dependencies not satisfied: buffer
      Effect.update ⟨
        { delivered := q.delivered
          pending := q.pending ++ [(msg.msgHash, msg)]
          ready := q.ready },
        inp.env.addressBook ⟩

/-- The causal broker guarded action. -/
def causalGuardedAction : GuardedAction PubSubIdx.broker :=
  { guard := causalGuard, action := causalAction }

/-- The underlying action list for the causal delivery mailbox. -/
def causalActions : Behaviour PubSubIdx.broker :=
  [causalGuardedAction]

/-- Non-overlapping guards hold trivially (single guard). -/
private theorem causalNonOverlapping : NonOverlappingGuards causalActions := by
  intro inp
  simp [causalActions, causalGuardedAction, causalGuard]

/-- Well-formed behaviour for the causal delivery mailbox: a single
    guarded action bundled with its non-overlapping proof. -/
def causalBehaviour : WellFormedBehaviour PubSubIdx.broker :=
  { actions := causalActions
    nonOverlapping := causalNonOverlapping }

end MailboxActors.Examples.CausalMailbox
