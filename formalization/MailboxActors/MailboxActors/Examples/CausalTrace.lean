import MailboxActors.Examples.CausalMailbox
import MailboxActors.Properties.TypePreservation

/-!
# Causal Trace Consistency

Proof that the CausalInvariant is preserved globally across system execution.
-/

namespace MailboxActors.Examples.CausalMailbox

-- Use the concrete PubSubSpec instance
open PubSubSpec

/-- The global causal invariant:
    For every broker in the system, its local state satisfies CausalInvariant. -/
def GlobalCausalInvariant (κ : SystemState) : Prop :=
  ∀ addr se, κ.engineAt addr = some se →
    ∀ (h : se.idx = PubSubIdx.broker),
    -- Cast localState to CausalState using the type equality
    let s : CausalState := cast (by simp [PubSub.LocalState, h]) se.engine.env.localState
    CausalInvariant s

theorem causal_invariant_preserved (κ κ' : SystemState) (op : OpLabel) :
    WellTypedState κ →
    GlobalCausalInvariant κ →
    OpStep κ op κ' →
    GlobalCausalInvariant κ' := by
  intro wt inv step
  intro addr' se' heng' hidx'
  -- Case analysis on OpStep.
  -- Easy cases: S-Node, S-Clean, M-Send, M-Enqueue, S-SpawnMbox, M-Dequeue
  --   do not modify broker local state (only status, messages, or add/remove engines).
  --   Relate κ'.engineAt addr' back to κ.engineAt addr' to use inv.
  -- Hard case: S-Process
  --   If the processing engine is a broker, the effect (from causalAction) modifies
  --   CausalState. Linking through EffectEvalStep requires showing causalAction
  --   preserves CausalInvariant for all reachable states, which depends on
  --   causalAction_preserves_invariant but needs additional plumbing through the
  --   OpStep/EffectEvalStep machinery. Left as sorry.
  sorry

end MailboxActors.Examples.CausalMailbox
