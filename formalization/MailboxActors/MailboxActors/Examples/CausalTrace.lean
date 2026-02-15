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
  -- Proof by case analysis on op
  sorry -- To be filled in Phase 4

end MailboxActors.Examples.CausalMailbox
