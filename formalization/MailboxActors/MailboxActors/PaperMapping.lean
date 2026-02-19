import MailboxActors.Basic
import MailboxActors.Engine.Mode
import MailboxActors.Engine.Status
import MailboxActors.Engine.Config
import MailboxActors.Engine.Env
import MailboxActors.Engine.Effect
import MailboxActors.Engine.Guard
import MailboxActors.Engine.Behaviour
import MailboxActors.Engine.Engine
import MailboxActors.Engine.Message
import MailboxActors.Engine.Mailbox
import MailboxActors.System.Node
import MailboxActors.System.State
import MailboxActors.System.WellTyped
import MailboxActors.Semantics.Judgment
import MailboxActors.Properties.TypePreservation
import MailboxActors.Properties.Progress
import MailboxActors.Properties.Determinism
import MailboxActors.Properties.Isolation
import MailboxActors.Properties.Delivery
import MailboxActors.Examples.CausalMailbox

/-!
# Paper-to-Lean Mapping

Typechecked mapping from paper definitions, propositions, and examples
to their Lean 4 counterparts. Every `#check @Name` fails to compile if
the referenced declaration is renamed or deleted.
-/

open MailboxActors

-- ============================================================================
-- § Notation and Basic Definitions (Paper §2)
-- ============================================================================

/- Definition 1 — Engine Type Index and parametric context -/
-- File: Basic.lean
#check @EngineSpec

/- Definition 2 — Address -/
-- File: Basic.lean
#check @Address

-- ============================================================================
-- § Messages (Paper §3.1)
-- ============================================================================

/- Definition 3 — TotalMsg (equation (3): Σ (i : 𝕀). Msg_i) -/
-- File: Engine/Message.lean
#check @TotalMsg

/- Definition 4 — Message packet -/
-- File: Engine/Message.lean
#check @Message

/- Definition 5 — Append wrapper -/
-- File: Engine/Message.lean
#check @MailboxActors.Append

-- ============================================================================
-- § Engine Components (Paper §3.2–§3.4)
-- ============================================================================

/- Definition 6 — Engine lifecycle status -/
-- File: Engine/Status.lean
#check @EngineStatus

/- Definition 7 — Engine mode -/
-- File: Engine/Mode.lean
#check @EngineMode

/- Definition 8 — Engine configuration -/
-- File: Engine/Config.lean
#check @EngineConfig

/- Definition 9 — Execution environment -/
-- File: Engine/Env.lean
#check @EngineEnv

/- Definition 10 — Effect system -/
-- File: Engine/Effect.lean
#check @Effect

/- Definition 11 — Guard input -/
-- File: Engine/Guard.lean
#check @GuardInput

/- Definition 13 — Guarded action -/
-- File: Engine/Guard.lean
#check @GuardedAction

/- Composite operation g ⊙ a -/
-- File: Engine/Guard.lean
#check @GuardedAction.apply

/- Definition 14 — Behaviour -/
-- File: Engine/Behaviour.lean
#check @Behaviour

/- Definition 15 — Non-overlapping guards -/
-- File: Engine/Behaviour.lean
#check @NonOverlappingGuards

/- Well-Formed Behaviour (bundles behaviour + non-overlapping proof) -/
-- File: Engine/Behaviour.lean
#check @WellFormedBehaviour

-- ============================================================================
-- § Engine (Paper §3.5)
-- ============================================================================

/- Definition 17 — Engine (5-tuple) -/
-- File: Engine/Engine.lean
#check @Engine

/- Definition 18 — Mailbox engine predicates -/
-- File: Engine/Engine.lean
#check @Engine.isMailbox
#check @Engine.isProcessing

-- ============================================================================
-- § Nodes and System State (Paper §3.6–§3.7)
-- ============================================================================

/- Definition 19 — Node -/
-- File: System/Node.lean
#check @Node

/- Definition 20 — System state κ = (N, M, Ω) -/
-- File: System/State.lean
#check @SystemState

-- ============================================================================
-- § Well-Typedness (Paper §5)
-- ============================================================================

/- Well-typed system state (implicit in §5) -/
#check @WellTypedState

-- ============================================================================
-- § Operational Semantics — Judgment Forms (Paper §4.2)
-- ============================================================================

/- Judgment Form 3 — Guarded action evaluation -/
-- File: Semantics/Judgment.lean
#check @GuardEvalStep
#check @GuardEvalStep.guardMatch   /- Definition 25 — B-GuardedActionEval -/
#check @GuardEvalStep.guardFail    /- Definition 26 — B-NoMatchingGuard -/

/- Judgment Form 2 — Behaviour evaluation -/
-- File: Semantics/Judgment.lean
#check @EvalStep
#check @EvalStep.guardStrategy     /- Definition 28 — B-GuardStrategy -/
#check @EvalStep.allGuardsFail     /- Definition 29 — B-AllGuardsFail -/

/- Judgment Form 4 — Effect execution -/
-- File: Semantics/Judgment.lean
#check @EffectEvalStep
#check @EffectEvalStep.noop        /- Definition 39 — E-Noop -/
#check @EffectEvalStep.terminate   /- Definition 37 — E-Terminate -/
#check @EffectEvalStep.update      /- Definition 31 — E-Update -/
#check @EffectEvalStep.mfilter     /- Definition 32 — E-MFilter -/
#check @EffectEvalStep.chain       /- Definition 36 — E-Chain -/

/- Judgment Form 1 — System-level operations -/
-- File: Semantics/Judgment.lean
#check @OpStep
#check @OpStep.sNode               /- Definition 21 — S-Node -/
#check @OpStep.sClean              /- Definition 24 — S-Clean -/
#check @OpStep.mSend               /- Definition 30 — M-Send -/
#check @OpStep.mEnqueue            /- Definition 31 — M-Enqueue -/
#check @OpStep.mDequeue            /- Definition 32 — M-Dequeue -/

/- Judgment Form 5 — Engine processing -/
-- File: Semantics/Judgment.lean
#check @ProcessStep
#check @ProcessStep.process        /- Definition 40 — S-Process -/

/- Top-level system step -/
-- File: Semantics/Judgment.lean
#check @SysStep

-- ============================================================================
-- § Metatheoretic Properties (Paper §5)
-- ============================================================================

/- Proposition 1 — Type Preservation -/
-- File: Properties/TypePreservation.lean
#check @typePreservation

/- Proposition 2 — Progress -/
-- File: Properties/Progress.lean
#check @progress

/- Proposition 3 — Effect Determinism -/
-- File: Properties/Determinism.lean
#check @effectDeterminism

/- Proposition 4 — Mailbox Isolation -/
-- File: Properties/Isolation.lean
#check @mailboxIsolation

/- Proposition 5 — Eventual Delivery -/
-- File: Properties/Delivery.lean
#check @eventualDelivery

-- ============================================================================
-- § Example: Causal Delivery Mailbox (Paper §3.6, §4.9)
-- ============================================================================

-- File: Examples/CausalMailbox.lean
#check @Examples.CausalMailbox.PubSubIdx
#check @Examples.CausalMailbox.TopicMsg
#check @Examples.CausalMailbox.CausalState
#check @Examples.CausalMailbox.causalGuard
#check @Examples.CausalMailbox.causalAction
#check @Examples.CausalMailbox.causalBehaviour
-- causalNonOverlapping is private; its proof is bundled in causalBehaviour.nonOverlapping
