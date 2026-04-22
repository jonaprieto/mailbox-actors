import VersoManual
import MailboxActors

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.style.setOption false

#doc (Manual) "Operational Semantics" =>
%%%
tag := "semantics"
%%%

The operational semantics is a **labelled transition system** with five
judgment forms and 18 inference rules (Section 4 of the paper).  All rules
are encoded as inductive propositions in Lean 4.

# Guard Evaluation
%%%
tag := "guard-eval"
%%%

{lean}`MailboxActors.GuardEvalStep` determines whether a single guarded
action fires or fails.  It has two constructors:

 * **B-GuardedActionEval** ({lean}`MailboxActors.GuardEvalStep.guardMatch`) —
   the guard returns `some w`, and the action produces an effect using the
   witness and the proof that the guard holds.
 * **B-NoMatchingGuard** ({lean}`MailboxActors.GuardEvalStep.guardFail`) —
   the guard returns `none`, producing `Effect.noop`.

# Behaviour Evaluation
%%%
tag := "behaviour-eval"
%%%

{lean}`MailboxActors.EvalStep` selects the overall effect of a behaviour
on a given message.  Two rules:

 * **B-GuardStrategy** ({lean}`MailboxActors.EvalStep.guardStrategy`) —
   exactly one guarded action in the behaviour list has a matching guard;
   all others produce `noop`.  The matching action's effect becomes the
   behaviour's effect.
 * **B-AllGuardsFail** ({lean}`MailboxActors.EvalStep.allGuardsFail`) —
   every guarded action in the behaviour list fails its guard, so the
   behaviour produces `noop`.

# Effect Execution
%%%
tag := "effect-exec"
%%%

{lean}`MailboxActors.EffectEvalStep` interprets effects against the current
system state, producing a successor state.  One constructor per effect kind:

 * **E-Noop** — no state change.
 * **E-Send** — appends a message to the transit pool if the target exists,
   is a processing engine, and the type index matches; otherwise a silent no-op.
 * **E-Terminate** — sets the engine's status to `terminated`.
 * **E-Update** — replaces the engine's execution environment.
 * **E-MFilter** — transitions the engine to `ready f`, installing a new
   message acceptance filter.
 * **E-Spawn** — creates a child processing engine **and** its paired mailbox
   atomically, if the allocated addresses are fresh; otherwise just advances
   `nextId`.
 * **E-Chain** — sequences two effects: evaluates `e₁`, then `e₂` on the
   resulting state.

After effect execution, {lean}`MailboxActors.resolvePostStatus` determines
the final status: if the engine is still `busy` it resets to
`ready (fun _ => true)` (accept all); otherwise the current status
(`terminated` or `ready f`) is preserved.

# System-Level Operations
%%%
tag := "system-ops"
%%%

{lean}`MailboxActors.OpStep` defines the system-level transition relation,
labelled by {lean}`MailboxActors.OpLabel`.  Six rules cover the full
lifecycle:

 * **S-Node** (`sNode`) — create a new empty node.
 * **S-Clean** (`sClean`) — remove a terminated processing engine.
   Per Remark 4.4 of the paper, the paired **mailbox engine persists**
   so that in-flight messages are not orphaned.
 * **M-Send** (`mSend`) — route a message into transit, targeting
   the recipient's mailbox (not the processing engine directly).
 * **M-Enqueue** (`mEnqueue`) — deliver an in-transit message to a ready
   mailbox engine, transitioning it from `ready f` to `busy w`.
 * **S-SpawnWithMailbox** (`sSpawnMbox`) — spawn a processing engine paired
   with its dedicated mailbox in a single atomic step.
 * **M-Dequeue** (`mDequeue`) — transfer a message from a mailbox engine
   to its paired processing engine, transitioning the processing engine
   from `ready f` to `busy v`.

# Engine Processing
%%%
tag := "engine-processing"
%%%

The **S-Process** rule ({lean}`MailboxActors.OpStep.sProcess`) is the
composite rule for a single processing step: a busy engine evaluates its
behaviour via `EvalStep`, executes the resulting effect via `EffectEvalStep`,
and resolves its post-processing status.

{lean}`MailboxActors.ProcessStep` mirrors S-Process as a standalone
proposition for use in property proofs.

The top-level reduction relation {lean}`MailboxActors.SysStep` is the
existential: `∃ op, OpStep κ op κ'`.
