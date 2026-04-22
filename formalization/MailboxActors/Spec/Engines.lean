import VersoManual
import MailboxActors

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.style.setOption false

#doc (Manual) "Engines" =>
%%%
tag := "engines"
%%%

An **engine** is the fundamental unit of computation.  The entire
formalization is parametric over a finite type of engine indices,
which determines the message, configuration, and state types for each
engine kind.  This section covers Definitions 1–18 of the paper
(Sections 2–3).

# Parametric Context
%%%
tag := "parametric-context"
%%%

The formalization is parameterised by the typeclass
{lean}`MailboxActors.EngineSpec`, which bundles:

 * A finite type of **engine type indices** (`𝕀`),
   with decidable equality and a `Fintype` instance.
 * Indexed families `MsgType`, `CfgData`, and `LocalState`
   assigning message, configuration, and state types to each index.
 * Operations `mailboxContains`, `mailboxRemove`, and `unwrap`
   that connect mailbox state to message delivery.

An {lean}`MailboxActors.Address` identifies an engine as a `(nodeId, engineId)` pair.

# Messages
%%%
tag := "messages"
%%%

Messages are typed by engine index.  The **total message type**
{lean}`MailboxActors.TotalMsg` is the dependent sum `Σ (i : 𝕀). Msg_i`,
collecting all payloads across engine types into a single universe.

A {lean}`MailboxActors.Message` is a packet in transit, carrying a
`sender` address, a `target` address, and a `TotalMsg` payload.

The {lean}`MailboxActors.Append` wrapper distinguishes mailbox-level
messages from processing-level messages: a mailbox engine for type `i`
receives `Append(Msg_i)`, making the indirection explicit in the type.

# Lifecycle and Mode
%%%
tag := "lifecycle-mode"
%%%

Each engine has a **lifecycle status** ({lean}`MailboxActors.EngineStatus`),
an inductive type with three constructors:

 * `ready f` — accepting messages filtered by `f : Msg_i → Bool`,
 * `busy m` — currently processing message `m`,
 * `terminated` — stopped, awaiting cleanup.

The **operational mode** ({lean}`MailboxActors.EngineMode`) distinguishes
processing engines (`process`) from mailbox engines (`mail`).  The mode
is fixed at creation and opaque to the engine's behaviour.

# Configuration and Environment
%%%
tag := "config-env"
%%%

An {lean}`MailboxActors.EngineConfig` bundles an optional parent address,
the operational mode, and type-specific configuration data.

An {lean}`MailboxActors.EngineEnv` provides the execution environment:
type-specific local state and an address book mapping names to addresses.

# Effects
%%%
tag := "effects"
%%%

The **effect system** ({lean}`MailboxActors.Effect`) describes side-effects
produced by a single behaviour step.  Effects form an inductive type with
seven constructors:

 * `noop` — no observable action,
 * `send j target payload` — enqueue a message for engine type `j`,
 * `update env` — replace the engine's local environment,
 * `spawn j cfg state` — create a new child engine of type `j`,
 * `mfilter f` — transition to `ready f`, installing a new acceptance filter,
 * `terminate` — signal engine termination,
 * `chain e₁ e₂` — sequence two effects.

The `chain` constructor gives effect composition without requiring a monadic
bind; the semantics evaluates `e₁` first, then `e₂` on the resulting state.

# Guards and Guarded Actions
%%%
tag := "guards"
%%%

A {lean}`MailboxActors.GuardInput` is the triple `(msg, config, env)` that
guards and actions receive.

A {lean}`MailboxActors.GuardedAction` pairs a **guard** with an **action**.
The action is dependently typed: it may only be invoked when
`guard inp = some w`, so the type system enforces the invariant
"action fires only when the guard holds."  The witness `w` carries
any data extracted by the guard (pattern-match results, decoded fields, etc.).

The convenience function {lean}`MailboxActors.GuardedAction.apply` evaluates
a guarded action on a given input: if the guard matches it fires the action
(forwarding the proof), otherwise it produces `noop`.

# Behaviours
%%%
tag := "behaviours"
%%%

A {lean}`MailboxActors.Behaviour` is a list of guarded actions.

{lean}`MailboxActors.NonOverlappingGuards` is the key structural property:
for any input, **at most one** guarded action's guard succeeds.  This
ensures determinism of behaviour evaluation (Proposition 3).

A {lean}`MailboxActors.WellFormedBehaviour` bundles the action list with
a proof of non-overlapping guards, so downstream theorems never need
`NonOverlappingGuards` as a separate hypothesis.

# Engine
%%%
tag := "engine"
%%%

An {lean}`MailboxActors.Engine` of type `i` is a **4-tuple**
`⟨behaviour, status, config, env⟩`.  The behaviour field carries a
`WellFormedBehaviour`, embedding the non-overlapping guard proof.

Two predicates classify engines by mode:

 * {lean}`MailboxActors.Engine.isMailbox` — the engine's mode is `mail`,
 * {lean}`MailboxActors.Engine.isProcessing` — the engine's mode is `process`.

Every processing engine is automatically paired with a dedicated mailbox engine.
The mailbox engine's behaviour governs delivery, filtering, and scheduling for
its partner.
