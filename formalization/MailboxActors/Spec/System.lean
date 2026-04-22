import VersoManual
import MailboxActors

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.style.setOption false

#doc (Manual) "System State" =>
%%%
tag := "system"
%%%

The system state assembles nodes, a global message pool, and a fresh-ID
counter into a single configuration (Sections 3.6–3.7 of the paper).

# Nodes
%%%
tag := "nodes"
%%%

A {lean}`MailboxActors.SomeEngine` is an existentially-typed engine: the
engine type index is packed inside, so heterogeneous collections of engines
are well-typed.

An engine map ({lean}`MailboxActors.EngineMap`) associates local identifiers
with engine instances.  A {lean}`MailboxActors.Node` groups an engine map
under a node identifier.

# System State
%%%
tag := "system-state"
%%%

The {lean}`MailboxActors.SystemState` is the triple `(nodes, messages, nextId)`:

 * `nodes : List Node` — the live nodes in the system,
 * `messages : List Message` — the global pool of messages in transit,
 * `nextId : Nat` — a monotonically increasing counter for fresh address generation.

Key operations on the system state include:

 * `engineAt addr` — global engine lookup by address,
 * `mailboxOf addr` — convention: the paired mailbox lives at `engineId + 1`,
 * `updateEngineAt`, `removeEngineAt`, `addEngineAt` — CRUD operations on engines,
 * `freshId` — allocates a fresh identifier and advances the counter.

The formalization includes **correctness lemmas** for all CRUD operations:
update-then-lookup returns the new engine, update does not affect other addresses,
removal yields `none` at the removed address, and addition at a fresh address
succeeds.  The lemma {lean}`MailboxActors.mailboxOf_injective` guarantees that
the mailbox pairing is injective, and {lean}`MailboxActors.mailboxOf_ne_self`
ensures a mailbox address always differs from its partner.

# Well-Typedness
%%%
tag := "well-typedness"
%%%

A {lean}`MailboxActors.WellTypedState` bundles five structural invariants:

 1. **Messages typed** — every in-transit message has a payload whose engine
    type index matches the target engine's type.
 2. **Mailbox exists** — every processing engine has a paired mailbox engine
    whose type index matches and whose mode is `mail`.
 3. **Fresh IDs** — the `nextId` counter exceeds every existing `engineId`,
    guaranteeing address freshness.
 4. **Message targets valid** — all messages in transit target addresses
    created before the current `nextId`.
 5. **Nodes exist** — for every engine, the corresponding node is present.

The companion predicate {lean}`MailboxActors.MailboxIsolation` states that
**all messages in transit target mailbox engines** (not processing engines).
This is a separate invariant because it is preserved by the semantics and
required by type preservation, but it is not part of the well-typedness
definition itself.

The theorem {lean}`MailboxActors.spawnPairing` restates the `mailbox_exists`
field as a standalone result for clarity: every processing engine has a
paired mailbox engine with matching type index in `mail` mode.
