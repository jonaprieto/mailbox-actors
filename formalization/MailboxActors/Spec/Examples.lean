import VersoManual
import MailboxActors

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.style.setOption false

#doc (Manual) "Examples" =>
%%%
tag := "examples"
%%%

Concrete instantiations of the framework demonstrate that the abstractions
are usable and that the metatheoretic properties yield practical guarantees.

# Causal Delivery Mailbox
%%%
tag := "causal-mailbox"
%%%

A **publish-subscribe system** where the mailbox enforces causal ordering
of messages (Sections 3.6 and 4.9 of the paper).

## Engine Types

{lean}`MailboxActors.Examples.CausalMailbox.PubSubIdx` defines two engine
kinds:

 * `relay` — forwards messages between nodes,
 * `broker` — delivers to local subscribers with causal ordering.

## Message and State Types

A {lean}`MailboxActors.Examples.CausalMailbox.TopicMsg` carries:

 * `publisher` — the originating address,
 * `deps` — a `Finset` of message hashes representing causal dependencies,
 * `content` and `sig` — payload and signature,
 * `msgHash` — the message's own hash for dependency tracking.

The broker's local state ({lean}`MailboxActors.Examples.CausalMailbox.CausalState`)
maintains three fields:

 * `delivered` — the set of hashes of already-delivered messages,
 * `pending` — messages buffered because their dependencies are not yet met,
 * `ready` — messages whose dependencies are satisfied and are ready for delivery.

## Causal Guard and Action

The causal guard ({lean}`MailboxActors.Examples.CausalMailbox.causalGuard`)
always matches (its witness type is `Unit`).  The real logic lives in the
action ({lean}`MailboxActors.Examples.CausalMailbox.causalAction`), which
branches on dependency satisfaction:

 * **Dependencies met**: the message is added to `ready`, its hash is
   recorded in `delivered`, and a **cascade** check releases any pending
   messages whose dependencies are now satisfied.
 * **Dependencies not met**: the message is buffered in `pending`.

The resulting {lean}`MailboxActors.Examples.CausalMailbox.causalBehaviour`
is a `WellFormedBehaviour` — the single-guard list trivially satisfies
`NonOverlappingGuards`.

## Correctness

The **causal delivery invariant** states that every message in the `ready`
list has its causal dependencies recorded in the `delivered` set.

The theorem {lean}`MailboxActors.Examples.CausalMailbox.causalAction_preserves_invariant`
proves that `causalAction` preserves this invariant: messages are only
released to subscribers when their causal predecessors have already been
delivered.  The cascade step (via `findCascade`) also respects the invariant,
since `findCascade` only releases messages whose dependencies are a subset
of the updated `delivered` set.
