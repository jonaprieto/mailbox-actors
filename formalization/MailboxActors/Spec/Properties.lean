import VersoManual
import MailboxActors

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.style.setOption false

#doc (Manual) "Metatheoretic Properties" =>
%%%
tag := "properties"
%%%

Five metatheoretic properties are established for the mailbox actor
system (Section 5 of the paper).  All proofs are fully machine-checked
with **zero** uses of `sorry` or `admit`.

# Type Preservation (Proposition 1)
%%%
tag := "type-preservation"
%%%

```lean
#check @MailboxActors.typePreservation
```

Every system step preserves {lean}`MailboxActors.WellTypedState`.  The proof
requires {lean}`MailboxActors.MailboxIsolation` as a co-invariant so that
S-Clean (which removes only the processing engine, not its mailbox) cannot
orphan message targets.

The proof proceeds by cases on the operation label.  The most involved case
is **S-Process**, which delegates to
{lean}`MailboxActors.sProcessPreservesInvariants` — itself proved by
induction on the `EffectEvalStep` derivation, handling each effect
constructor (send, spawn, chain, etc.) individually.

# Progress (Proposition 2)
%%%
tag := "progress"
%%%

```lean
#check @MailboxActors.progress
```

A well-typed system with productive work can always take a **non-trivial**
step (excluding S-Node, which is always available).

The predicate {lean}`MailboxActors.hasProductiveWork` holds when at least
one of the following is true:

 1. An engine is `busy` — guaranteed to proceed via S-Process.
 2. A processing engine is `terminated` — guaranteed to be cleaned via S-Clean.
 3. A message is in transit to a ready mailbox that accepts it — guaranteed
    to proceed via M-Enqueue.

The proof relies on two helper results:
 * {lean}`MailboxActors.evalStep_total` — behaviour evaluation is total
   for well-formed behaviours.
 * {lean}`MailboxActors.effectEvalStep_total` — effect execution always
   produces a valid successor state.

# Effect Determinism (Proposition 3)
%%%
tag := "effect-determinism"
%%%

```lean
#check @MailboxActors.effectDeterminism
```

Under non-overlapping guards, the effect produced by behaviour evaluation
is **unique**.  The `NonOverlappingGuards` proof is embedded in
`WellFormedBehaviour`, so no explicit hypothesis is needed.

The proof case-splits on both `EvalStep` derivations.  When two different
guards appear to match (`guardStrategy`/`guardStrategy`), the
non-overlapping invariant forces one to produce `noop`, yielding a
contradiction.

# Mailbox Isolation (Proposition 4)
%%%
tag := "mailbox-isolation"
%%%

```lean
#check @MailboxActors.mailboxIsolation
```

All messages in transit target **mailbox engines**, never processing
engines directly.  This invariant is preserved by every system step.

The key insight is that M-Send is the only rule that creates messages,
and it always routes them to the target's mailbox address.

Two companion theorems formalize Remark 4.4 of the paper:

 * {lean}`MailboxActors.mailboxPersistence` — when S-Clean removes a
   terminated processing engine, its paired mailbox engine **survives**.
 * {lean}`MailboxActors.mailboxSurvivesClean` — the surviving mailbox
   retains its type index and `mail` mode.

# Eventual Delivery (Proposition 5)
%%%
tag := "eventual-delivery"
%%%

```lean
#check @MailboxActors.eventualDelivery
```

Under **strong fairness**, every in-transit message is eventually consumed.

The proof is structured around infinite execution traces
({lean}`MailboxActors.Trace`).  The key definitions are:

 * {lean}`MailboxActors.IsExecution` — consecutive states are related
   by `SysStep`.
 * {lean}`MailboxActors.StronglyFair` — every infinitely-often-enabled
   transition is eventually taken (TLA⁺-style).
 * {lean}`MailboxActors.UniqueInTransit` — the message appears at most
   once in the transit pool.
 * {lean}`MailboxActors.EventuallyAccepts` — the target mailbox is
   eventually ready and willing to accept the message.

The safety lemma {lean}`MailboxActors.invariants_trace` establishes that
well-typedness and mailbox isolation are jointly preserved along any
execution trace.  The main theorem then shows that under the fairness
and acceptance hypotheses, there exists a future step `k` where the
message is no longer in transit.
