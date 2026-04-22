import VersoManual

import Spec.Engines
import Spec.System
import Spec.Semantics
import Spec.Properties
import Spec.Examples

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.style.setOption false

#doc (Manual) "Mailbox Actors" =>

This is the machine-checked companion to the paper
[*Mailbox Actors*](https://github.com/jonaprieto/mailbox-actors/blob/main/main.pdf)
(submitted, under revision).

We present a formal framework for actor systems in which **mailboxes are
promoted to independent, first-class actors** — native actors with their own
configuration, behaviour, and lifecycle.  Each processing actor is automatically
paired with a dedicated mailbox actor whose guarded-action behaviour governs
delivery, filtering, and scheduling, enabling modular mailbox implementations
while adding no burden for simple engines that need only the default
first-in-first-out policy.

Every definition, proposition, and example below is type-checked by the
[Lean 4](https://lean-lang.org/) theorem prover.  There are **zero** uses of
`sorry` or `admit` in the formalization.

**Citation**

> J. Prieto-Cubides, A. Hart, T. Heindel. *Mailbox Actors*. 2025.
> DOI: [10.5281/zenodo.14915469](https://doi.org/10.5281/zenodo.14915469)

{include 0 Spec.Engines}

{include 0 Spec.System}

{include 0 Spec.Semantics}

{include 0 Spec.Properties}

{include 0 Spec.Examples}
