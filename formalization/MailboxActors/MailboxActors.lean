-- Core
import MailboxActors.Basic

-- Engine components
import MailboxActors.Engine.Status
import MailboxActors.Engine.Mode
import MailboxActors.Engine.Config
import MailboxActors.Engine.Env
import MailboxActors.Engine.Effect
import MailboxActors.Engine.Guard
import MailboxActors.Engine.Behaviour
import MailboxActors.Engine.Message
import MailboxActors.Engine.Engine
import MailboxActors.Engine.Mailbox

-- System
import MailboxActors.System.Node
import MailboxActors.System.State
import MailboxActors.System.WellTyped

-- Operational semantics
import MailboxActors.Semantics.Judgment

-- Metatheoretic properties
import MailboxActors.Properties.TypePreservation
import MailboxActors.Properties.Progress
import MailboxActors.Properties.Determinism
import MailboxActors.Properties.Isolation
import MailboxActors.Properties.Delivery

-- Examples
import MailboxActors.Examples.CausalMailbox

/-!
# Mailbox Actors — Lean 4 Formalization

Mechanized formalization of "Mailbox Actors: promoting mailboxes to
first-class actors in actor systems, formalized in dependent type theory."

## Module Structure

- `Basic`            — Address, EngineSpec (parametric context)
- `Engine.*`         — Engine components (Status, Mode, Config, Env, Effect, etc.)
- `System.*`         — Node, SystemState, WellTypedState
- `Semantics.*`      — Judgment forms and all 18 operational rules
- `Properties.*`     — Metatheoretic properties (5 propositions)
- `Examples.*`       — Concrete instantiations (CausalMailbox)
-/
