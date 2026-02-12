# MailboxActors — Lean 4 Formalization

Mechanized formalization of the Mailbox Actors paper.

## Module structure

| Module | Contents |
|---|---|
| `Basic` | Address, EngineSpec (parametric context) |
| `Engine.*` | Engine components (Status, Mode, Config, Env, Effect, Guard, Behaviour, Message, Mailbox) |
| `System.*` | Node, SystemState, WellTypedState |
| `Semantics.*` | Judgment forms and operational rules |
| `Properties.*` | Type Preservation, Progress, Effect Determinism, Mailbox Isolation, Eventual Delivery |
| `Examples.*` | Concrete instantiations (CausalMailbox) |
| `PaperMapping` | Compilation-guarded mapping from paper definitions to Lean declarations |

## Build

```
lake build
```

Depends on [Mathlib](https://github.com/leanprover-community/mathlib4).
