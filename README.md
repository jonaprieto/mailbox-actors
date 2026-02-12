[![LaTeX](https://github.com/anoma/ART-Mailboxes-actors/actions/workflows/latex.yml/badge.svg)](https://github.com/anoma/ART-Mailboxes-actors/actions/workflows/latex.yml)
[![Lean 4](https://github.com/anoma/ART-Mailboxes-actors/actions/workflows/lean.yml/badge.svg)](https://github.com/anoma/ART-Mailboxes-actors/actions/workflows/lean.yml)

# Mailbox Actors

Formal framework for actor systems in which mailboxes are promoted to
independent, first-class actors with their own configuration, behaviour, and
lifecycle. Formalised in predicative Martin-Lof type theory.

- **Paper**: [`main.pdf`](main.pdf) (LaTeX, XeTeX)
- **Lean 4 formalization**: [`formalization/MailboxActors/`](formalization/MailboxActors/)

## Building the paper

Requires [LaTeXMk](https://ctan.org/pkg/latexmk) and XeTeX:

```
make
```

See the [Makefile](Makefile) for alternative engines (`lualatex`, `pdflatex`).

## Building the formalization

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (see
[`lean-toolchain`](formalization/MailboxActors/lean-toolchain) for the exact
version):

```
cd formalization/MailboxActors
lake build
```
