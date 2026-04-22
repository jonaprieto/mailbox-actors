[![LaTeX](https://github.com/jonaprieto/mailbox-actors/actions/workflows/latex.yml/badge.svg)](https://github.com/jonaprieto/mailbox-actors/actions/workflows/latex.yml)
[![Lean 4](https://github.com/jonaprieto/mailbox-actors/actions/workflows/lean.yml/badge.svg)](https://github.com/jonaprieto/mailbox-actors/actions/workflows/lean.yml)
[![Spec](https://github.com/jonaprieto/mailbox-actors/actions/workflows/pages.yml/badge.svg)](https://github.com/jonaprieto/mailbox-actors/actions/workflows/pages.yml)

# Mailbox Actors

Formal framework for actor systems in which mailboxes are promoted to
independent, first-class actors with their own configuration, behaviour, and
lifecycle. Formalised in predicative Martin-Lof type theory.

- **Paper**: [`main.pdf`](main.pdf) (LaTeX, XeTeX)
- **Lean 4 formalization**: [`formalization/MailboxActors/`](formalization/MailboxActors/)
- **Online spec**: [jonaprieto.github.io/mailbox-actors](https://jonaprieto.github.io/mailbox-actors/) (Verso, type-checked by Lean)

## Citing

The paper has been submitted and is currently under revision.
The latest PDF is available in this repository: [`main.pdf`](main.pdf).

```bibtex
@misc{prieto2025mailboxactors,
  title        = {Mailbox Actors},
  author       = {Jonathan Prieto-Cubides and Anthony Hart and Tobias Heindel},
  year         = {2025},
  note         = {Submitted, under revision},
  doi          = {10.5281/zenodo.14915469},
  url          = {https://doi.org/10.5281/zenodo.14915469}
}
```

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

## Building the online spec

```
cd formalization/MailboxActors
lake build generate-spec
lake exe generate-spec
```

The generated site will be in `formalization/MailboxActors/_out/html-multi/`.
