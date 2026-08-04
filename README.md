# QuantumRepresentationTheory

A [Lean 4](https://leanprover.github.io/)/[Mathlib](https://leanprover-community.github.io/mathlib4_docs/)
project sketching a path toward formalizing the energy spectrum of the
hydrogen atom — not through the usual analytic route, but through
representation theory.

## The idea

The standard way to make the hydrogen atom rigorous is analytic: unbounded
self-adjoint operators, spectral theory, all the machinery needed to give the
Coulomb Hamiltonian a precise meaning. That work is real and hard, and
[Physlib](https://github.com/leanprover-community/physlib) is already making
progress on it.

There is an older, more algebraic story too. The hydrogen atom has a hidden
symmetry — beyond ordinary rotations, its bound states also carry a
conserved Runge–Lenz vector, and together these generate a bigger symmetry
algebra. Lean on the representation theory of that algebra hard enough, and
the energy levels and their degeneracies fall out of group theory almost
without touching an actual Hamiltonian.

This project tries to build that second route: work out the algebra
completely first — classification of irreducible representations, Casimir
elements, the works — and only afterward come back and show that the real,
concrete quantum-mechanical operators satisfy whatever the algebra needed all
along.

That structure splits the project naturally into two halves, developed
mostly independently, that need to be stitched together at the end:

* **A math half** with no physics content at all: representations of Lie
  algebras, the classification of finite-dimensional irreducible
  $\mathfrak{sl}_2$-modules, Casimir elements, and the classification of
  jointly-irreducible *commuting pairs* of $\mathfrak{sl}_2$-actions (the
  algebraic heart of why hydrogen's degeneracy is $n^2$ and not just $2j+1$).
* **A physics half** that names the same objects the way a physicist would —
  angular momentum operators, the Runge–Lenz vector, the hidden $\mathfrak{so}(4)$
  symmetry of the bound states — currently developed as a self-contained
  finite-dimensional algebraic model, deliberately decoupled from Physlib's
  Hilbert-space machinery. Connecting the two, so this project's
  classification theorems actually discharge real physics, is future work.

## Where to look

* **[Blueprint](https://tomolediem.github.io/QuantumRepresentationTheory/blueprint/)**
  — the roadmap: every theorem and definition needed to get from bare Lie
  algebra representations to the hydrogen spectrum, and how they depend on
  each other. This is the best starting point.
* **[API documentation](https://tomolediem.github.io/QuantumRepresentationTheory/docs/)**
  — generated Lean documentation for this project, Mathlib, and the other
  dependencies, fully cross-linked with the blueprint (click "L∃∀N" on any
  blueprint theorem to jump to its Lean declaration).

Most of the blueprint is currently *stated but not proved* (`sorry` in the
Lean source) — the point of publishing it at this stage is to nail down the
right statements and the right dependency structure before doing the harder
work of proving them.

## Feedback wanted

This blueprint was put together with some help from Claude. I'd be genuinely
happy for people — whether coming from the math side or the physics side —
to poke holes in it, correct definitions, or point out where something I
think is missing from Mathlib already exists. The goal is to give people a
concrete, checkable target to walk toward, not a finished artifact.

## Building locally

```
lake build
```

To build and serve the blueprint locally, see the
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) documentation
(`blueprint/` contains the LaTeX source; `leanblueprint web` builds it,
`leanblueprint serve` serves it locally).
