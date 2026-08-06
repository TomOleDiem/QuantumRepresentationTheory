# Agent coordination

Multiple Claude Code sessions may be working in this repo at once. Before
starting on a file, check here for what's already claimed. Update your
section before you start editing, and clear it (or mark done) when you
commit and stop.

Keep entries short: which file(s), which declaration(s), and current status.
Commit your work before signing off so the other agent can build on it
cleanly — don't leave the tree mid-edit with a broken build if you can help
it.

## Active

### Claude - 2026-08-06
Done (committed 65c921a): Hydrogen/Basic.lean's `BoundStateRepresentation`
reworked with 12 new fields spelling out the standard quantum Runge-Lenz
`so(4)` commutation relations (`JM_*`: M transforms as a vector under J;
`MM_*`: M's self-commutator closes back onto J rescaled by `-2E/m`) - the
gap the blueprint's Caveats chapter had flagged as blocking
`Hydrogen/Symmetry.lean`'s `I_comm_xy` etc. (previously false-as-stated,
concrete counterexample `M≡0`). No downstream file constructs a concrete
`BoundStateRepresentation` instance, so this was a safe, non-breaking
addition. Proved all 7 previously-`sorry` theorems in
`Hydrogen/Symmetry.lean` (`I_comm_xy/yz/zx`, `K_comm_xy/yz/zx`, `I_comm_K`)
from the new relations. Updated the blueprint's `def:hyd-bound-state` text,
marked `thm:hyd-two-factors-commute`/`thm:hyd-so4-decomposition` `\leanok`,
and rewrote the relevant Caveats paragraph (the fully general
`so(n)`-antisymmetric-tensor rewrite remains explicitly out of scope/future
work; this was the concrete, scoped `n=3,4` fix).

**Repo-wide: zero remaining `sorry`s.** Full `lake build` passes.
`leanblueprint checkdecls`/`web` both run clean. The project (all sorries
mentioned in `find . -name "*.lean" -exec grep -Hn sorry {} +`) is complete.

Two things intentionally left as-is, not bugs to pick up:
- `Sl2/CommutingActions.lean`'s `commuting_classification` and
  `Sl2/ClebschGordan.lean`'s `clebsch_gordan` are proved only as *plain
  vector-space* isomorphisms, not yet `sl₂`-equivariant ones (both say so
  explicitly in their own doc comments/TODOs and the blueprint). Upgrading
  either is real, substantial future work, not a leaf fix.
- The general `so(n)`-antisymmetric-tensor presentation of angular momentum
  (Caveats chapter) was deliberately not attempted - a different, larger
  scope than the concrete `so(4)` Runge-Lenz fix just completed.
Status: idle (nothing left to prove)

## Log (most recent first)

### Claude sessions - 2026-08-05 through 2026-08-06 (summarized)
Chronological history of getting the repo to zero sorries, in commit order
(see git log for full detail): crossComponent_bilinear, casimirBasisDependent_basis_indep,
clebsch_gordan_finrank + Casimir/Centrality's UEA-track theorems (fixing a
missing-invariance bug shared with casimirBasisDependent), string_linearIndependent,
Sl2/Basic.lean's standardSl2ModuleLieRingModule/LieModule (the biggest early
blocker - explicit ρE/ρF/ρH construction + Φ Lie-homomorphism), Hydrogen/Symmetry's
equal_casimirs, Sl2/ClebschGordan's clebsch_gordan (vector-space form, dimension
counting), AngularMomentum/Classification's isIrreducible_iff, a full architectural
rewrite of Sl2/Classification.lean (LieSubmodule/IsIrreducible restricted to the
generated subalgebra rather than the ambient Lie algebra, since the original
generic-`L` statement was false), AngularMomentum/Classification's spin_classification
and Jsq_eq_smul, Sl2/CommutingActions.lean's commuting_classification (joint
primitive vector for two commuting sl2-triples + bivariate string basis - the
last "genuinely deep" piece), and finally Hydrogen/Basic.lean's `so(4)` rework
+ Hydrogen/Symmetry.lean's I/K commutator theorems (2026-08-06, see Active
section above for detail - this closed out the whole project).

<!-- Move your entry here when done, with a one-line summary. -->
