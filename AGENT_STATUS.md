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

### Claude (this session) - 2026-08-05
Done (committed 844168e, pushed): fixed 9 blueprint definitions that were
sorry-free in Lean but missing \leanok (casimirBasisDependent, casimir,
AngularMomentumRepresentation, Jp/Jm, magneticBasisVec, leviCivita,
BoundStateRepresentation, Ax/Ay/Az, Ix/Iy/Iz/Kx/Ky/Kz) - these were rendering
as not-yet-formalized in the live dependency graph despite having complete
Lean code. Redeployed blueprint to gh-pages (a439885) with these fixes plus
the other session's clebsch_gordan_finrank/Casimir centrality work baked in.
Then proved AngularMomentum/Classification.lean's isIrreducible_iff (no
sorry, not yet committed) - ρ.IsIrreducible (invariance under Jx,Jy,Jz
individually) agrees with LieModule.IsIrreducible for the induced sl2-
subalgebra action, via `IsSl2Triple.mem_toLieSubalgebra_iff` to express
Jx,Jy,Jz as combinations of (2Jz,J+,J-) and back. Marked \leanok in the
blueprint. Not touching Sl2/Basic.lean or Sl2/Classification.lean (claimed
below). Picking next leaf target now.
External feedback received: someone reviewing the blueprint suggested
angular momentum should really be an antisymmetric 2-tensor (so(n)-style),
not a 3-vector specific to 3D - a real point (so(3)'s vector-via-cross-
product presentation is a low-dimension coincidence) but a bigger design
question than a leaf fix. Per user's explicit direction, only documented
this (new Caveats paragraph, committed 7d87f2c) rather than acting on it -
also connects it to the concrete Hydrogen/Symmetry.lean gap below. Not
attempting a rewrite; flagging so whoever revisits doesn't duplicate the
"stay algebraic, decoupled from Physlib" scoping discussion already baked
into the Overview/Chapter 4 text.
Also done (once Sl2/Basic.lean became buildable again): Sl2/ClebschGordan.lean's
`clebsch_gordan` (vector-space form) - both of that file's theorems are now
sorry-free. Proved via pure dimension-counting
(FiniteDimensional.nonempty_linearEquiv_of_finrank_eq +
Module.finrank_tensorProduct/finrank_directSum/finrank_pi +
clebsch_gordan_finrank), no Lie-theory content needed. Also corrected the
blueprint's \uses for thm:sl2-clebsch-gordan: it cited thm:sl2-classification
and thm:sl2-tensor-action, but the actual Lean `clebsch_gordan` is
(deliberately, per its own doc comment) only a plain vector-space
isomorphism, not yet sl2-equivariant, so neither is really used - reworded
the theorem statement to say so honestly and marked \leanok.
Currently: adding two private helper lemmas to AngularMomentum/Classification.lean
towards Jsq_eq_smul (still sorry, not attempting the full proof - it needs
either Sl2/Classification's machinery or a from-scratch primitive-vector
argument, both substantial). The clean fact: `Jp*Jm = Jx*Jx+Jy*Jy+Jz` (the
standard ladder-operator identity - NOT `Jp*Jm = J²`, an easy sign error to
make, since `[Jx,Jy]=iJz` gives an extra `+Jz` term), hence
`J² = Jp*Jm+Jz*Jz-Jz`. Verified in isolation (Sl2/Basic.lean was mid-edit
and broken at the time, couldn't build-test in place) via a standalone
repro file matching the real defs; waiting for Sl2/Basic.lean to stabilize
to do a real build check before committing.
Status: in progress

### Claude (2nd session) - 2026-08-06
Done (committed): Hydrogen/Basic.lean's crossComponent_bilinear,
Casimir/Basic.lean's casimirBasisDependent_basis_indep (548f2de);
Sl2/Classification.lean's string_linearIndependent, added [CharZero K]
(fc01331).
Done (committed ae14a1d): Sl2/Basic.lean's standardSl2ModuleLieRingModule
and standardSl2ModuleLieModule - both previously-sorry theorems now proved
in full. Built explicit ρE/ρF/ρH endomorphisms of StandardSl2Module K n,
proved the sl2 bracket relations (rel_ef/rel_he/rel_hf) directly via the
associative-ring commutator, transported {e,f,h}'s basis of the generated
subalgebra (linearIndependent_efh via the ad(h)-eigenvector trick + Basis.mk)
along Basis.constr into a Lie-homomorphism Φ (checked on generators via
Φ_bracket_basis, extended to the whole subalgebra by bilinearity via
Basis.ext twice - Φ_lie_basis_right then Φ_lie), then packaged into the
LieRingModule/LieModule instances. Full `lake build` passes. This was the
largest remaining foundational blocker; several downstream files (ClebschGordan,
CommutingActions, AngularMomentum/Classification's spin_classification) were
stuck on it.
Done (committed 40adcca): Hydrogen/Symmetry.lean's equal_casimirs - added
the missing `[Nontrivial V]` hypothesis (zero module makes hI/hK vacuous) and
proved n1=n2 via applying I²=K² to a nonzero vector + linear_combination
factoring. Marked \leanok.
Flagged, NOT proved (left `sorry` with an in-file doc comment + concrete
counterexample, matching the blueprint's own already-documented Caveats
entry): Hydrogen/Symmetry.lean's I_comm_xy/I_comm_yz/I_comm_zx/K_comm_xy/
K_comm_yz/K_comm_zx/I_comm_K - false as stated, since BoundStateRepresentation
has no axioms relating Mx,My,Mz to Jx,Jy,Jz (Mx=My=Mz=0 is a valid instance
for any Jz≠0, giving a genuine counterexample to I_comm_xy). Needs the
so(4)-antisymmetric-tensor architectural fix the blueprint's Caveats section
already proposes; not attempted.
User confirmed: go ahead with the Sl2/Classification.lean architectural fix.
Done (committed ae2fe96, cfa3b57): Sl2/Classification.lean - all 6 remaining
sorries proved (exists_stringLieSubmodule, stringSpan_eq_top, string_isBasis,
finrank_eq_succ, classification, classification_n_eq_finrank_sub_one), via
the planned rewrite: `LieSubmodule K L M` -> `LieSubmodule K
↥(t.toLieSubalgebra (R:=K)) M` and `LieModule.IsIrreducible K L M` ->
`LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R:=K)) M` throughout, using
the automatic `LieSubalgebra.lieRingModule`/`lieModule` instances. The hard
part, `classification`, builds an explicit `LieModuleEquiv` from the
primitive-vector string basis to `StandardSl2Module` via `Basis.equiv` +
`Basis.ext` (checked equivariance generator-by-generator, combined via
`IsSl2Triple.mem_toLieSubalgebra_iff`). Also added a `PublicApi` section to
Sl2/Basic.lean (commit 70f6e4a) exposing the action formulas
(standardSl2ModuleLieRingModule_{h,e,f}_apply_*) since Φ/ρE/ρF/ρH are
private - needed by classification's proof.
Done (committed c0c01fd): AngularMomentum/Classification.lean is now fully
sorry-free. `spin_classification` is a direct corollary of the completed
Sl2.Classification.classification + this file's own isIrreducible_iff (just
needed the missing import). `Jsq_eq_smul` proved from scratch: J^2 is central
for the sl2 action (commutes with Jp,Jm via explicit associative-ring
algebra; commuting with Jz follows from Jacobi since 2*Jz=[Jp,Jm]), then
case-split on Jz=0 (forces Jx=Jy=0 too, n=0) vs Jz!=0 (primitive vector m0 of
weight n, compute J^2 m0 = (n/2)(n/2+1).m0 directly, then irreducibility on
ker(J^2 - c.1) forces it to be everything). Both marked \leanok.
Repo-wide remaining sorries: Hydrogen/Symmetry.lean's 7 (flagged
false-as-stated, not attempting - see below) and Sl2/CommutingActions.lean's
2 (commuting_classification, commuting_classification_finrank).
User confirmed: go ahead and attempt commuting_classification.
Done (committed 4105969): Sl2/CommutingActions.lean - both
commuting_classification and commuting_classification_finrank proved;
the file is now fully sorry-free. Ended up NOT needing Mathlib's general
Lie's-theorem machinery (checked, none exists for Lie modules) - instead
built the joint primitive vector concretely: get a primitive vector for t1
on all of V, note ker(e1)⊓ker(h1-n1•1) is invariant under h2,e2,f2 (they
commute with e1,h1) and nonzero, package it as a LieSubmodule for t2's
subalgebra (needed a new lemma, isSl2Triple_sub, added to Sl2/Basic.lean:
hSub/eSub/fSub form a genuine IsSl2Triple within the subalgebra), and take
ITS primitive vector - automatically primitive for t1 too since it lies in
that invariant space. The bivariate string f1^a(f2^b m0) is then a basis:
linearly independent via the combined operator h1+(n1+1)•h2 (injective
combined eigenvalue, proved via an integer argument since K need not be
ordered), spanning via reusing Sl2/Classification's single-triple string
API twice (once per triple, commuting the other triple's generators
through) plus the joint-irreducibility hypothesis. Dimension count then
gives commuting_classification via FiniteDimensional.nonempty_linearEquiv_of_finrank_eq,
same technique as Sl2/ClebschGordan.lean. Reworded the blueprint entry to
honestly state a vector-space (not yet equivariant) isomorphism, matching
the file's own TODO and the precedent already set by thm:sl2-clebsch-gordan.
Repo-wide, the only remaining sorries anywhere are Hydrogen/Symmetry.lean's
7 already-flagged false-as-stated theorems (need the so(4)-tensor
architectural fix; not attempted, out of scope unless requested).
Status: idle

### Claude (other session) - 2026-08-05
Done (committed, 3d33b7c): Sl2/ClebschGordan.lean's clebsch_gordan_finrank
(pure Finset identity). Casimir/Centrality.lean's casimirUEA_mem_center and
central_commutes_toEnd (UEA-track) - Casimir/Centrality.lean and
Casimir/Basic.lean now both fully sorry-free. casimirUEA gained a
`(hΦ_inv : Φ.lieInvariant L)` parameter (same missing-invariance bug as
casimirBasisDependent had).
Investigated but did not claim Sl2/Basic.lean's
standardSl2ModuleLieRingModule/standardSl2ModuleLieModule (now claimed above
by the 2nd session).
Status: last known - in progress / idle, unclear. Check git log for latest.

## Log (most recent first)

<!-- Move your entry here when done, with a one-line summary. -->
