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
Status: in progress

### Claude (2nd session) - 2026-08-05
Done (committed): Hydrogen/Basic.lean's crossComponent_bilinear,
Casimir/Basic.lean's casimirBasisDependent_basis_indep (548f2de);
Sl2/Classification.lean's string_linearIndependent, added [CharZero K]
(fc01331). Not touching Sl2/Classification.lean further right now.
Now claiming/working: Sl2/Basic.lean only (standardSl2ModuleLieRingModule,
standardSl2ModuleLieModule). Adding [CharZero K]. Plan: linear independence of
{e,f,h} via the ad(h)-eigenvector trick (eigenvalues 2,-2,0), Basis.span for a
basis of the subalgebra, Basis.constr for the three generator actions on
StandardSl2Module and the subalgebra->End map.
Found but not fixed (flagging for whoever picks up Sl2/Classification.lean
next): exists_stringLieSubmodule and everything after it in that file
(stringSpan_eq_top, string_isBasis, finrank_eq_succ, classification,
classification_n_eq_finrank_sub_one) is false as stated for generic ambient
`L` - `LieSubmodule K L M` demands invariance under *all* of L, not just
h,e,f, but the file's `L` carries no hypothesis that it's spanned by {h,e,f}.
Only true when L is (isomorphic to) `t.toLieSubalgebra K` itself - matches how
downstream callers always instantiate it, but the file's own generic
statement doesn't capture that. Needs an architectural decision, not a leaf
fix.
Status: in progress

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
