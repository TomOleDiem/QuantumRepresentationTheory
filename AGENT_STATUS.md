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
Now claiming/working: Sl2/Classification.lean (all 6 remaining sorries:
exists_stringLieSubmodule, stringSpan_eq_top, string_isBasis, finrank_eq_succ,
classification, classification_n_eq_finrank_sub_one). Plan: change
`LieSubmodule K L M` -> `LieSubmodule K ↥(t.toLieSubalgebra (R:=K)) M` and
`LieModule.IsIrreducible K L M` -> `LieModule.IsIrreducible K
↥(t.toLieSubalgebra (R:=K)) M` throughout (the automatic
`LieSubalgebra.lieRingModule`/`lieModule` instances make M a module for the
subalgebra for free, restricting the ambient L-action - no change needed to
the file's M-side hypotheses). Grep confirms nothing else in the repo imports
Sl2/Classification.lean yet, so this is self-contained. Mathlib's own
`IsSl2Triple.HasPrimitiveVectorWith` API (lie_h_pow_toEnd_f,
lie_e_pow_succ_toEnd_f, lie_f_pow_toEnd_f, pow_toEnd_f_eq_zero_of_eq_nat)
already has everything needed for exists_stringLieSubmodule's h/e/f-invariance
computation; pow_toEnd_f_eq_zero_of_eq_nat needs IsNoetherian/IsTorsionFree,
so exists_stringLieSubmodule (and hence string_isBasis) will likely need
[FiniteDimensional K M] added too, matching what finrank_eq_succ/
classification already require.
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
