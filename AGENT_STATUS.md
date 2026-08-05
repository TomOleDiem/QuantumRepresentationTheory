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
Done this session (no sorry, full project builds, blueprint \leanok'd, not yet
committed): Sl2/ClebschGordan.lean's clebsch_gordan_finrank (pure Finset identity).
Casimir/Centrality.lean's casimirUEA_mem_center and central_commutes_toEnd (the
UEA-track theorems) - Casimir/Centrality.lean and Casimir/Basic.lean are now both
fully sorry-free. Note: casimirUEA's signature changed, gained a
`(hΦ_inv : Φ.lieInvariant L)` parameter - same missing-invariance bug as
casimirBasisDependent had; checked no other file references casimirUEA.
casimirUEA_mem_center's proof reuses casimir_commutes via a "regular representation"
trick (L acting on U(L) itself by left mult. through ι) rather than re-deriving the
same commutator computation - `regRep`/`regRep_apply`/`casimir_regRep_apply` in
Centrality.lean, all private.
Not claiming a new file yet this message; about to pick the next leaf sorry.
Investigated Sl2/Basic.lean's standardSl2ModuleLieRingModule/standardSl2ModuleLieModule:
these are genuinely hard (need to build a LieHom from the sl2-subalgebra into
Module.End K V from scratch, which in turn needs linear independence of {h,e,f} -
provable but only for CharZero/char≠2 K, not stated as a hypothesis currently).
Not claiming it; flagging for whoever tackles it that a CharZero (or char≠2)
hypothesis will likely need to be added to match Sl2/Classification.lean's later
assumptions - same issue the 2nd session flagged below for string_linearIndependent.
Status: in progress

### Claude (2nd session) - 2026-08-05
Done: Hydrogen/Basic.lean's crossComponent_bilinear, Casimir/Basic.lean's
casimirBasisDependent_basis_indep (no sorry, committed 548f2de). Marked
\leanok on both in the blueprint.
Now working on: Sl2/Classification.lean's string_linearIndependent - adding a
`[CharZero K]` hypothesis (needed: Mathlib's own
IsSl2Triple.HasPrimitiveVectorWith.pow_toEnd_f_ne_zero_of_eq_nat, which this
proof leans on, itself requires CharZero; without it the string can collapse
to 0 early, e.g. char-2 adjoint rep, n=2 - false as stated otherwise, same
pattern as the isSl2Triple fix in AngularMomentum/Basic.lean).
Found but NOT fixing: exists_stringLieSubmodule (and everything after it in
Sl2/Classification.lean: stringSpan_eq_top, string_isBasis, finrank_eq_succ,
classification, classification_n_eq_finrank_sub_one) is false as stated for
generic ambient `L` - `LieSubmodule K L M` demands invariance under *all* of
L, not just h,e,f, but the file's `L` is a fully generic LieAlgebra with no
assumption that it's spanned by {h,e,f}. It's only true when L is
(isomorphic to) `t.toLieSubalgebra K` itself, which matches how downstream
callers (AngularMomentum/Classification.lean, Sl2/CommutingActions.lean)
always instantiate it - but the file's own generic statement doesn't capture
that. Needs an architectural decision (add a "L is spanned by {h,e,f}"
hypothesis, or restructure the file's variables around the subalgebra type
directly) bigger than a leaf fix. Related to the other session's note above
about Sl2/Basic.lean needing CharZero/char≠2 for the same subalgebra
construction - likely worth tackling together.
Status: in progress

## Log (most recent first)

<!-- Move your entry here when done, with a one-line summary. -->
