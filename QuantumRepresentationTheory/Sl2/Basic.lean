import Mathlib

/-!
# Sl2/Basic

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"$\sltwo$-triples and primitive vectors"
(`sec:sl2-basic`). The primitive-vector string calculus itself is already in
Mathlib (`Mathlib.Algebra.Lie.Sl2`); the only new content here is the
explicit standard module `V(n)` (`def:sl2-standard-module`).
-/

noncomputable section

namespace QuantumRepresentationTheory

/-- **Standard module `V(n)`, underlying carrier** (`def:sl2-standard-module`).
An `(n+1)`-dimensional `K`-vector space with standard basis `v_0, …, v_n`. -/
def StandardSl2Module (K : Type*) (n : ℕ) : Type _ := Fin (n + 1) → K

variable {K : Type*} [Field K] {n : ℕ}

instance : AddCommGroup (StandardSl2Module K n) :=
  inferInstanceAs (AddCommGroup (Fin (n + 1) → K))

instance : Module K (StandardSl2Module K n) :=
  inferInstanceAs (Module K (Fin (n + 1) → K))

/-- The standard basis vector `v_k` of `StandardSl2Module K n`. -/
def StandardSl2Module.v (k : Fin (n + 1)) : StandardSl2Module K n :=
  Pi.single k 1

variable {L : Type*} [LieRing L] [LieAlgebra K L] {h e f : L}

/-- **Standard module `V(n)`, module structure** (`def:sl2-standard-module`).
Given an `sl₂`-triple `(h,e,f)` in `L`, `StandardSl2Module K n` carries a
`LieRingModule` structure for the generated subalgebra, with
`h ⬝ v k = (n - 2k) • v k`, `f ⬝ v k = v (k+1)` (and `f ⬝ v n = 0`), and
`e ⬝ v k = (k * (n - k + 1)) • v (k-1)` (and `e ⬝ v 0 = 0`). -/
@[reducible] def standardSl2ModuleLieRingModule (t : IsSl2Triple h e f) :
    LieRingModule (↥(t.toLieSubalgebra (R := K))) (StandardSl2Module K n) := by
  sorry

/-- **Standard module `V(n)`, module structure, continued**
(`def:sl2-standard-module`). The `LieModule` axioms for
`standardSl2ModuleLieRingModule`. -/
theorem standardSl2ModuleLieModule (t : IsSl2Triple h e f) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    LieModule K (↥(t.toLieSubalgebra (R := K))) (StandardSl2Module K n) := by
  sorry

end QuantumRepresentationTheory
