import Mathlib
import QuantumRepresentationTheory.Sl2.Basic

/-!
# Sl2/Classification

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"Classification of irreducible $\sltwo$-modules"
(`sec:sl2-classification`).
-/

noncomputable section

namespace QuantumRepresentationTheory

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    {h e f : L} {m : M} {n : ℕ}

/-- The vectors `m, fm, …, fⁿm` of the primitive-vector string, indexed by `Fin (n+1)`. -/
def stringVecs (f : L) (m : M) (n : ℕ) (k : Fin (n + 1)) : M :=
  (LieModule.toEnd K L M f ^ (k : ℕ)) m

/-- **Linear independence of the primitive-vector string** (`thm:sl2-string-independent`). -/
theorem string_linearIndependent {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) :
    LinearIndependent K (stringVecs (K := K) f m n) := by
  sorry

/-- The span of the primitive-vector string, as a plain `K`-submodule. -/
def stringSpan (f : L) (m : M) (n : ℕ) : Submodule K M :=
  Submodule.span K (Set.range (stringVecs (K := K) f m n))

/-- **The string spans a Lie submodule** (`thm:sl2-string-submodule`): the span of the
string is invariant under `h`, `e`, and `f`, hence underlies a `LieSubmodule`. -/
theorem exists_stringLieSubmodule {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) :
    ∃ N : LieSubmodule K L M, (N : Submodule K M) = stringSpan f m n := by
  sorry

/-- **Irreducibility forces the string to span** (`thm:sl2-irreducible-spans`). -/
theorem stringSpan_eq_top [LieModule.IsIrreducible K L M] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) (N : LieSubmodule K L M)
    (hN : (N : Submodule K M) = stringSpan f m n) : N = ⊤ := by
  sorry

/-- **Basis theorem** (`thm:sl2-basis-theorem`): for `M` irreducible with primitive vector
`m` of weight `n`, the string `m, fm, …, fⁿm` is a basis of `M`. -/
theorem string_isBasis [LieModule.IsIrreducible K L M] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) :
    LinearIndependent K (stringVecs (K := K) f m n) ∧
      Submodule.span K (Set.range (stringVecs (K := K) f m n)) = ⊤ := by
  sorry

/-- **Basis theorem, dimension count** (`thm:sl2-basis-theorem`). -/
theorem finrank_eq_succ [LieModule.IsIrreducible K L M] [FiniteDimensional K M]
    {t : IsSl2Triple h e f} (P : t.HasPrimitiveVectorWith m (n : K)) :
    Module.finrank K M = n + 1 := by
  sorry

/-- **Classification of irreducible $\sltwo$-modules** (`thm:sl2-classification`).
Every finite-dimensional irreducible module for an `sl₂`-triple, over an algebraically
closed field of characteristic zero, is isomorphic (as a module for the generated
subalgebra) to the standard module `V(n)` for a unique `n`. -/
theorem classification [IsAlgClosed K] [CharZero K] [FiniteDimensional K M]
    [LieModule.IsIrreducible K L M] (t : IsSl2Triple h e f) :
    ∃ n : ℕ, letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
      Nonempty (M ≃ₗ⁅K, ↥(t.toLieSubalgebra (R := K))⁆ StandardSl2Module K n) := by
  sorry

/-- **Uniqueness of the highest weight** (`thm:sl2-uniqueness-hw`): the `n` produced by
`classification` is determined by `M` alone, namely `n = finrank K M - 1`. -/
theorem classification_n_eq_finrank_sub_one [IsAlgClosed K] [CharZero K] [FiniteDimensional K M]
    [LieModule.IsIrreducible K L M] (t : IsSl2Triple h e f) {n : ℕ}
    (hn : letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
      Nonempty (M ≃ₗ⁅K, ↥(t.toLieSubalgebra (R := K))⁆ StandardSl2Module K n)) :
    n = Module.finrank K M - 1 := by
  sorry

end QuantumRepresentationTheory
