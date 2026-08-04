import Mathlib
import QuantumRepresentationTheory.Sl2.Basic

/-!
# Sl2/ClebschGordan

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"Clebsch–Gordan decomposition" (`sec:sl2-cg`).
-/

noncomputable section

namespace QuantumRepresentationTheory

open scoped TensorProduct DirectSum

variable {K : Type*} [Field K]

/-- **Clebsch–Gordan decomposition, dimension form** (`thm:sl2-clebsch-gordan`):
the numerical shadow `(m+1)(n+1) = ∑_{k=0}^{min(m,n)} (m+n-2k+1)` of the module
isomorphism `V(m) ⊗ V(n) ≅ ⊕_k V(m+n-2k)`. -/
theorem clebsch_gordan_finrank (m n : ℕ) :
    (m + 1) * (n + 1) = ∑ k ∈ Finset.range (min m n + 1), (m + n - 2 * k + 1) := by
  sorry

/-- **Clebsch–Gordan decomposition, vector-space form** (`thm:sl2-clebsch-gordan`):
`V(m) ⊗ V(n)` is linearly isomorphic to `⊕_{k=0}^{min(m,n)} V(m+n-2k)`.

TODO: as with `Sl2.CommutingActions.commuting_classification`, the isomorphism
here is only asserted at the vector-space level; upgrading it to an isomorphism
of `sl₂`-modules (diagonal action on the left, direct sum action on the right,
both via `standardSl2ModuleLieRingModule`) is future work. -/
theorem clebsch_gordan (m n : ℕ) :
    Nonempty (StandardSl2Module K m ⊗[K] StandardSl2Module K n ≃ₗ[K]
      ⨁ _k : Fin (min m n + 1), StandardSl2Module K (m + n - 2 * (_k : ℕ))) := by
  sorry

end QuantumRepresentationTheory
