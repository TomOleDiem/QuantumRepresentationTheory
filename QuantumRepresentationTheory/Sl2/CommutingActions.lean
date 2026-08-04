import Mathlib
import QuantumRepresentationTheory.Sl2.Basic
import QuantumRepresentationTheory.Representation.Basic

/-!
# Sl2/CommutingActions

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"Commuting $\sltwo$-actions and tensor products"
(`sec:sl2-commuting`) — the largest hidden node in the roadmap: without this, equal
Casimir eigenvalues for two commuting `sl₂`-triples do not by themselves give a
dimension formula.
-/

noncomputable section

namespace QuantumRepresentationTheory

open scoped TensorProduct

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


/-- **Classification of jointly irreducible commuting $\sltwo$-actions**
(`thm:sl2-commuting-classification`). Two `sl₂`-triples of operators on a
finite-dimensional space `V`, commuting with each other and with no proper
subspace invariant under both, force `V` to be linearly isomorphic to a tensor
product `V(m) ⊗ V(n)` of standard modules.

TODO: the isomorphism produced here is only asserted at the level of the
underlying `K`-vector spaces; the stronger statement (that it intertwines
`h1,e1,f1,h2,e2,f2` with the actions on the two tensor factors from
`standardSl2ModuleLieRingModule`) is future work, tracked alongside
`def:rep-bridge`. -/
theorem commuting_classification [IsAlgClosed K] [CharZero K] [FiniteDimensional K V]
    {h1 e1 f1 h2 e2 f2 : Module.End K V}
    (t1 : IsSl2Triple h1 e1 f1) (t2 : IsSl2Triple h2 e2 f2)
    (hcomm : ∀ x ∈ ({h1, e1, f1} : Set (Module.End K V)),
      ∀ y ∈ ({h2, e2, f2} : Set (Module.End K V)), ⁅x, y⁆ = 0)
    (hirr : ∀ W : Submodule K V,
      (∀ x ∈ ({h1, e1, f1, h2, e2, f2} : Set (Module.End K V)), ∀ v ∈ W, x v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ m n : ℕ, Nonempty (V ≃ₗ[K] StandardSl2Module K m ⊗[K] StandardSl2Module K n) := by
  sorry

/-- **Dimension consequence** of `commuting_classification`: `finrank K V = (m+1)(n+1)`. -/
theorem commuting_classification_finrank [IsAlgClosed K] [CharZero K] [FiniteDimensional K V]
    {h1 e1 f1 h2 e2 f2 : Module.End K V}
    (t1 : IsSl2Triple h1 e1 f1) (t2 : IsSl2Triple h2 e2 f2)
    (hcomm : ∀ x ∈ ({h1, e1, f1} : Set (Module.End K V)),
      ∀ y ∈ ({h2, e2, f2} : Set (Module.End K V)), ⁅x, y⁆ = 0)
    (hirr : ∀ W : Submodule K V,
      (∀ x ∈ ({h1, e1, f1, h2, e2, f2} : Set (Module.End K V)), ∀ v ∈ W, x v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ m n : ℕ, Module.finrank K V = (m + 1) * (n + 1) := by
  sorry

end QuantumRepresentationTheory
