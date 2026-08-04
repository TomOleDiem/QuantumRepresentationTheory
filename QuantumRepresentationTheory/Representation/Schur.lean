import Mathlib

/-!
# Representation/Schur

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"Schur's lemma" (`sec:rep-schur`).
-/

noncomputable section

namespace QuantumRepresentationTheory

variable (K L M : Type*) [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- **Eigenspace of an endomorphism is nonzero** (`thm:rep-eigenspace-nonzero`).
If `K` is algebraically closed and `M` is nonzero finite-dimensional, every
`f : M →ₗ[K] M` has a scalar `c` with `ker (f - c • id) ≠ ⊥`. -/
theorem exists_ker_smul_id_ne_bot [IsAlgClosed K] [FiniteDimensional K M] [Nontrivial M]
    (f : Module.End K M) : ∃ c : K, LinearMap.ker (f - c • (1 : Module.End K M)) ≠ ⊥ := by
  obtain ⟨c, hc⟩ := f.exists_eigenvalue
  exact ⟨c, by rwa [← Module.End.eigenspace_def, ← Module.End.hasEigenvalue_iff]⟩

/-- **Schur's lemma** (`thm:rep-schur`). A `LieModuleHom` self-map of a
finite-dimensional irreducible Lie module, over an algebraically closed
field, is scalar multiplication by some `c : K`. -/
theorem schur [IsAlgClosed K] [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
    (f : M →ₗ⁅K,L⁆ M) : ∃ c : K, (f : M →ₗ[K] M) = c • LinearMap.id := by
  sorry

end QuantumRepresentationTheory
