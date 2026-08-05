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
  haveI := LieModule.nontrivial_of_isIrreducible K L M
  obtain ⟨c, hc⟩ := exists_ker_smul_id_ne_bot K M (f : Module.End K M)
  set g : M →ₗ⁅K,L⁆ M := f - c • LieModuleHom.id with hg_def
  have hg_coe : (g : M →ₗ[K] M) = (f : M →ₗ[K] M) - c • (1 : Module.End K M) := by
    ext m
    simp [hg_def, LieModuleHom.sub_apply, LieModuleHom.smul_apply, LieModuleHom.id_apply]
  have hg_ker_ne_bot : g.ker ≠ ⊥ := by
    rw [Ne, ← LieSubmodule.toSubmodule_inj, LieModuleHom.ker_toSubmodule,
      LieSubmodule.bot_toSubmodule, hg_coe]
    exact hc
  haveI : Nontrivial g.ker := (LieSubmodule.nontrivial_iff_ne_bot K L M).mpr hg_ker_ne_bot
  have hg_ker_top : g.ker = ⊤ := LieSubmodule.eq_top_of_isIrreducible K L M g.ker
  have hg_zero : g = 0 := by
    ext m
    have hm : m ∈ g.ker := hg_ker_top ▸ LieSubmodule.mem_top m
    simpa using hm
  refine ⟨c, ?_⟩
  have : (f : M →ₗ[K] M) - c • (1 : Module.End K M) = 0 := hg_coe ▸ congrArg _ hg_zero
  have := sub_eq_zero.mp this
  rwa [Module.End.one_eq_id] at this

end QuantumRepresentationTheory
