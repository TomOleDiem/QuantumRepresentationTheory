import Mathlib
import QuantumRepresentationTheory.Casimir.Basic
import QuantumRepresentationTheory.Representation.Schur

/-!
# Casimir/Centrality

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"Centrality and the scalar action" (`sec:cas-centrality`).
-/

noncomputable section

namespace QuantumRepresentationTheory

open Module (Basis finBasis)

variable {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V]


/-- **The Casimir element commutes with the generators** (`thm:cas-commutes-generators`). -/
theorem casimir_commutes [FiniteDimensional K L] (ρ : LieRepresentation K L V)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate) (y : L) :
    ⁅ρ y, casimir ρ Φ hΦ⁆ = 0 := by
  sorry

/-- The Casimir element of the adjoint representation, as an element of the universal
enveloping algebra `U(L)` itself (rather than as an operator via some `ρ`):
`C = ∑ᵢ ι(bᵢ) ι(bⁱ)`. -/
def casimirUEA [FiniteDimensional K L] (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate) :
    UniversalEnvelopingAlgebra K L :=
  ∑ i, UniversalEnvelopingAlgebra.ι K (finBasis K L i) *
      UniversalEnvelopingAlgebra.ι K (Φ.dualBasis hΦ (finBasis K L) i)

/-- **Centrality of the Casimir element** (`thm:cas-central`). The correct ambient object
is `Subalgebra.center`, not `Subring.center`, since we need `K`-linearity of the
centralizing condition. -/
theorem casimirUEA_mem_center [FiniteDimensional K L] (Φ : LinearMap.BilinForm K L)
    (hΦ : Φ.Nondegenerate) :
    casimirUEA Φ hΦ ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L) := by
  sorry

variable [LieRingModule L V] [LieModule K L V]

/-- **A central element gives a `LieModuleHom`** (`thm:cas-central-intertwines`). If `z`
is central in `U(L)`, its image under the extension of `LieModule.toEnd K L V` commutes
with `LieModule.toEnd K L V x` for every `x : L`. -/
theorem central_commutes_toEnd (z : UniversalEnvelopingAlgebra K L)
    (hz : z ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L)) (x : L) :
    UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) z * LieModule.toEnd K L V x =
      LieModule.toEnd K L V x * UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) z := by
  sorry

/-- **Schur gives a scalar Casimir** (`thm:cas-scalar`). -/
theorem casimir_scalar [IsAlgClosed K] [FiniteDimensional K L] [FiniteDimensional K V]
    [LieModule.IsIrreducible K L V] (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate) :
    ∃ c : K, casimir (LieModule.toEnd K L V) Φ hΦ = c • (1 : Module.End K V) := by
  sorry

end QuantumRepresentationTheory
