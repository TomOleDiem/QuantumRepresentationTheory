import Mathlib
import QuantumRepresentationTheory.Representation.Basic

/-!
# Casimir/Basic

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"Construction" (`sec:cas-basic`).
-/

noncomputable section

namespace QuantumRepresentationTheory

open Module (Basis finBasis)

variable {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V]


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Basis-dependent Casimir element** (`def:cas-basis-dependent`). For a
representation `ρ` of `L` on `V`, a basis `b` of `L`, and its `Φ`-dual basis
(`LinearMap.BilinForm.dualBasis`), the Casimir operator is
`C_ρ = ∑ᵢ ρ(bᵢ) ρ(bⁱ)`. -/
def casimirBasisDependent (ρ : LieRepresentation K L V) (Φ : LinearMap.BilinForm K L)
    (hΦ : Φ.Nondegenerate) (b : Basis ι K L) : Module.End K V :=
  ∑ i, ρ (b i) * ρ (Φ.dualBasis hΦ b i)

/-- **Change-of-basis invariance** (`thm:cas-change-of-basis`): the operator
`casimirBasisDependent` does not depend on the choice of basis `b` of `L`. -/
theorem casimirBasisDependent_basis_indep {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (ρ : LieRepresentation K L V) (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate)
    (b : Basis ι K L) (b' : Basis ι' K L) :
    casimirBasisDependent ρ Φ hΦ b = casimirBasisDependent ρ Φ hΦ b' := by
  sorry

/-- **The Casimir operator** (`def:cas-casimir`): the common value of
`casimirBasisDependent`, computed using the canonical basis of a
finite-dimensional `L` supplied by `Module.finBasis`, independent of that
choice by `casimirBasisDependent_basis_indep`. -/
def casimir [FiniteDimensional K L] (ρ : LieRepresentation K L V)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate) : Module.End K V :=
  casimirBasisDependent ρ Φ hΦ (Module.finBasis K L)

end QuantumRepresentationTheory
