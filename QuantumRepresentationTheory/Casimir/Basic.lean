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
`C_ρ = ∑ᵢ ρ(bᵢ) ρ(bⁱ)`. `Φ` is required to be nondegenerate (so the dual
basis exists) and Lie-invariant (so the resulting operator commutes with the
representation, `Casimir.casimir_commutes`); the latter was missing from an
earlier version of this definition. -/
def casimirBasisDependent (ρ : LieRepresentation K L V) (Φ : LinearMap.BilinForm K L)
    (hΦ : Φ.Nondegenerate) (_hΦ_inv : Φ.lieInvariant L) (b : Basis ι K L) : Module.End K V :=
  ∑ i, ρ (b i) * ρ (Φ.dualBasis hΦ b i)

/-- Expansion of `z : L` in the basis `b` via pairing with the `Φ`-dual basis:
`z = ∑ⱼ Φ(bʲ, z) • bⱼ`. No symmetry of `Φ` is required. -/
private theorem expand_in_basis (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate)
    (b : Basis ι K L) (z : L) :
    z = ∑ j, Φ (Φ.dualBasis hΦ b j) z • b j := by
  have key : ∀ j, Φ (Φ.dualBasis hΦ b j) z = b.repr z j := by
    intro j
    conv_lhs => rw [← Basis.sum_repr b z]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul, LinearMap.BilinForm.apply_dualBasis_left]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · simp
  simp_rw [key]
  exact (Basis.sum_repr b z).symm

/-- Expansion of `x : L` in the `Φ`-dual basis `Φ.dualBasis hΦ b`:
`x = ∑ᵢ Φ(x, bᵢ) • bⁱ`. -/
private theorem expand_in_dualBasis (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate)
    (b : Basis ι K L) (x : L) :
    x = ∑ i, Φ x (b i) • Φ.dualBasis hΦ b i := by
  conv_lhs => rw [← Basis.sum_repr (Φ.dualBasis hΦ b) x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply]

/-- **Change-of-basis invariance** (`thm:cas-change-of-basis`): the operator
`casimirBasisDependent` does not depend on the choice of basis `b` of `L`.

Proof idea: expand each `b' k` in the `b`-basis, push `ρ` through the resulting
sum, swap the two (now single-indexed) sums, and recognize the inner sum as the
`expand_in_dualBasis` expansion of `bd i` in the `b'`-dual basis; this collapses
it straight back to `ρ (bd i)` without ever needing a change-of-basis matrix. -/
theorem casimirBasisDependent_basis_indep {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (ρ : LieRepresentation K L V) (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate)
    (hΦ_inv : Φ.lieInvariant L) (b : Basis ι K L) (b' : Basis ι' K L) :
    casimirBasisDependent ρ Φ hΦ hΦ_inv b = casimirBasisDependent ρ Φ hΦ hΦ_inv b' := by
  classical
  set bd := Φ.dualBasis hΦ b with hbd_def
  set b'd := Φ.dualBasis hΦ b' with hb'd_def
  show ∑ i, ρ (b i) * ρ (bd i) = ∑ k, ρ (b' k) * ρ (b'd k)
  have hrho : ∀ k, ρ (b' k) = ∑ i, Φ (bd i) (b' k) • ρ (b i) := by
    intro k
    conv_lhs => rw [expand_in_basis Φ hΦ b (b' k)]
    rw [map_sum]
    simp_rw [map_smul, ← hbd_def]
  have step1 : ∑ k, ρ (b' k) * ρ (b'd k)
      = ∑ k, ∑ i, Φ (bd i) (b' k) • (ρ (b i) * ρ (b'd k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrho k, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc]
  have step2 : ∀ i, ∑ k, Φ (bd i) (b' k) • (ρ (b i) * ρ (b'd k)) = ρ (b i) * ρ (bd i) := by
    intro i
    have hcollapse : ∑ k, Φ (bd i) (b' k) • ρ (b'd k) = ρ (bd i) := by
      conv_rhs => rw [expand_in_dualBasis Φ hΦ b' (bd i)]
      rw [map_sum]
      simp_rw [map_smul, ← hb'd_def]
    rw [← hcollapse, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_smul_comm]
  rw [step1, Finset.sum_comm]
  simp_rw [step2]

/-- **The Casimir operator** (`def:cas-casimir`): the common value of
`casimirBasisDependent`, computed using the canonical basis of a
finite-dimensional `L` supplied by `Module.finBasis`, independent of that
choice by `casimirBasisDependent_basis_indep`. -/
def casimir [FiniteDimensional K L] (ρ : LieRepresentation K L V)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L) :
    Module.End K V :=
  casimirBasisDependent ρ Φ hΦ hΦ_inv (Module.finBasis K L)

end QuantumRepresentationTheory
