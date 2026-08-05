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


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expansion of `z : L` in the basis `b` via pairing with the dual basis:
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

/-- Expansion of `x : L` in the dual basis `Φ.dualBasis hΦ b`:
`x = ∑ᵢ Φ(x, bᵢ) • bⁱ`. -/
private theorem expand_in_dualBasis (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate)
    (b : Basis ι K L) (x : L) :
    x = ∑ i, Φ x (b i) • Φ.dualBasis hΦ b i := by
  conv_lhs => rw [← Basis.sum_repr (Φ.dualBasis hΦ b) x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply]

private theorem assoc_leibniz (a x z : Module.End K V) :
    ⁅a, x * z⁆ = ⁅a, x⁆ * z + x * ⁅a, z⁆ := by
  simp only [LieRing.of_associative_ring_bracket]
  noncomm_ring

/-- **The Casimir element commutes with the generators** (`thm:cas-commutes-generators`). -/
theorem casimir_commutes [FiniteDimensional K L] (ρ : LieRepresentation K L V)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L) (y : L) :
    ⁅ρ y, casimir ρ Φ hΦ hΦ_inv⁆ = 0 := by
  classical
  set b := Module.finBasis K L with hb_def
  set b' := Φ.dualBasis hΦ b with hb'_def
  show ⁅ρ y, ∑ i, ρ (b i) * ρ (b' i)⁆ = 0
  rw [lie_sum]
  have hterm : ∀ i, ⁅ρ y, ρ (b i) * ρ (b' i)⁆ = ρ ⁅y, b i⁆ * ρ (b' i) + ρ (b i) * ρ ⁅y, b' i⁆ := by
    intro i
    rw [assoc_leibniz, ← ρ.map_lie, ← ρ.map_lie]
  simp_rw [hterm, Finset.sum_add_distrib]
  have hexp1 : ∀ i, (⁅y, b i⁆ : L) = ∑ j, Φ (b' j) ⁅y, b i⁆ • b j := fun i =>
    expand_in_basis Φ hΦ b _
  have hexp2 : ∀ i, (⁅y, b' i⁆ : L) = ∑ j, Φ ⁅y, b' i⁆ (b j) • b' j := fun i =>
    expand_in_dualBasis Φ hΦ b _
  have hinv : ∀ i j, Φ (b' j) ⁅y, b i⁆ = -Φ ⁅y, b' j⁆ (b i) := fun i j => by
    have h := hΦ_inv y (b' j) (b i)
    linear_combination h
  have step1 : ∀ i, ρ ⁅y, b i⁆ * ρ (b' i)
      = -∑ j, Φ ⁅y, b' j⁆ (b i) • (ρ (b j) * ρ (b' i)) := by
    intro i
    rw [hexp1 i, map_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_mul_assoc, hinv i j, neg_smul]
  have step2 : ∀ i, ρ (b i) * ρ ⁅y, b' i⁆
      = ∑ j, Φ ⁅y, b' i⁆ (b j) • (ρ (b i) * ρ (b' j)) := by
    intro i
    conv_lhs => rw [hexp2 i]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, mul_smul_comm]
  have hswap : (∑ i, ∑ j, Φ ⁅y, b' i⁆ (b j) • (ρ (b i) * ρ (b' j)))
      = ∑ i, ∑ j, Φ ⁅y, b' j⁆ (b i) • (ρ (b j) * ρ (b' i)) :=
    Finset.sum_comm
  simp_rw [step1, step2, hswap]
  rw [← Finset.sum_add_distrib]
  simp

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
    [LieModule.IsIrreducible K L V] (Φ : LinearMap.BilinForm K L) (hΦ : Φ.Nondegenerate)
    (hΦ_inv : Φ.lieInvariant L) :
    ∃ c : K, casimir (LieModule.toEnd K L V) Φ hΦ hΦ_inv = c • (1 : Module.End K V) := by
  set C := casimir (LieModule.toEnd K L V) Φ hΦ hΦ_inv with hC_def
  have hcomm : ∀ x : L, ⁅LieModule.toEnd K L V x, C⁆ = 0 :=
    casimir_commutes (LieModule.toEnd K L V) Φ hΦ hΦ_inv
  have hg_map_lie : ∀ {x : L} {m : V}, C ⁅x, m⁆ = ⁅x, C m⁆ := by
    intro x m
    have h := hcomm x
    rw [LieRing.of_associative_ring_bracket, sub_eq_zero] at h
    have hx : LieModule.toEnd K L V x * C = C * LieModule.toEnd K L V x := h
    have := LinearMap.congr_fun hx m
    simpa [LieModule.toEnd_apply_apply] using this.symm
  let g : V →ₗ⁅K,L⁆ V := { C with map_lie' := hg_map_lie }
  obtain ⟨c, hc⟩ := schur K L V g
  refine ⟨c, ?_⟩
  have hgC : (g : V →ₗ[K] V) = C := rfl
  rw [hgC] at hc
  rw [hc, Module.End.one_eq_id]

end QuantumRepresentationTheory
