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

/-- Case `m ≤ n` of `clebsch_gordan_finrank`, proved by reindexing `k ↦ m - k` so that
the truncated subtraction `m + n - 2k` becomes genuine addition `(n - m) + 2k`, then
summing the resulting arithmetic progression via `Finset.sum_range_id_mul_two`. -/
private lemma clebsch_gordan_finrank_aux (m n : ℕ) (h : m ≤ n) :
    (m + 1) * (n + 1) = ∑ k ∈ Finset.range (m + 1), (m + n - 2 * k + 1) := by
  set d := n - m with hd_def
  have hn : n = m + d := by omega
  have hterm : ∀ k ∈ Finset.range (m + 1), (m + n - 2 * k + 1 : ℕ) = d + 2 * (m - k) + 1 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    omega
  rw [Finset.sum_congr rfl hterm]
  have hreflect := Finset.sum_range_reflect (fun k => d + 2 * k + 1) (m + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  have hgauss : ∑ k ∈ Finset.range (m + 1), k * 2 = (m + 1) * m := by
    have h2 := Finset.sum_range_id_mul_two (m + 1)
    rw [Finset.sum_mul] at h2
    simpa using h2
  have hexpand : ∑ k ∈ Finset.range (m + 1), (d + 2 * k + 1)
      = (m + 1) * (d + 1) + ∑ k ∈ Finset.range (m + 1), k * 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  rw [hexpand, hgauss, hn]
  ring

/-- **Clebsch–Gordan decomposition, dimension form** (`thm:sl2-clebsch-gordan`):
the numerical shadow `(m+1)(n+1) = ∑_{k=0}^{min(m,n)} (m+n-2k+1)` of the module
isomorphism `V(m) ⊗ V(n) ≅ ⊕_k V(m+n-2k)`. -/
theorem clebsch_gordan_finrank (m n : ℕ) :
    (m + 1) * (n + 1) = ∑ k ∈ Finset.range (min m n + 1), (m + n - 2 * k + 1) := by
  rcases le_total m n with h | h
  · rw [min_eq_left h]
    exact clebsch_gordan_finrank_aux m n h
  · rw [min_eq_right h, Nat.add_comm m n, mul_comm]
    exact clebsch_gordan_finrank_aux n m h

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
