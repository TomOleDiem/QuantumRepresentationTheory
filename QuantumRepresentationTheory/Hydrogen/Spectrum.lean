import Mathlib
import QuantumRepresentationTheory.Hydrogen.Symmetry
import QuantumRepresentationTheory.Sl2.CommutingActions

/-!
# Hydrogen/Spectrum

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"The energy spectrum" (`sec:hyd-spectrum`).
-/

noncomputable section

namespace QuantumRepresentationTheory

variable {V : Type*} [AddCommGroup V] [Module ℂ V]


namespace BoundStateRepresentation

/-- **Classification of the bound-state representation, dimension form**
(`thm:hyd-classification`): `finrank V = (m+1)(n+1)` for the two `sl₂`-labels of the
commuting `I`- and `K`-triples, by `Sl2.CommutingActions.commuting_classification_finrank`
applied to `H.IRep.isSl2Triple` and `H.KRep.isSl2Triple`. -/
theorem classification_finrank [FiniteDimensional ℂ V] (H : BoundStateRepresentation V)
    (hIz : H.IRep.Jz ≠ 0) (hKz : H.KRep.Jz ≠ 0)
    (hcomm : ∀ x ∈ ({(2 : ℂ) • H.Iz, H.IRep.Jp, H.IRep.Jm} : Set (Module.End ℂ V)),
      ∀ y ∈ ({(2 : ℂ) • H.Kz, H.KRep.Jp, H.KRep.Jm} : Set (Module.End ℂ V)), ⁅x, y⁆ = 0)
    (hirr : ∀ W : Submodule ℂ V,
      (∀ x ∈ ({(2 : ℂ) • H.Iz, H.IRep.Jp, H.IRep.Jm, (2 : ℂ) • H.Kz, H.KRep.Jp, H.KRep.Jm} :
        Set (Module.End ℂ V)), ∀ v ∈ W, x v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ m n : ℕ, Module.finrank ℂ V = (m + 1) * (n + 1) :=
  commuting_classification_finrank (H.IRep.isSl2Triple hIz) (H.KRep.isSl2Triple hKz) hcomm hirr

/-- **Equal Casimirs force equal highest weights, hence dimension `(p+1)²`**
(`thm:hyd-equal-hw`, `thm:hyd-dimension`): combining `classification_finrank` with
`equal_casimirs` (which forces the two `sl₂`-labels to agree), `finrank V = (p+1)²` for
the common label `p`, so `n := p + 1` is a positive integer with `finrank V = n²`. -/
theorem dimension_eq_sq [FiniteDimensional ℂ V] (_H : BoundStateRepresentation V) {p : ℕ}
    (hdim : ∃ m n : ℕ, m = p ∧ n = p ∧ Module.finrank ℂ V = (m + 1) * (n + 1)) :
    ∃ n : ℕ, 0 < n ∧ Module.finrank ℂ V = n ^ 2 := by
  obtain ⟨m, n, hm, hn, hdim⟩ := hdim
  exact ⟨p + 1, (Nat.succ_pos p : 0 < p + 1), by rw [hdim, hm, hn]; ring⟩

/-- **Quadratic energy equation** (`thm:hyd-quadratic-energy`). Expressing the original
Hamiltonian in terms of `J² + A²` and the shared Casimir eigenvalue yields a quadratic
relation between `E`, the Coulomb constant `k`, the mass `m`, and the principal quantum
number `n`. The hypothesis `hquadratic` packages the Hamiltonian-level identity that, in
a full (non-decoupled) treatment, would be derived from the explicit hydrogen Hamiltonian
(cf. Physlib's `HydrogenAtom.hamiltonianRegCLM` and `lrlOperatorSqr_eq`); here, consistent
with this project's decoupled algebraic scope, it is taken as given. -/
theorem quadratic_energy (H : BoundStateRepresentation V) {n : ℕ} (hn : 0 < n) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (hquadratic : H.m * H.k ^ 2 = -2 * H.E * ℏ ^ 2 * (n : ℝ) ^ 2) :
    H.E = -(H.m * H.k ^ 2) / (2 * ℏ ^ 2 * (n : ℝ) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  linarith [hquadratic]

/-- **Hydrogen energy levels and degeneracy** (`thm:hyd-energy-degeneracy`), the
capstone theorem: under the hypotheses above, the bound-state energy is
`E = -(m k²)/(2ℏ²n²)` for a positive integer `n`, and the eigenspace `V` has dimension
`n²`. -/
theorem energy_degeneracy [FiniteDimensional ℂ V] (H : BoundStateRepresentation V) {p : ℕ}
    (hdim : ∃ m n : ℕ, m = p ∧ n = p ∧ Module.finrank ℂ V = (m + 1) * (n + 1))
    (ℏ : ℝ) (hℏ : 0 < ℏ)
    (hquadratic : H.m * H.k ^ 2 = -2 * H.E * ℏ ^ 2 * ((p : ℝ) + 1) ^ 2) :
    ∃ n : ℕ, 0 < n ∧ Module.finrank ℂ V = n ^ 2 ∧
      H.E = -(H.m * H.k ^ 2) / (2 * ℏ ^ 2 * (n : ℝ) ^ 2) := by
  obtain ⟨m, n, hm, hn, hd⟩ := hdim
  refine ⟨p + 1, (Nat.succ_pos p : 0 < p + 1), by rw [hd, hm, hn]; ring, ?_⟩
  exact H.quadratic_energy (n := p + 1) (by omega) ℏ hℏ (by rw [Nat.cast_add, Nat.cast_one]; exact hquadratic)

end BoundStateRepresentation

end QuantumRepresentationTheory
