import Mathlib
import QuantumRepresentationTheory.Representation.Basic

/-!
# AngularMomentum/Basic

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"The algebraic representation" (`sec:am-basic`).
As decided for the scope of this project, this is a purely algebraic model
(finite-dimensional operators on a `ℂ`-vector space): it does not depend on
Physlib's Hilbert-space / self-adjoint-operator machinery.
-/

noncomputable section

namespace QuantumRepresentationTheory

variable (V : Type*) [AddCommGroup V] [Module ℂ V]


/-- **Angular momentum representation** (`def:am-representation`). Three operators
`Jx, Jy, Jz` on a state space `V`, satisfying the `so(3)` commutation relations
`[Jx,Jy] = iJz` and cyclic permutations. (The physical requirement that they be
self-adjoint on a Hilbert space is out of scope for this algebraic model.) -/
structure AngularMomentumRepresentation where
  Jx : Module.End ℂ V
  Jy : Module.End ℂ V
  Jz : Module.End ℂ V
  comm_xy : ⁅Jx, Jy⁆ = Complex.I • Jz
  comm_yz : ⁅Jy, Jz⁆ = Complex.I • Jx
  comm_zx : ⁅Jz, Jx⁆ = Complex.I • Jy

namespace AngularMomentumRepresentation

variable {V}

/-- **Ladder operators** (`def:am-ladder`). `J± := Jx ± iJy`. -/
def Jp (ρ : AngularMomentumRepresentation V) : Module.End ℂ V := ρ.Jx + Complex.I • ρ.Jy

@[inherit_doc Jp]
def Jm (ρ : AngularMomentumRepresentation V) : Module.End ℂ V := ρ.Jx - Complex.I • ρ.Jy

/-- **Commutation relations for the ladder operators** (`thm:am-commutators`):
`[Jz, J±] = ±J±` and `[J+, J-] = 2Jz`. -/
theorem comm_z_p (ρ : AngularMomentumRepresentation V) : ⁅ρ.Jz, ρ.Jp⁆ = ρ.Jp := by
  have hzy : ⁅ρ.Jz, ρ.Jy⁆ = -(Complex.I • ρ.Jx) := by rw [← lie_skew, ρ.comm_yz]
  simp only [Jp, lie_add, lie_smul, ρ.comm_zx, hzy, smul_neg, smul_smul,
    Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  abel

theorem comm_z_m (ρ : AngularMomentumRepresentation V) : ⁅ρ.Jz, ρ.Jm⁆ = -ρ.Jm := by
  have hzy : ⁅ρ.Jz, ρ.Jy⁆ = -(Complex.I • ρ.Jx) := by rw [← lie_skew, ρ.comm_yz]
  simp only [Jm, lie_sub, lie_smul, ρ.comm_zx, hzy, smul_neg, smul_smul,
    Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  abel

theorem comm_p_m (ρ : AngularMomentumRepresentation V) :
    ⁅ρ.Jp, ρ.Jm⁆ = (2 : ℂ) • ρ.Jz := by
  have h1 : ⁅ρ.Jx, ρ.Jm⁆ = ρ.Jz := by
    simp only [Jm, lie_sub, lie_self, lie_smul, ρ.comm_xy, smul_smul, Complex.I_mul_I,
      zero_sub, neg_smul, one_smul, neg_neg]
  have hyx : ⁅ρ.Jy, ρ.Jx⁆ = -(Complex.I • ρ.Jz) := by rw [← lie_skew, ρ.comm_xy]
  have h2 : ⁅ρ.Jy, ρ.Jm⁆ = -(Complex.I • ρ.Jz) := by
    simp only [Jm, lie_sub, lie_self, lie_smul, hyx, smul_zero, sub_zero]
  have hsmul : ⁅Complex.I • ρ.Jy, ρ.Jm⁆ = Complex.I • ⁅ρ.Jy, ρ.Jm⁆ := by
    rw [← lie_skew, lie_smul, ← lie_skew ρ.Jy ρ.Jm, smul_neg]
  have h3 : ⁅ρ.Jp, ρ.Jm⁆ = ⁅ρ.Jx, ρ.Jm⁆ + Complex.I • ⁅ρ.Jy, ρ.Jm⁆ := by
    rw [Jp, add_lie, hsmul]
  rw [h3, h1, h2, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg,
    two_smul]

/-- **Angular momentum generates an `sl₂`-triple** (`thm:am-is-sl2-triple`), via
`h := 2 • Jz`, `e := J+`, `f := J-` (the doubling of `Jz` reconciles the physicists'
normalization `[Jz,J±]=±J±` with the `sl₂`-triple normalization `[h,e]=2e`).

The hypothesis `ρ.Jz ≠ 0` is necessary: the all-zero representation
(`Jx = Jy = Jz = 0`) satisfies every field of `AngularMomentumRepresentation`
but gives `h = 2 • Jz = 0`, which `IsSl2Triple` explicitly excludes
(`h_ne_zero`) — the trivial, spin-`0` representation does not generate an
honest copy of `sl₂` inside `End(V)`. -/
theorem isSl2Triple (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0) :
    IsSl2Triple ((2 : ℂ) • ρ.Jz) ρ.Jp ρ.Jm where
  h_ne_zero := smul_ne_zero (by norm_num) hz
  lie_e_f := comm_p_m ρ
  lie_h_e_nsmul := by
    have hcast : (2 : ℕ) • ρ.Jz = (2 : ℂ) • ρ.Jz := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; norm_num
    rw [← hcast, nsmul_lie, comm_z_p]
  lie_h_f_nsmul := by
    have hcast : (2 : ℕ) • ρ.Jz = (2 : ℂ) • ρ.Jz := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; norm_num
    rw [← hcast, nsmul_lie, comm_z_m, smul_neg]

end AngularMomentumRepresentation

end QuantumRepresentationTheory
