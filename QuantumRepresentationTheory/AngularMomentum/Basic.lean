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
  sorry

theorem comm_z_m (ρ : AngularMomentumRepresentation V) : ⁅ρ.Jz, ρ.Jm⁆ = -ρ.Jm := by
  sorry

theorem comm_p_m (ρ : AngularMomentumRepresentation V) :
    ⁅ρ.Jp, ρ.Jm⁆ = (2 : ℂ) • ρ.Jz := by
  sorry

/-- **Angular momentum generates an `sl₂`-triple** (`thm:am-is-sl2-triple`), via
`h := 2 • Jz`, `e := J+`, `f := J-` (the doubling of `Jz` reconciles the physicists'
normalization `[Jz,J±]=±J±` with the `sl₂`-triple normalization `[h,e]=2e`). -/
theorem isSl2Triple (ρ : AngularMomentumRepresentation V) :
    IsSl2Triple ((2 : ℂ) • ρ.Jz) ρ.Jp ρ.Jm := by
  sorry

end AngularMomentumRepresentation

end QuantumRepresentationTheory
