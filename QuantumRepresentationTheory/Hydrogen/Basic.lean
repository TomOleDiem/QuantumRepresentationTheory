import Mathlib
import QuantumRepresentationTheory.AngularMomentum.Basic

/-!
# Hydrogen/Basic

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"The Runge–Lenz vector" (`sec:hyd-basic`). As decided
for the scope of this project, this is a purely algebraic model: `BoundStateRepresentation`
packages a finite-dimensional negative-energy eigenspace as *given* data, rather than
deriving it from Physlib's Hilbert-space Hamiltonian (`Physlib.QuantumMechanics.Hydrogen.Basic`).
-/

noncomputable section

namespace QuantumRepresentationTheory

/-- **Levi-Civita symbol** (`def:hyd-levi-civita`) on `Fin 3`. -/
def leviCivita (i j k : Fin 3) : ℤ :=
  if (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (1, 2, 0) ∨ (i, j, k) = (2, 0, 1) then 1
  else if (i, j, k) = (0, 2, 1) ∨ (i, j, k) = (2, 1, 0) ∨ (i, j, k) = (1, 0, 2) then -1
  else 0

variable {R : Type*} [Ring R]

/-- The `i`-th component of the cross product of `A B : Fin 3 → R`,
`(A × B)ᵢ = ∑ⱼₖ εᵢⱼₖ Aⱼ Bₖ`. -/
def crossComponent (A B : Fin 3 → R) (i : Fin 3) : R :=
  ∑ j, ∑ k, (leviCivita i j k : R) * (A j * B k)

/-- **Linearity of the cross-product components** (`thm:hyd-cross-linearity`):
each component is bilinear in `A`, `B`. -/
theorem crossComponent_bilinear (i : Fin 3) :
    (∀ A A' B : Fin 3 → R, crossComponent (A + A') B i =
      crossComponent A B i + crossComponent A' B i) ∧
    (∀ A B B' : Fin 3 → R, crossComponent A (B + B') i =
      crossComponent A B i + crossComponent A B' i) := by
  sorry

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- **Bound-state representation** (`def:hyd-bound-state`). The explicit representation
of the hydrogen Hamiltonian's dynamical symmetry algebra on a fixed negative-energy
eigenspace `V`: the angular momentum representation `(Jx,Jy,Jz)`, the (unnormalized)
Runge–Lenz operator `(Mx,My,Mz)`, and the physical parameters (mass `m`, Coulomb
constant `k`, energy eigenvalue `E < 0`). -/
structure BoundStateRepresentation extends AngularMomentumRepresentation V where
  Mx : Module.End ℂ V
  My : Module.End ℂ V
  Mz : Module.End ℂ V
  m : ℝ
  k : ℝ
  E : ℝ
  m_pos : 0 < m
  E_neg : E < 0

namespace BoundStateRepresentation

variable {V}

/-- **The rescaling constant is nonzero** (`thm:hyd-rescaling-nonzero`): on a
bound state (`E < 0`, `m > 0`), the scalar `-2E/m` is strictly positive. -/
theorem rescaling_pos (H : BoundStateRepresentation V) : 0 < -2 * H.E / H.m := by
  apply div_pos _ H.m_pos
  linarith [H.E_neg]

/-- The rescaling constant `√(-2E/m)`, well-defined by `rescaling_pos`. -/
def rescalingConst (H : BoundStateRepresentation V) : ℝ :=
  Real.sqrt (-2 * H.E / H.m)

theorem rescalingConst_pos (H : BoundStateRepresentation V) : 0 < H.rescalingConst :=
  Real.sqrt_pos.mpr H.rescaling_pos

/-- **Rescaled Runge–Lenz vector** (`def:hyd-rescaled-rl`): `A := M / √(-2E/m)`, chosen
so that `J` and `A` satisfy the commutation relations of two copies of `so(3)`
(`thm:hyd-two-factors-commute`). -/
def Ax (H : BoundStateRepresentation V) : Module.End ℂ V :=
  (H.rescalingConst⁻¹ : ℂ) • H.Mx

@[inherit_doc Ax] def Ay (H : BoundStateRepresentation V) : Module.End ℂ V :=
  (H.rescalingConst⁻¹ : ℂ) • H.My

@[inherit_doc Ax] def Az (H : BoundStateRepresentation V) : Module.End ℂ V :=
  (H.rescalingConst⁻¹ : ℂ) • H.Mz

end BoundStateRepresentation

end QuantumRepresentationTheory
