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
  constructor
  · intro A A' B
    simp only [crossComponent, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  · intro A B B'
    simp only [crossComponent, Pi.add_apply, mul_add, Finset.sum_add_distrib]

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- **Bound-state representation** (`def:hyd-bound-state`). The explicit representation
of the hydrogen Hamiltonian's dynamical symmetry algebra on a fixed negative-energy
eigenspace `V`: the angular momentum representation `(Jx,Jy,Jz)`, the (unnormalized)
Runge–Lenz operator `(Mx,My,Mz)`, the physical parameters (mass `m`, Coulomb constant
`k`, energy eigenvalue `E < 0`), and the `so(4)` commutation relations tying them
together: `M` transforms as a vector under `J` (`JM_*`), and `M`'s self-commutator
closes back onto `J`, rescaled by the (fixed) energy eigenvalue (`MM_*`). This is the
standard quantum Runge–Lenz algebra for the hydrogen atom (e.g. Sakurai's or Griffiths'
treatment of the hidden `SO(4)` symmetry); on the fixed negative-energy eigenspace `V`
it is genuine data about the representation, not derivable from the `AngularMomentumRepresentation`
axioms alone, so it is taken as given here, consistent with this project's algebraic
(rather than Hamiltonian-derived) scope. Without these relations, `Mx = My = Mz = 0` would
be a valid (but physically nonsensical) instance, which is why an earlier version of this
structure — omitting them — left `Hydrogen/Symmetry.lean`'s `I,K` commutator theorems
unprovable (documented in the blueprint's Caveats chapter; see git history for the
counterexample). -/
structure BoundStateRepresentation extends AngularMomentumRepresentation V where
  Mx : Module.End ℂ V
  My : Module.End ℂ V
  Mz : Module.End ℂ V
  m : ℝ
  k : ℝ
  E : ℝ
  m_pos : 0 < m
  E_neg : E < 0
  /-- `M` transforms as a vector under `J`: `[Jᵢ, Mⱼ] = i εᵢⱼₖ Mₖ`, spelled out
  component-wise since `Jx,Jy,Jz,Mx,My,Mz` are separate fields rather than
  `Fin 3 → Module.End ℂ V`-valued (see the blueprint's Caveats chapter). -/
  JM_xy : ⁅Jx, My⁆ = Complex.I • Mz
  JM_yx : ⁅Jy, Mx⁆ = -Complex.I • Mz
  JM_yz : ⁅Jy, Mz⁆ = Complex.I • Mx
  JM_zy : ⁅Jz, My⁆ = -Complex.I • Mx
  JM_zx : ⁅Jz, Mx⁆ = Complex.I • My
  JM_xz : ⁅Jx, Mz⁆ = -Complex.I • My
  JM_xx : ⁅Jx, Mx⁆ = 0
  JM_yy : ⁅Jy, My⁆ = 0
  JM_zz : ⁅Jz, Mz⁆ = 0
  /-- `M`'s self-commutator closes back onto `J`, rescaled by `-2E/m`:
  `[Mᵢ, Mⱼ] = i εᵢⱼₖ (-2E/m) Jₖ`. -/
  MM_xy : ⁅Mx, My⁆ = Complex.I • ((-2 * E / m : ℝ) : ℂ) • Jz
  MM_yz : ⁅My, Mz⁆ = Complex.I • ((-2 * E / m : ℝ) : ℂ) • Jx
  MM_zx : ⁅Mz, Mx⁆ = Complex.I • ((-2 * E / m : ℝ) : ℂ) • Jy

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

/-- `rescalingConst² = -2E/m`, the identity that makes `MM_xy` etc. rescale into the
`⁅Ax,Ay⁆ = i•Jz` form used by `Hydrogen/Symmetry.lean`. -/
theorem rescalingConst_sq (H : BoundStateRepresentation V) :
    H.rescalingConst ^ 2 = -2 * H.E / H.m :=
  Real.sq_sqrt H.rescaling_pos.le

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
