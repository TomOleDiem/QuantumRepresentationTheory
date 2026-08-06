import Mathlib
import QuantumRepresentationTheory.Hydrogen.Basic

/-!
# Hydrogen/Symmetry

Part of the blueprint for algebraic quantum representation theory.
See `blueprint/src/content.tex`, §"The hidden $\sofour$ symmetry" (`sec:hyd-symmetry`).
-/

noncomputable section

namespace QuantumRepresentationTheory

variable {V : Type*} [AddCommGroup V] [Module ℂ V]


namespace BoundStateRepresentation

/-- **Two angular momentum triples** (`def:hyd-two-triples`): `I := (J+A)/2`,
`K := (J-A)/2`. -/
def Ix (H : BoundStateRepresentation V) : Module.End ℂ V := (2 : ℂ)⁻¹ • (H.Jx + H.Ax)
@[inherit_doc Ix] def Iy (H : BoundStateRepresentation V) : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (H.Jy + H.Ay)
@[inherit_doc Ix] def Iz (H : BoundStateRepresentation V) : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (H.Jz + H.Az)

@[inherit_doc Ix] def Kx (H : BoundStateRepresentation V) : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (H.Jx - H.Ax)
@[inherit_doc Ix] def Ky (H : BoundStateRepresentation V) : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (H.Jy - H.Ay)
@[inherit_doc Ix] def Kz (H : BoundStateRepresentation V) : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (H.Jz - H.Az)

/-- **`I` and `K` each satisfy `so(3)` relations and commute with each other**
(`thm:hyd-two-factors-commute`).

**Currently unprovable as stated**, and deliberately left `sorry` rather than patched: this
is already documented in `blueprint/src/content.tex`'s Caveats section
("Angular momentum as a 3-vector is a low-dimension coincidence, not the right general
object"). `BoundStateRepresentation` (`Hydrogen/Basic.lean`) presents the Runge–Lenz vector
as three *unconstrained* operators `Mx, My, Mz` with no commutation hypotheses at all
relating them to `Jx, Jy, Jz` or to each other — nothing in the structure pins down the
`so(4)` relations a genuine Runge–Lenz vector must satisfy. Concretely, `Mx = My = Mz = 0`
(hence `Ax = Ay = Az = 0`) is a valid `BoundStateRepresentation` for *any* choice of
`AngularMomentumRepresentation` with `Jz ≠ 0`, giving `Ix = Jx/2` etc., and then
`⁅Ix,Iy⁆ = (1/4)⁅Jx,Jy⁆ = (i/4)•Jz ≠ (i/2)•Jz = i•Iz` whenever `Jz ≠ 0` — a genuine
counterexample to `I_comm_xy` as stated. Fixing this needs an architectural change to
`BoundStateRepresentation` (the `so(4)`-antisymmetric-tensor presentation the blueprint
proposes), not a leaf-level proof. -/
theorem I_comm_xy (H : BoundStateRepresentation V) : ⁅H.Ix, H.Iy⁆ = Complex.I • H.Iz := by
  sorry
theorem I_comm_yz (H : BoundStateRepresentation V) : ⁅H.Iy, H.Iz⁆ = Complex.I • H.Ix := by
  sorry
theorem I_comm_zx (H : BoundStateRepresentation V) : ⁅H.Iz, H.Ix⁆ = Complex.I • H.Iy := by
  sorry
theorem K_comm_xy (H : BoundStateRepresentation V) : ⁅H.Kx, H.Ky⁆ = Complex.I • H.Kz := by
  sorry
theorem K_comm_yz (H : BoundStateRepresentation V) : ⁅H.Ky, H.Kz⁆ = Complex.I • H.Kx := by
  sorry
theorem K_comm_zx (H : BoundStateRepresentation V) : ⁅H.Kz, H.Kx⁆ = Complex.I • H.Ky := by
  sorry

/-- `I` and `K` commute with each other componentwise.

Same underlying gap as `I_comm_xy` etc. (see its doc comment): unprovable without
commutation hypotheses relating `Mx,My,Mz` to `Jx,Jy,Jz`, which `BoundStateRepresentation`
does not currently provide. Left `sorry`, not patched. -/
theorem I_comm_K (H : BoundStateRepresentation V) (a b : Module.End ℂ V)
    (ha : a = H.Ix ∨ a = H.Iy ∨ a = H.Iz) (hb : b = H.Kx ∨ b = H.Ky ∨ b = H.Kz) :
    ⁅a, b⁆ = 0 := by
  sorry

/-- **`$\sofour \cong \liealg{so}_3\oplus\liealg{so}_3$` decomposition** (`thm:hyd-so4-decomposition`):
`I` generates an `sl₂`-triple. -/
def IRep (H : BoundStateRepresentation V) : AngularMomentumRepresentation V where
  Jx := H.Ix
  Jy := H.Iy
  Jz := H.Iz
  comm_xy := H.I_comm_xy
  comm_yz := H.I_comm_yz
  comm_zx := H.I_comm_zx

@[inherit_doc IRep] def KRep (H : BoundStateRepresentation V) : AngularMomentumRepresentation V where
  Jx := H.Kx
  Jy := H.Ky
  Jz := H.Kz
  comm_xy := H.K_comm_xy
  comm_yz := H.K_comm_yz
  comm_zx := H.K_comm_zx

/-- **Equality of the two Casimir eigenvalues** (`thm:hyd-equal-casimirs`). On any
irreducible summand of `V` under the joint `(I,K)` action, the Casimir eigenvalues of
the `I`-triple and `K`-triple coincide, forcing equal spin labels `n₁ = n₂` (where
`I²` acts as `(n₁/2)(n₁/2+1)` and `K²` as `(n₂/2)(n₂/2+1)`, per
`AngularMomentumRepresentation.Jsq_eq_smul`). The hypothesis `hIsqKsq` packages the
Hamiltonian-level identity `I² = K²` that, in a full (non-decoupled) treatment, would
be derived from the explicit form of the hydrogen Hamiltonian (cf. Physlib's
`lrlOperatorSqr_eq`); here it is taken as given, consistent with this project's
decoupled algebraic scope.

The hypothesis `[Nontrivial V]` was missing from an earlier version of this statement and is
necessary: on the zero module, `(1 : Module.End ℂ V) = 0`, so `hI`/`hK` hold vacuously for
*every* `n₁, n₂` and the conclusion `n₁ = n₂` is unreachable. The blueprint's own phrasing
("on any irreducible summand") already presupposes this — an irreducible summand is
nonzero. -/
theorem equal_casimirs (H : BoundStateRepresentation V) [Nontrivial V]
    (hIsqKsq : H.Ix * H.Ix + H.Iy * H.Iy + H.Iz * H.Iz =
      H.Kx * H.Kx + H.Ky * H.Ky + H.Kz * H.Kz)
    {n₁ n₂ : ℕ}
    (hI : H.Ix * H.Ix + H.Iy * H.Iy + H.Iz * H.Iz =
      ((n₁ : ℂ) / 2 * ((n₁ : ℂ) / 2 + 1)) • (1 : Module.End ℂ V))
    (hK : H.Kx * H.Kx + H.Ky * H.Ky + H.Kz * H.Kz =
      ((n₂ : ℂ) / 2 * ((n₂ : ℂ) / 2 + 1)) • (1 : Module.End ℂ V)) :
    n₁ = n₂ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have heq : ((n₁ : ℂ) / 2 * ((n₁ : ℂ) / 2 + 1)) • v
      = ((n₂ : ℂ) / 2 * ((n₂ : ℂ) / 2 + 1)) • v := by
    have h := hIsqKsq
    rw [hI, hK] at h
    have h2 := congrArg (fun T : Module.End ℂ V => T v) h
    simpa using h2
  have hscalar : (n₁ : ℂ) / 2 * ((n₁ : ℂ) / 2 + 1) = (n₂ : ℂ) / 2 * ((n₂ : ℂ) / 2 + 1) := by
    by_contra hne
    apply hv
    have hsub : ((n₁ : ℂ) / 2 * ((n₁ : ℂ) / 2 + 1)
        - (n₂ : ℂ) / 2 * ((n₂ : ℂ) / 2 + 1)) • v = 0 := by
      rw [sub_smul, heq, sub_self]
    exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)
  have hfactor : ((n₁ : ℂ) - (n₂ : ℂ)) * ((n₁ : ℂ) + (n₂ : ℂ) + 2) = 0 := by
    linear_combination 4 * hscalar
  have hcast : (n₁ : ℂ) + (n₂ : ℂ) + 2 = ((n₁ + n₂ + 2 : ℕ) : ℂ) := by push_cast; ring
  have hpos : (n₁ : ℂ) + (n₂ : ℂ) + 2 ≠ 0 := by
    rw [hcast]; exact_mod_cast (by omega : n₁ + n₂ + 2 ≠ 0)
  rcases mul_eq_zero.mp hfactor with h | h
  · exact_mod_cast sub_eq_zero.mp h
  · exact absurd h hpos

end BoundStateRepresentation

end QuantumRepresentationTheory
