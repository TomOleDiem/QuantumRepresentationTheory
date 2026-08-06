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

/-! ### The rescaled Runge–Lenz vector inherits `M`'s `so(4)` relations

`A := (rescalingConst)⁻¹ • M`, so each of `BoundStateRepresentation`'s `JM_*`/`MM_*`
fields (stated for `M`) transfers to `A` by pulling the scalar `(rescalingConst)⁻¹`
through the bracket, using `endLieSmul`/`endSmulLie` and `rescalingConst_sq` (for the
`MM_*`-derived facts, where the rescaling has to cancel the `-2E/m` factor).

`endSmulLie`/`endLieSmul` are bespoke replacements for the generic `smul_lie`/`lie_smul`
(which need a `LieRingModule L M` instance for possibly-distinct `L,M`; here `L = M =
Module.End ℂ V` and the only registered such instance is the self-action one - which,
empirically, doesn't always unify syntactically with the associative-ring bracket used
for `Module.End`'s own `LieRing` structure). Proved directly via
`LieRing.of_associative_ring_bracket`, mirroring `Sl2/Basic.lean`'s `endSmulLie` etc. -/

private theorem endSmulLie (c : ℂ) (x y : Module.End ℂ V) : ⁅c • x, y⁆ = c • ⁅x, y⁆ := by
  simp only [LieRing.of_associative_ring_bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

private theorem endLieSmul (c : ℂ) (x y : Module.End ℂ V) : ⁅x, c • y⁆ = c • ⁅x, y⁆ := by
  simp only [LieRing.of_associative_ring_bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

private theorem A_scale (H : BoundStateRepresentation V) {X Y Z : Module.End ℂ V} (c1 : ℂ)
    (h : ⁅X, Y⁆ = c1 • Z) :
    ⁅X, (H.rescalingConst⁻¹ : ℂ) • Y⁆ = c1 • ((H.rescalingConst⁻¹ : ℂ) • Z) := by
  rw [endLieSmul, h, smul_comm]

private theorem JA_xy (H : BoundStateRepresentation V) : ⁅H.Jx, H.Ay⁆ = Complex.I • H.Az :=
  H.A_scale Complex.I H.JM_xy

private theorem JA_yx (H : BoundStateRepresentation V) : ⁅H.Jy, H.Ax⁆ = -Complex.I • H.Az :=
  H.A_scale (-Complex.I) H.JM_yx

private theorem JA_yz (H : BoundStateRepresentation V) : ⁅H.Jy, H.Az⁆ = Complex.I • H.Ax :=
  H.A_scale Complex.I H.JM_yz

private theorem JA_zy (H : BoundStateRepresentation V) : ⁅H.Jz, H.Ay⁆ = -Complex.I • H.Ax :=
  H.A_scale (-Complex.I) H.JM_zy

private theorem JA_zx (H : BoundStateRepresentation V) : ⁅H.Jz, H.Ax⁆ = Complex.I • H.Ay :=
  H.A_scale Complex.I H.JM_zx

private theorem JA_xz (H : BoundStateRepresentation V) : ⁅H.Jx, H.Az⁆ = -Complex.I • H.Ay :=
  H.A_scale (-Complex.I) H.JM_xz

private theorem JA_xx (H : BoundStateRepresentation V) : ⁅H.Jx, H.Ax⁆ = 0 := by
  show ⁅H.Jx, (H.rescalingConst⁻¹ : ℂ) • H.Mx⁆ = 0
  rw [endLieSmul, H.JM_xx, smul_zero]

private theorem JA_yy (H : BoundStateRepresentation V) : ⁅H.Jy, H.Ay⁆ = 0 := by
  show ⁅H.Jy, (H.rescalingConst⁻¹ : ℂ) • H.My⁆ = 0
  rw [endLieSmul, H.JM_yy, smul_zero]

private theorem JA_zz (H : BoundStateRepresentation V) : ⁅H.Jz, H.Az⁆ = 0 := by
  show ⁅H.Jz, (H.rescalingConst⁻¹ : ℂ) • H.Mz⁆ = 0
  rw [endLieSmul, H.JM_zz, smul_zero]

private theorem rescalingConst_ne_zero (H : BoundStateRepresentation V) :
    (H.rescalingConst : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr H.rescalingConst_pos.ne'

private theorem rescalingConst_sq_C (H : BoundStateRepresentation V) :
    (H.rescalingConst : ℂ) ^ 2 = ((-2 * H.E / H.m : ℝ) : ℂ) := by
  rw [← H.rescalingConst_sq]; push_cast; ring

private theorem AA_xy (H : BoundStateRepresentation V) : ⁅H.Ax, H.Ay⁆ = Complex.I • H.Jz := by
  show ⁅(H.rescalingConst⁻¹ : ℂ) • H.Mx, (H.rescalingConst⁻¹ : ℂ) • H.My⁆ = Complex.I • H.Jz
  rw [endSmulLie, endLieSmul, H.MM_xy, smul_smul, smul_smul, smul_smul]
  rw [show (H.rescalingConst⁻¹ : ℂ) * (H.rescalingConst⁻¹ : ℂ) * Complex.I
        * ((-2 * H.E / H.m : ℝ) : ℂ) = Complex.I
      from by rw [← H.rescalingConst_sq_C]; field_simp [H.rescalingConst_ne_zero]]

private theorem AA_yz (H : BoundStateRepresentation V) : ⁅H.Ay, H.Az⁆ = Complex.I • H.Jx := by
  show ⁅(H.rescalingConst⁻¹ : ℂ) • H.My, (H.rescalingConst⁻¹ : ℂ) • H.Mz⁆ = Complex.I • H.Jx
  rw [endSmulLie, endLieSmul, H.MM_yz, smul_smul, smul_smul, smul_smul]
  rw [show (H.rescalingConst⁻¹ : ℂ) * (H.rescalingConst⁻¹ : ℂ) * Complex.I
        * ((-2 * H.E / H.m : ℝ) : ℂ) = Complex.I
      from by rw [← H.rescalingConst_sq_C]; field_simp [H.rescalingConst_ne_zero]]

private theorem AA_zx (H : BoundStateRepresentation V) : ⁅H.Az, H.Ax⁆ = Complex.I • H.Jy := by
  show ⁅(H.rescalingConst⁻¹ : ℂ) • H.Mz, (H.rescalingConst⁻¹ : ℂ) • H.Mx⁆ = Complex.I • H.Jy
  rw [endSmulLie, endLieSmul, H.MM_zx, smul_smul, smul_smul, smul_smul]
  rw [show (H.rescalingConst⁻¹ : ℂ) * (H.rescalingConst⁻¹ : ℂ) * Complex.I
        * ((-2 * H.E / H.m : ℝ) : ℂ) = Complex.I
      from by rw [← H.rescalingConst_sq_C]; field_simp [H.rescalingConst_ne_zero]]

/-! ### Reversed-order brackets

`add_lie`/`sub_lie`/`lie_add`/`lie_sub` expand a bracket of sums/differences into *all
four* cross terms in a fixed pairing order, which doesn't always match the order the
`JA_*`/`AA_*`/`comm_*` lemmas above are stated in (e.g. `⁅Ax,Jy⁆` shows up, not
`⁅Jy,Ax⁆`). `lie_anti` flips a bracket's argument order (`⁅Y,X⁆ = -⁅X,Y⁆`), used here to
generate the reversed-order companion of each fact needed below, so the main proofs can
finish with a single order-agnostic `simp only`. -/

private theorem lie_anti (X Y : Module.End ℂ V) : ⁅Y, X⁆ = -⁅X, Y⁆ :=
  neg_eq_iff_eq_neg.mp (lie_skew X Y)

private theorem comm_yx (H : BoundStateRepresentation V) : ⁅H.Jy, H.Jx⁆ = -Complex.I • H.Jz := by
  simp [lie_anti, H.comm_xy]
private theorem comm_zy (H : BoundStateRepresentation V) : ⁅H.Jz, H.Jy⁆ = -Complex.I • H.Jx := by
  simp [lie_anti, H.comm_yz]
private theorem comm_xz (H : BoundStateRepresentation V) : ⁅H.Jx, H.Jz⁆ = -Complex.I • H.Jy := by
  simp [lie_anti, H.comm_zx]

private theorem AJ_xy (H : BoundStateRepresentation V) : ⁅H.Ax, H.Jy⁆ = Complex.I • H.Az := by
  simp [lie_anti, H.JA_yx]
private theorem AJ_yx (H : BoundStateRepresentation V) : ⁅H.Ay, H.Jx⁆ = -Complex.I • H.Az := by
  simp [lie_anti, H.JA_xy]
private theorem AJ_yz (H : BoundStateRepresentation V) : ⁅H.Ay, H.Jz⁆ = Complex.I • H.Ax := by
  simp [lie_anti, H.JA_zy]
private theorem AJ_zy (H : BoundStateRepresentation V) : ⁅H.Az, H.Jy⁆ = -Complex.I • H.Ax := by
  simp [lie_anti, H.JA_yz]
private theorem AJ_zx (H : BoundStateRepresentation V) : ⁅H.Az, H.Jx⁆ = Complex.I • H.Ay := by
  simp [lie_anti, H.JA_xz]
private theorem AJ_xz (H : BoundStateRepresentation V) : ⁅H.Ax, H.Jz⁆ = -Complex.I • H.Ay := by
  simp [lie_anti, H.JA_zx]
private theorem AJ_xx (H : BoundStateRepresentation V) : ⁅H.Ax, H.Jx⁆ = 0 := by
  simp [lie_anti, H.JA_xx]
private theorem AJ_yy (H : BoundStateRepresentation V) : ⁅H.Ay, H.Jy⁆ = 0 := by
  simp [lie_anti, H.JA_yy]
private theorem AJ_zz (H : BoundStateRepresentation V) : ⁅H.Az, H.Jz⁆ = 0 := by
  simp [lie_anti, H.JA_zz]

private theorem AA_yx (H : BoundStateRepresentation V) : ⁅H.Ay, H.Ax⁆ = -Complex.I • H.Jz := by
  simp [lie_anti, H.AA_xy]
private theorem AA_zy (H : BoundStateRepresentation V) : ⁅H.Az, H.Ay⁆ = -Complex.I • H.Jx := by
  simp [lie_anti, H.AA_yz]
private theorem AA_xz (H : BoundStateRepresentation V) : ⁅H.Ax, H.Az⁆ = -Complex.I • H.Jy := by
  simp [lie_anti, H.AA_zx]

/-- **`I` and `K` each satisfy `so(3)` relations and commute with each other**
(`thm:hyd-two-factors-commute`), the standard fact about the hydrogen atom's hidden
`SO(4)` symmetry: since `A` inherits `M`'s `so(4)` relations (`JA_*`/`AA_*` above),
expanding `⁅Ix,Iy⁆ = 4⁻¹⁅Jx+Ax,Jy+Ay⁆` and substituting gives `i•Iz` directly. -/
theorem I_comm_xy (H : BoundStateRepresentation V) : ⁅H.Ix, H.Iy⁆ = Complex.I • H.Iz := by
  show ⁅(2 : ℂ)⁻¹ • (H.Jx + H.Ax), (2 : ℂ)⁻¹ • (H.Jy + H.Ay)⁆
      = Complex.I • ((2 : ℂ)⁻¹ • (H.Jz + H.Az))
  simp only [endSmulLie, endLieSmul, add_lie, lie_add, H.comm_xy, H.JA_xy, H.AJ_xy, H.AA_xy]
  match_scalars <;> ring

theorem I_comm_yz (H : BoundStateRepresentation V) : ⁅H.Iy, H.Iz⁆ = Complex.I • H.Ix := by
  show ⁅(2 : ℂ)⁻¹ • (H.Jy + H.Ay), (2 : ℂ)⁻¹ • (H.Jz + H.Az)⁆
      = Complex.I • ((2 : ℂ)⁻¹ • (H.Jx + H.Ax))
  simp only [endSmulLie, endLieSmul, add_lie, lie_add, H.comm_yz, H.JA_yz, H.AJ_yz, H.AA_yz]
  match_scalars <;> ring

theorem I_comm_zx (H : BoundStateRepresentation V) : ⁅H.Iz, H.Ix⁆ = Complex.I • H.Iy := by
  show ⁅(2 : ℂ)⁻¹ • (H.Jz + H.Az), (2 : ℂ)⁻¹ • (H.Jx + H.Ax)⁆
      = Complex.I • ((2 : ℂ)⁻¹ • (H.Jy + H.Ay))
  simp only [endSmulLie, endLieSmul, add_lie, lie_add, H.comm_zx, H.JA_zx, H.AJ_zx, H.AA_zx]
  match_scalars <;> ring

theorem K_comm_xy (H : BoundStateRepresentation V) : ⁅H.Kx, H.Ky⁆ = Complex.I • H.Kz := by
  show ⁅(2 : ℂ)⁻¹ • (H.Jx - H.Ax), (2 : ℂ)⁻¹ • (H.Jy - H.Ay)⁆
      = Complex.I • ((2 : ℂ)⁻¹ • (H.Jz - H.Az))
  simp only [endSmulLie, endLieSmul, sub_lie, lie_sub, H.comm_xy, H.JA_xy, H.AJ_xy, H.AA_xy]
  match_scalars <;> ring

theorem K_comm_yz (H : BoundStateRepresentation V) : ⁅H.Ky, H.Kz⁆ = Complex.I • H.Kx := by
  show ⁅(2 : ℂ)⁻¹ • (H.Jy - H.Ay), (2 : ℂ)⁻¹ • (H.Jz - H.Az)⁆
      = Complex.I • ((2 : ℂ)⁻¹ • (H.Jx - H.Ax))
  simp only [endSmulLie, endLieSmul, sub_lie, lie_sub, H.comm_yz, H.JA_yz, H.AJ_yz, H.AA_yz]
  match_scalars <;> ring

theorem K_comm_zx (H : BoundStateRepresentation V) : ⁅H.Kz, H.Kx⁆ = Complex.I • H.Ky := by
  show ⁅(2 : ℂ)⁻¹ • (H.Jz - H.Az), (2 : ℂ)⁻¹ • (H.Jx - H.Ax)⁆
      = Complex.I • ((2 : ℂ)⁻¹ • (H.Jy - H.Ay))
  simp only [endSmulLie, endLieSmul, sub_lie, lie_sub, H.comm_zx, H.JA_zx, H.AJ_zx, H.AA_zx]
  match_scalars <;> ring

/-- `I` and `K` commute with each other componentwise (`thm:hyd-two-factors-commute`):
since `⁅Ji,Aj⁆` is symmetric-in-sign under swapping which of `J,A` gets the `+`, the
cross terms in `⁅Jx±Ax, Jy∓Ay⁆`-style expansions cancel, and the same-index case
additionally needs `JA_xx`/`JA_yy`/`JA_zz` (`⁅Ji,Ai⁆=0`) to kill `⁅Ax,Ax⁆`'s partner. -/
theorem I_comm_K (H : BoundStateRepresentation V) (a b : Module.End ℂ V)
    (ha : a = H.Ix ∨ a = H.Iy ∨ a = H.Iz) (hb : b = H.Kx ∨ b = H.Ky ∨ b = H.Kz) :
    ⁅a, b⁆ = 0 := by
  have hIKxx : ⁅H.Ix, H.Kx⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jx + H.Ax), (2 : ℂ)⁻¹ • (H.Jx - H.Ax)⁆ = 0
    simp [add_lie, lie_sub, lie_self, H.JA_xx, H.AJ_xx]
  have hIKyy : ⁅H.Iy, H.Ky⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jy + H.Ay), (2 : ℂ)⁻¹ • (H.Jy - H.Ay)⁆ = 0
    simp [add_lie, lie_sub, lie_self, H.JA_yy, H.AJ_yy]
  have hIKzz : ⁅H.Iz, H.Kz⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jz + H.Az), (2 : ℂ)⁻¹ • (H.Jz - H.Az)⁆ = 0
    simp [add_lie, lie_sub, lie_self, H.JA_zz, H.AJ_zz]
  have hIKxy : ⁅H.Ix, H.Ky⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jx + H.Ax), (2 : ℂ)⁻¹ • (H.Jy - H.Ay)⁆ = 0
    simp only [endSmulLie, endLieSmul, add_lie, lie_sub, H.comm_xy, H.JA_xy, H.AJ_xy, H.AA_xy]
    match_scalars <;> ring
  have hIKxz : ⁅H.Ix, H.Kz⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jx + H.Ax), (2 : ℂ)⁻¹ • (H.Jz - H.Az)⁆ = 0
    simp only [endSmulLie, endLieSmul, add_lie, lie_sub, H.comm_xz, H.JA_xz, H.AJ_xz, H.AA_xz]
    match_scalars <;> ring
  have hIKyx : ⁅H.Iy, H.Kx⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jy + H.Ay), (2 : ℂ)⁻¹ • (H.Jx - H.Ax)⁆ = 0
    simp only [endSmulLie, endLieSmul, add_lie, lie_sub, H.comm_yx, H.JA_yx, H.AJ_yx, H.AA_yx]
    match_scalars <;> ring
  have hIKyz : ⁅H.Iy, H.Kz⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jy + H.Ay), (2 : ℂ)⁻¹ • (H.Jz - H.Az)⁆ = 0
    simp only [endSmulLie, endLieSmul, add_lie, lie_sub, H.comm_yz, H.JA_yz, H.AJ_yz, H.AA_yz]
    match_scalars <;> ring
  have hIKzx : ⁅H.Iz, H.Kx⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jz + H.Az), (2 : ℂ)⁻¹ • (H.Jx - H.Ax)⁆ = 0
    simp only [endSmulLie, endLieSmul, add_lie, lie_sub, H.comm_zx, H.JA_zx, H.AJ_zx, H.AA_zx]
    match_scalars <;> ring
  have hIKzy : ⁅H.Iz, H.Ky⁆ = 0 := by
    show ⁅(2 : ℂ)⁻¹ • (H.Jz + H.Az), (2 : ℂ)⁻¹ • (H.Jy - H.Ay)⁆ = 0
    simp only [endSmulLie, endLieSmul, add_lie, lie_sub, H.comm_zy, H.JA_zy, H.AJ_zy, H.AA_zy]
    match_scalars <;> ring
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact hIKxx
  · exact hIKxy
  · exact hIKxz
  · exact hIKyx
  · exact hIKyy
  · exact hIKyz
  · exact hIKzx
  · exact hIKzy
  · exact hIKzz

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
