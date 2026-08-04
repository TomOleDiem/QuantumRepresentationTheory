import Mathlib

noncomputable section

namespace QuantumRepresentationTheory

universe u v w w'

section Representation

variable
    (K : Type u)
    (L : Type v)
    (V : Type w)
    [Field K]
    [LieRing L]
    [LieAlgebra K L]
    [AddCommGroup V]
    [Module K V]

/-- The Lie ring structure on `Module.End K V` given by the commutator bracket.
Declared once, globally, here (rather than as a `local instance` re-declared in
every file that needs bracket notation for endomorphisms) so that importing this
file is enough to make `⁅f, g⁆` notation available for `f g : Module.End K V`
everywhere in the project, without name collisions between separately-declared
local copies. -/
instance instEndLieRing : LieRing (Module.End K V) :=
  LieRing.ofAssociativeRing

/-- A representation of a Lie algebra by linear endomorphisms. -/
abbrev LieRepresentation :=
  L →ₗ⁅K⁆ Module.End K V

/-- A linear subspace preserved by every operator in the representation. -/
def IsInvariantSubspace
    (ρ : LieRepresentation K L V)
    (W : Submodule K V) : Prop :=
  ∀ x : L, ∀ v : V, v ∈ W → ρ x v ∈ W

/-- An irreducible representation has no nontrivial invariant subspaces. -/
def IsIrreducible
    (ρ : LieRepresentation K L V) : Prop :=
  ∀ W : Submodule K V,
    IsInvariantSubspace K L V ρ W →
      W = ⊥ ∨ W = ⊤

variable
    (W : Type w')
    [AddCommGroup W]
    [Module K W]

local instance instEndLieRingW : LieRing (Module.End K W) :=
  LieRing.ofAssociativeRing

/-- A linear map intertwining two Lie algebra representations. -/
def IsIntertwiner
    (ρV : LieRepresentation K L V)
    (ρW : LieRepresentation K L W)
    (f : V →ₗ[K] W) : Prop :=
  ∀ x : L,
    f.comp (ρV x) = (ρW x).comp f

/-- The kernel of an intertwiner is invariant. -/
theorem IsIntertwiner.ker_isInvariant
    (ρV : LieRepresentation K L V)
    (ρW : LieRepresentation K L W)
    (f : V →ₗ[K] W)
    (hf : IsIntertwiner K L V W ρV ρW f) :
    IsInvariantSubspace K L V ρV f.ker := by
  intro x v hv
  change f (ρV x v) = 0
  have h := LinearMap.congr_fun (hf x) v
  simp only [LinearMap.comp_apply] at h
  rw [h]
  change ρW x (f v) = 0
  rw [show f v = 0 from hv]
  exact map_zero (ρW x)

/-- The range of an intertwiner is invariant. -/
theorem IsIntertwiner.range_isInvariant
    (ρV : LieRepresentation K L V)
    (ρW : LieRepresentation K L W)
    (f : V →ₗ[K] W)
    (hf : IsIntertwiner K L V W ρV ρW f) :
    IsInvariantSubspace K L W ρW f.range := by
  intro x w hw
  rcases hw with ⟨v, rfl⟩
  refine ⟨ρV x v, ?_⟩
  have h := LinearMap.congr_fun (hf x) v
  simpa only [LinearMap.comp_apply] using h

end Representation

end QuantumRepresentationTheory
