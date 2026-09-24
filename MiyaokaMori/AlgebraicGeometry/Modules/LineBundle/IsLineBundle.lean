import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnit
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyTrivialFinite

/-! # Line bundles (invertible sheaves) as an unbundled class

An `O_X`-module `M` on a scheme `X` is a line bundle (invertible sheaf, Stacks 01CR) if every point has an
open neighbourhood `U` with `M|_U ≅ O_U`. This module provides the unbundled class
`AlgebraicGeometry.Scheme.Modules.IsLineBundle` and its basic closure properties: invariance under
isomorphism (`of_iso`), the structure sheaf (`unit`), pullback along any morphism (`pullback`), restriction
along open immersions (`restrict`), together with the instances for local freeness (`isLocallyFree`) and
finite type (`isFiniteType`). The categorical ingredients (`f^*O_Y ≅ O_X`, restriction commutes with
pullback, the site-level criteria for locally free / finite type) live in `PullbackUnit` and
`LocallyTrivialFinite`.

Design: the unbundled `Prop`-class `[M.IsLineBundle]` is primary; the bundled `LineBundle X` is a thin
wrapper `{ M : X.Modules // M.IsLineBundle }` around it. The name lives in the namespace
`AlgebraicGeometry.Scheme.Modules`, so that for `M : X.Modules` the dot notation `M.IsLineBundle` resolves
to this class.

References: Stacks 01CR (invertible modules), 01CT.
-/

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- A line bundle (invertible sheaf): locally isomorphic to the structure sheaf. -/
class IsLineBundle (M : X.Modules) : Prop where
  locally_trivial : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U),
    Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- A trivialization of a line bundle on an open `U` (data). For existence see
`IsLineBundle.exists_trivialization`. -/
structure Trivialization (M : X.Modules) where
  /-- the open on which the trivialization lives -/
  carrier : X.Opens
  /-- `M|_U ≅ O_U` -/
  iso : M.restrict carrier.ι ≅ SheafOfModules.unit carrier.toScheme.ringCatSheaf

theorem IsLineBundle.exists_trivialization (M : X.Modules) [M.IsLineBundle] (x : X) :
    ∃ t : Trivialization M, x ∈ t.carrier := by
  obtain ⟨U, hx, ⟨e⟩⟩ := IsLineBundle.locally_trivial (M := M) x
  exact ⟨⟨U, e⟩, hx⟩

theorem isLineBundle_iff (M : X.Modules) :
    M.IsLineBundle ↔ ∀ x : X, ∃ t : Trivialization M, x ∈ t.carrier :=
  ⟨fun _ x => IsLineBundle.exists_trivialization M x,
    fun h => ⟨fun x => by obtain ⟨t, hx⟩ := h x; exact ⟨t.carrier, hx, ⟨t.iso⟩⟩⟩⟩

/-- Transport of a trivialization along an isomorphism. -/
def Trivialization.ofIso {M N : X.Modules} (e : M ≅ N) (t : Trivialization M) : Trivialization N where
  carrier := t.carrier
  iso := (restrictFunctor t.carrier.ι).mapIso e.symm ≪≫ t.iso

@[simp] theorem Trivialization.ofIso_carrier {M N : X.Modules} (e : M ≅ N) (t : Trivialization M) :
    (t.ofIso e).carrier = t.carrier := rfl

/-- Being a line bundle is invariant under isomorphism. -/
theorem IsLineBundle.of_iso {M N : X.Modules} (e : M ≅ N) [M.IsLineBundle] : N.IsLineBundle :=
  (isLineBundle_iff N).mpr fun x => by
    obtain ⟨t, hx⟩ := IsLineBundle.exists_trivialization M x
    exact ⟨t.ofIso e, hx⟩

theorem isLineBundle_iff_of_iso {M N : X.Modules} (e : M ≅ N) : M.IsLineBundle ↔ N.IsLineBundle :=
  ⟨fun _ => IsLineBundle.of_iso e, fun _ => IsLineBundle.of_iso e.symm⟩

/-- The structure sheaf is a line bundle. -/
instance IsLineBundle.unit (X : Scheme.{u}) :
    IsLineBundle (X := X) (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨fun _ => ⟨⊤, trivial, ⟨restrictUnitIso _⟩⟩⟩

/-- Pullback of a trivialization. -/
def Trivialization.pullback (f : X ⟶ Y) {M : Y.Modules} (t : Trivialization M) :
    Trivialization ((Scheme.Modules.pullback f).obj M) where
  carrier := f ⁻¹ᵁ t.carrier
  iso := pullbackTrivializationIso f t.iso

@[simp] theorem Trivialization.pullback_carrier (f : X ⟶ Y) {M : Y.Modules} (t : Trivialization M) :
    (t.pullback f).carrier = f ⁻¹ᵁ t.carrier := rfl

/-- The pullback of a line bundle is a line bundle (remark after Stacks 01CR). -/
instance IsLineBundle.pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsLineBundle] :
    ((Scheme.Modules.pullback f).obj M).IsLineBundle :=
  (isLineBundle_iff _).mpr fun x => by
    obtain ⟨t, hx⟩ := IsLineBundle.exists_trivialization M (f.base x)
    exact ⟨t.pullback f, hx⟩

/-- A line bundle is locally free (Mathlib's site-level notion). -/
instance (priority := 100) IsLineBundle.isLocallyFree (M : X.Modules) [M.IsLineBundle] :
    M.IsLocallyFree :=
  isLocallyFree_of_locally_unit M IsLineBundle.locally_trivial

/-- A line bundle is of finite type. -/
instance (priority := 100) IsLineBundle.isFiniteType (M : X.Modules) [M.IsLineBundle] :
    M.IsFiniteType :=
  isFiniteType_of_locally_unit M IsLineBundle.locally_trivial

/-- The restriction of a line bundle along an open immersion is a line bundle. -/
instance IsLineBundle.restrict (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) [M.IsLineBundle] :
    (M.restrict f).IsLineBundle :=
  IsLineBundle.of_iso ((restrictFunctorIsoPullback f).app M).symm

end AlgebraicGeometry.Scheme.Modules

end
