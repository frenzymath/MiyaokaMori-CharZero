import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension

/-! # Transport of properties along isomorphisms over the base

Transport of properties of varieties (separated, finite type, smooth, projective, dimension) along
an isomorphism of schemes that is **compatible with the structure morphisms to `Spec k`**.

Several statements have the form "there is a smooth projective surface `S′` and an isomorphism
`e : S′ ≅ X` commuting with the `k`-structure morphisms". Only with the compatibility with the
`k`-structure can such a statement be turned into properties of the structure morphism
`σ : X ⟶ Spec k` of `X` itself; an isomorphism without it gives none of them
(`IsSeparated`, `IsOfFiniteType`, `IsSmoothOver`, `IsProjectiveOver` are all properties of `σ`, not
of the underlying scheme).

The proofs are formal transport together with the invariance of these morphism properties under
isomorphisms in Mathlib (`MorphismProperty.RespectsIso` for `IsSeparated`, `LocallyOfFiniteType`,
`Smooth`; `quasiCompact_of_isIso` for `QuasiCompact`); the invariance of the topological Krull
dimension under homeomorphisms is `IsHomeomorph.topologicalKrullDim_eq`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.IsoOverBase

/-- If `e.hom ≫ φ = σ` then `φ = e.inv ≫ σ`. The common first step of all transport lemmas below. -/
theorem hom_eq_inv_comp {C : Type*} [Category C] {X Y Z : C} (e : X ≅ Y) {φ : Y ⟶ Z} {σ : X ⟶ Z}
    (he : e.hom ≫ φ = σ) : φ = e.inv ≫ σ :=
  (Iso.eq_inv_comp e).mpr he

/-- Separatedness transports along a compatible isomorphism. -/
theorem isSeparated_of_isoOver {X Y Z : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) {φ : Y ⟶ Z}
    {σ : X ⟶ Z} (he : e.hom ≫ φ = σ) (hσ : AlgebraicGeometry.IsSeparated σ) :
    AlgebraicGeometry.IsSeparated φ := by
  rw [hom_eq_inv_comp e he]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@AlgebraicGeometry.IsSeparated) e.inv σ).mpr hσ

/-- Locally of finite type transports along a compatible isomorphism (an isomorphism is an open
immersion; `locallyOfFiniteType_of_isOpenImmersion` and composition). -/
theorem locallyOfFiniteType_of_isoOver {X Y Z : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y)
    {φ : Y ⟶ Z} {σ : X ⟶ Z} (he : e.hom ≫ φ = σ)
    (hσ : AlgebraicGeometry.LocallyOfFiniteType σ) :
    AlgebraicGeometry.LocallyOfFiniteType φ := by
  have := hσ
  rw [hom_eq_inv_comp e he]
  infer_instance

/-- Finite type (= locally of finite type + quasi-compact) transports along a compatible
isomorphism. -/
theorem isOfFiniteType_of_isoOver {X Y Z : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) {φ : Y ⟶ Z}
    {σ : X ⟶ Z} (he : e.hom ≫ φ = σ) (hσ : AlgebraicGeometry.IsOfFiniteType σ) :
    AlgebraicGeometry.IsOfFiniteType φ := by
  have := hσ
  have : AlgebraicGeometry.LocallyOfFiniteType φ :=
    locallyOfFiniteType_of_isoOver e he inferInstance
  have : AlgebraicGeometry.QuasiCompact φ := by
    rw [hom_eq_inv_comp e he]; infer_instance
  exact {}

/-- Smoothness transports along a compatible isomorphism (an isomorphism is an open immersion;
`Smooth` holds for open immersions and is stable under composition). -/
theorem smooth_of_isoOver {X Y Z : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) {φ : Y ⟶ Z}
    {σ : X ⟶ Z} (he : e.hom ≫ φ = σ) (hσ : AlgebraicGeometry.Smooth σ) :
    AlgebraicGeometry.Smooth φ := by
  have := hσ
  rw [hom_eq_inv_comp e he]
  infer_instance

variable {k : Type u} [Field k]

/-- Smoothness over `k` transports along a compatible isomorphism. -/
theorem isSmoothOver_of_isoOver {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (e : X ≅ Y)
    (he : e.hom ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (h : IsSmoothOver k X) : IsSmoothOver k Y :=
  smooth_of_isoOver e he h

/-- Projectivity over `k` transports along a compatible isomorphism: replace the closed immersion
`i : X ⟶ P^N` by `e.inv ≫ i`. -/
theorem isProjectiveOver_of_isoOver {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (e : X ≅ Y)
    (he : e.hom ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (h : IsProjectiveOver k X) : IsProjectiveOver k Y := by
  obtain ⟨N, i, hi, ho⟩ := h
  refine ⟨N, e.inv ≫ i, inferInstance, ⟨?_⟩⟩
  rw [Category.assoc, ho.1]
  exact (hom_eq_inv_comp e he).symm

/-- The topological Krull dimension is invariant under isomorphisms (only the homeomorphism of the
underlying spaces is used). -/
theorem topologicalKrullDim_eq_of_iso {X Y : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (AlgebraicGeometry.Scheme.homeoOfIso e).isHomeomorph

/-- The dimension of a variety is invariant under isomorphisms of the underlying schemes. -/
theorem Variety.dim_eq_of_iso (V W : Variety k) (e : V.carrier ≅ W.carrier) : V.dim = W.dim := by
  simp only [Variety.dim, AlgebraicGeometry.Scheme.dimension]
  rw [topologicalKrullDim_eq_of_iso e]

end MiyaokaMori.IsoOverBase

end
