import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyCompat

/-! # `fromOfGlobalSections φ` is an isomorphism onto `D₊(t)` when the degree-zero fraction map is bijective

Used to show that the total space of a line bundle is affine over the base (`totalSpace.toTotLine_isIso`).
Mathlib's `Proj.fromOfGlobalSections 𝒜 φ hφ : X ⟶ Proj 𝒜` (Stacks 01O4) restricted to `D₊(t)` is
`toBasicOpenOfGlobalSections`, i.e. `X.toSpecΓ` followed by `Spec.map` of the degree-zero fraction map
`ρ : (A_t)_0 → Γ(X, ⊤)[1/φ t]`, `a/t^k ↦ φ(a)/φ(t)^k`, followed by `basicOpenIsoSpec⁻¹`
(`Proj.fromOfGlobalSections_resLE`; spelled out as `projBundle.toSpecAway ≫ Spec.map ρ ≫ basicOpenIsoSpec⁻¹` in
`ProjectiveBundleUniversalPropertyCompat.lean`, whose `evalAway`/`toSpecAway` are reused here). Hence, when `X` is
affine and `φ t` is a unit (so `X.basicOpen (φ t) = ⊤`),
`fromOfGlobalSections φ` is an open immersion with image exactly `D₊(t)` as soon as `ρ` is bijective.
This is the geometric half of "Tot(L)|_W = D₊(T) ≅ Spec (A(W)_T)_0" (Stacks 01NS); the algebraic half
(bijectivity of `ρ` for the total space of a line bundle) is the leaf `toProjBundle_awayMap_bijective`
in `TotLineAffineOverBase.lean`.

-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ : Type u} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {X : AlgebraicGeometry.Scheme.{u}} (f : A →+* Γ(X, ⊤))

/-- **The degree-zero fraction map** `(A_t)_0 → Γ(X, ⊤)[1/f t]`, `a/t^k ↦ f(a)/f(t)^k`: the ring homomorphism
whose `Spec.map` is the middle factor of Mathlib's `toBasicOpenOfGlobalSections` (Stacks 01O4); it is
`projBundle.evalAway f t rfl` (`A_t → Γ(X, ⊤)_{f t}`) precomposed with `(A_t)_0 ⊆ A_t`. -/
def awayMapOfGlobalSections (t : A) :
    HomogeneousLocalization.Away 𝒜 t →+* Localization.Away (f t) :=
  (AlgebraicGeometry.Scheme.projBundle.evalAway f t rfl).comp
    (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t))

variable {t : A} {d : ℕ}

/-- `toBasicOpenOfGlobalSections` unfolded: `toSpecAway ≫ Spec.map ρ ≫ basicOpenIsoSpec⁻¹`
(`projBundle.toBasicOpenOfGlobalSections_eq'`). -/
theorem toBasicOpenOfGlobalSections_eq (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      AlgebraicGeometry.Scheme.projBundle.toSpecAway X (f t) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (awayMapOfGlobalSections 𝒜 f t)) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 t hd h0d).inv :=
  AlgebraicGeometry.Scheme.projBundle.toBasicOpenOfGlobalSections_eq' 𝒜 f rfl h0d hd

/-- On an affine scheme, `toSpecAway X x : D(x) ⟶ Spec Γ(X, ⊤)_x` is an isomorphism (composite of
`isoOfEq⁻¹`, the restriction of the isomorphism `X.toSpecΓ`, and `basicOpenIsoSpecAway`). -/
theorem isIso_toSpecAway [AlgebraicGeometry.IsAffine X] (x : Γ(X, ⊤)) :
    IsIso (AlgebraicGeometry.Scheme.projBundle.toSpecAway X x) := by
  unfold AlgebraicGeometry.Scheme.projBundle.toSpecAway
  have : IsIso X.toSpecΓ := AlgebraicGeometry.IsAffine.affine
  have : IsIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x) := by
    delta AlgebraicGeometry.morphismRestrict; infer_instance
  infer_instance

/-- If `X` is affine and the degree-zero fraction map is bijective, `toBasicOpenOfGlobalSections` is an
isomorphism `D(f t) ≅ D₊(t)` (a composite of isomorphisms). -/
theorem isIso_toBasicOpenOfGlobalSections [AlgebraicGeometry.IsAffine X] (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (hbij : Function.Bijective (awayMapOfGlobalSections 𝒜 f t)) :
    IsIso (AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd) := by
  rw [toBasicOpenOfGlobalSections_eq]
  have : IsIso (CommRingCat.ofHom (awayMapOfGlobalSections 𝒜 f t)) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have := isIso_toSpecAway (X := X) (f t)
  infer_instance

variable (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

/-- `D(f t) ↪ X → Proj 𝒜` factors as `toBasicOpenOfGlobalSections ≫ D₊(t).ι`
(`projBundle.basicOpen_ι_fromOfGlobalSections'`). -/
theorem basicOpen_ι_comp_fromOfGlobalSections (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    (X.basicOpen (f t)).ι ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf =
      AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫
        (AlgebraicGeometry.Proj.basicOpen 𝒜 t).ι :=
  AlgebraicGeometry.Scheme.projBundle.basicOpen_ι_fromOfGlobalSections' 𝒜 f hf rfl h0d hd

/-- If `f t` is a unit then `D(f t) = X` and its inclusion is an isomorphism. -/
theorem isIso_basicOpen_ι_of_isUnit (hu : IsUnit (f t)) : IsIso (X.basicOpen (f t)).ι :=
  AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (by rw [AlgebraicGeometry.Scheme.Opens.opensRange_ι]; exact X.basicOpen_of_isUnit hu)

/-- **`fromOfGlobalSections` is an open immersion** when `X` is affine, `f t` is a unit for a homogeneous `t` of
positive degree, and the degree-zero fraction map `(A_t)_0 → Γ(X, ⊤)[1/f t]` is bijective. -/
theorem isOpenImmersion_fromOfGlobalSections_of_bijective [AlgebraicGeometry.IsAffine X]
    (h0d : 0 < d) (hd : t ∈ 𝒜 d) (hu : IsUnit (f t))
    (hbij : Function.Bijective (awayMapOfGlobalSections 𝒜 f t)) :
    AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf) := by
  have := isIso_toBasicOpenOfGlobalSections 𝒜 f h0d hd hbij
  have := isIso_basicOpen_ι_of_isUnit f hu
  rw [← IsIso.inv_hom_id_assoc (X.basicOpen (f t)).ι (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf),
    basicOpen_ι_comp_fromOfGlobalSections 𝒜 f hf h0d hd]
  infer_instance

/-- **The image of `fromOfGlobalSections` is exactly `D₊(t)`** under the hypotheses of
`isOpenImmersion_fromOfGlobalSections_of_bijective`. -/
theorem range_fromOfGlobalSections_of_bijective [AlgebraicGeometry.IsAffine X]
    (h0d : 0 < d) (hd : t ∈ 𝒜 d) (hu : IsUnit (f t))
    (hbij : Function.Bijective (awayMapOfGlobalSections 𝒜 f t)) :
    Set.range (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf).base =
      (AlgebraicGeometry.Proj.basicOpen 𝒜 t : Set (AlgebraicGeometry.Proj 𝒜)) := by
  have hbo := isIso_toBasicOpenOfGlobalSections 𝒜 f h0d hd hbij
  have hι := isIso_basicOpen_ι_of_isUnit f hu
  have h1 : Set.range (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf).base =
      Set.range ((X.basicOpen (f t)).ι ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf).base := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (X.basicOpen (f t)).ι.surjective, Set.image_univ]
  rw [h1, basicOpen_ι_comp_fromOfGlobalSections 𝒜 f hf h0d hd, AlgebraicGeometry.Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd).surjective,
    Set.image_univ, AlgebraicGeometry.Scheme.Opens.range_ι]

/-- Point-level form: every point of `D₊(t)` is in the image of `fromOfGlobalSections`. -/
theorem mem_range_fromOfGlobalSections_of_bijective [AlgebraicGeometry.IsAffine X]
    (h0d : 0 < d) (hd : t ∈ 𝒜 d) (hu : IsUnit (f t))
    (hbij : Function.Bijective (awayMapOfGlobalSections 𝒜 f t))
    {q : AlgebraicGeometry.Proj 𝒜} (hq : q ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 t) :
    q ∈ Set.range (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf).base := by
  rw [range_fromOfGlobalSections_of_bijective 𝒜 f hf h0d hd hu hbij]
  exact hq

end AlgebraicGeometry.Proj

/-- **Shape of a local piece of `projBundle.lift`**: `e.hom ≫ g ≫ i.inv ≫ U.ι` is an open immersion when `g` is
(`e`, `i` isomorphisms, `U.ι` the inclusion of an open). Stated abstractly so that it can be applied by `exact`
in contexts where instance search on the large concrete terms (`fromOfGlobalSections … ≫ affineIso.inv ≫ ι`)
fails. -/
theorem AlgebraicGeometry.IsOpenImmersion.isoHom_comp_comp_isoInv_comp_ι {A B C E : AlgebraicGeometry.Scheme.{u}}
    {U : E.Opens} (e : A ≅ B) (g : B ⟶ C) [AlgebraicGeometry.IsOpenImmersion g] (i : U.toScheme ≅ C) :
    AlgebraicGeometry.IsOpenImmersion (e.hom ≫ g ≫ i.inv ≫ U.ι) :=
  inferInstance

end
