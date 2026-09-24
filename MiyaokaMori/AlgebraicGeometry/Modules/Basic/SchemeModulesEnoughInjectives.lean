import MiyaokaMori.Prelude

/-! # The category of sheaves of modules on a scheme has enough injectives

The category `X.Modules` of `O_X`-modules on a scheme `X` has enough injectives (Stacks 01DI / Hartshorne III.2.2).

References: Stacks 01DI (`injectives-lemma-sheaves-modules-space`); Hartshorne III.2.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Stacks 01DI (Hartshorne III.2.2): the category of `O_X`-modules on a ringed space has enough injectives.
   `X.Modules = SheafOfModules X.ringCatSheaf`.

   Two possible routes: (A) the original route of 01DI (embedding into a product of skyscraper sheaves)
   + `EnoughInjectives.of_adjunction`; (B) prove `IsGrothendieckAbelian (SheafOfModules R)` and use
   Mathlib's `IsGrothendieckAbelian.enoughInjectives`. We follow route (B); Mathlib already provides all
   the pieces at both levels, they only need to be connected.

   Presheaf level `PresheafOfModules.{u} R` (`C` a small category, `R : Cᵒᵖ ⥤ RingCat.{u}`):
   * AB5: `HasExactColimitsOfShape.domain_of_functor` pulls the AB5 property of `Cᵒᵖ ⥤ AddCommGrpCat`
     (functor category instance + AB5 for `AddCommGrpCat`) back along the forgetful functor `toPresheaf R`;
     `toPresheaf` preserves finite limits, reflects finite limits and preserves colimits of every shape
     (all Mathlib instances).
   * Separator: Mathlib's `PresheafOfModules.freeYoneda.isSeparating` (the family of free Yoneda presheaves
     of modules is separating) plus `ObjectProperty.IsSeparating.isSeparator_coproduct`, taking the
     coproduct of the family over `C`.

   Sheaf level `SheafOfModules.{u} R` (`R : Sheaf J RingCat.{u}`):
   * AB5: `Adjunction.hasExactColimitsOfShape` applied to the sheafification adjunction
     `sheafification (𝟙 R.obj) ⊣ SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)`
     (right adjoint fully faithful, left adjoint preserves finite limits).
   * Separator: sheafify the family of free Yoneda presheaves of modules (`freeYonedaSheaf`). Its separating
     property follows from faithfulness of the right adjoint + naturality of the hom bijection of the
     adjunction, see `isSeparating_freeYonedaSheaf`.
   Thus the four fields of `IsGrothendieckAbelian.{u}` are available and `IsGrothendieckAbelian.enoughInjectives`
   gives the conclusion.

   These intermediate results are stated as `theorem`s and not registered as global instances: they are
   enabled locally by `have` only at the end of this file, to avoid adding wide-ranging new candidates
   such as `AB5OfSize` / `HasSeparator` / `IsGrothendieckAbelian` to instance search throughout the
   project. Only the `enoughInjectives` instance is exported. -/

namespace PresheafOfModules

variable {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- Filtered colimits in the category of presheaves of modules are exact (single-shape version of AB5):
pulled back from the functor category along the forgetful functor
`toPresheaf R : PresheafOfModules R ⥤ (Cᵒᵖ ⥤ AddCommGrpCat)`. -/
theorem hasExactColimitsOfShape_of_isFiltered (K : Type u) [Category.{u} K] [IsFiltered K] :
    HasExactColimitsOfShape K (PresheafOfModules.{u} R) :=
  HasExactColimitsOfShape.domain_of_functor K (toPresheaf R)

/-- The category of presheaves of modules satisfies AB5. -/
theorem ab5OfSize : AB5OfSize.{u, u} (PresheafOfModules.{u} R) where
  ofShape K _ _ := hasExactColimitsOfShape_of_isFiltered R K

/-- The coproduct of the free Yoneda presheaves of modules `(free R).obj (yoneda.obj X)` (`X : C`) is a
separator of the category of presheaves of modules. -/
theorem isSeparator_freeYonedaCoproduct :
    IsSeparator (∐ (yoneda ⋙ free R).obj) :=
  ObjectProperty.IsSeparating.isSeparator_coproduct (freeYoneda.isSeparating R)

/-- The category of presheaves of modules has a separator. -/
theorem hasSeparator : HasSeparator (PresheafOfModules.{u} R) :=
  ⟨_, isSeparator_freeYonedaCoproduct R⟩

/-- The category of presheaves of modules on a small category is a Grothendieck abelian category. -/
theorem isGrothendieckAbelian : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R) := by
  have := ab5OfSize R
  have := hasSeparator R
  exact { }

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Filtered colimits in the category of sheaves of modules are exact (single-shape version of AB5):
transported from the presheaf level along the sheafification adjunction (right adjoint fully faithful,
left adjoint `sheafification` preserves finite limits). -/
theorem hasExactColimitsOfShape_of_isFiltered (K : Type u) [Category.{u} K] [IsFiltered K] :
    HasExactColimitsOfShape K (SheafOfModules.{u} R) := by
  have := PresheafOfModules.hasExactColimitsOfShape_of_isFiltered R.obj K
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

/-- The category of sheaves of modules satisfies AB5. -/
theorem ab5OfSize : AB5OfSize.{u, u} (SheafOfModules.{u} R) where
  ofShape K _ _ := hasExactColimitsOfShape_of_isFiltered R K

/-- The sheafification of the free Yoneda presheaf of modules `(free R.obj).obj (yoneda.obj X)`, `X : C`. -/
abbrev freeYonedaSheaf (X : C) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj X))

/-- The sheafified free Yoneda family `freeYonedaSheaf R` is a separating family in the category of
sheaves of modules.

Proof: the right adjoint `SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)` of the sheafification
adjunction is faithful, so it suffices to separate at the presheaf level; there we use Mathlib's
`freeYoneda.isSeparating`, and every `a : (free R.obj).obj (yoneda.obj X) ⟶ G.obj M` corresponds under the
hom bijection of the adjunction to some `freeYonedaSheaf R X ⟶ M`; conclude by naturality of the hom
bijection in the right variable. -/
theorem isSeparating_freeYonedaSheaf :
    ObjectProperty.IsSeparating (.ofObj (freeYonedaSheaf R)) := by
  intro M N f g hfg
  set adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj) with hadj
  have hfaithful : (SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj)).Faithful := inferInstance
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
  refine PresheafOfModules.freeYoneda.isSeparating R.obj _ _ ?_
  rintro _ ⟨X⟩ a
  have h := hfg _ (ObjectProperty.ofObj_apply _ X) ((adj.homEquiv _ _).symm a)
  have h' := congrArg (adj.homEquiv _ _) h
  rwa [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply] at h'

/-- The category of sheaves of modules has a separator (the coproduct of the sheafified free Yoneda family). -/
theorem hasSeparator : HasSeparator (SheafOfModules.{u} R) :=
  ⟨_, (isSeparating_freeYonedaSheaf R).isSeparator_coproduct⟩

/-- The category of sheaves of modules on a small site is a Grothendieck abelian category. -/
theorem isGrothendieckAbelian : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  have := ab5OfSize R
  have := hasSeparator R
  exact { }

/-- The category of sheaves of modules has enough injectives (the general form of Stacks 01DI). -/
theorem enoughInjectives : EnoughInjectives (SheafOfModules.{u} R) := by
  have := isGrothendieckAbelian R
  infer_instance

end SheafOfModules

theorem AlgebraicGeometry.Scheme.Modules.enoughInjectives_modules (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EnoughInjectives X.Modules := by
  have := SheafOfModules.enoughInjectives X.ringCatSheaf
  exact inferInstanceAs (EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf))

instance AlgebraicGeometry.Scheme.Modules.enoughInjectives (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EnoughInjectives X.Modules :=
  AlgebraicGeometry.Scheme.Modules.enoughInjectives_modules X

end
