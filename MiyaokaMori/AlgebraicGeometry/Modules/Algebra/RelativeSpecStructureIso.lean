import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty

/-! # The structure map of the relative Spec is an isomorphism

The structure map `A → p_*O_{Spec_X A}` of the relative Spec (the value of the universal property at the
identity) and the isomorphism `p_*O_{Spec_X A} ≅ A` (Stacks 01LQ: `π_*O = A`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The structure map `A → p_*O_{Spec_X A}` of the relative Spec: the value of the universal property at
`T = Spec_X A` and the identity morphism. -/
noncomputable def AlgebraicGeometry.Scheme.relativeSpec.structureHom {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) :
    A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeSpec A).hom).obj
      (SheafOfModules.unit (AlgebraicGeometry.Scheme.relativeSpec A).left.ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.relativeSpecHomEquiv A (AlgebraicGeometry.Scheme.relativeSpec A)
    (CategoryTheory.CategoryStruct.id _)).1

/- Stacks 01LQ(2): `p_*O_{Spec_X A} = A`. Route:
   (1) the section maps of `structureHom` are those of the morphism of sheaves of rings `structureRingMap`
       (the pullback along the identity is the identity);
   (2) on an affine open `U` the component of `structureRingMap` is `sectionsToFunctions A U`, the composite
       of the three isomorphisms `A(U) ≅ Γ(Spec A(U), ⊤) ≅ Γ(π⁻¹U, ⊤) ≅ Γ(Spec_X A, π⁻¹U)` (`ΓSpecIso`,
       `affineIso`, `topIso`), packaged as the explicit isomorphism `sectionsIso`;
   (3) a morphism of sheaves that is an isomorphism on a basis is an isomorphism (Mathlib
       `TopCat.Sheaf.isIso_iff_isIso_basis`), and `SheafOfModules.toSheaf` reflects isomorphisms. No
       quasi-coherence of `A` or `p_*O` is needed. -/

/-- The ring homomorphism on sections corresponding to the identity is the component of the morphism of
sheaves of rings `structureRingMap`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_id {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.Opens) :
    AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A (AlgebraicGeometry.Scheme.relativeSpec A)
        (CategoryTheory.CategoryStruct.id _) U =
      ((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op U)).hom := by
  have h1 : ∀ (Y : AlgebraicGeometry.Scheme.{u}) (V : Y.Opens) (e : V = V),
      Y.presheaf.map (CategoryTheory.eqToHom e).op = CategoryTheory.CategoryStruct.id _ := by
    intro Y V e; simp
  refine RingHom.ext fun c => ?_
  exact congrArg (fun f : Γ((AlgebraicGeometry.Scheme.relativeSpec A).left,
        (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) ⟶
      Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) =>
      f.hom (((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op U)).hom c))
    (h1 _ ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) _)

/-- **`structureHom` on sections** (any open): `structureHom(c) = structureRingMap(c)`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_apply {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.Opens) (c : A.carrier.val.obj (Opposite.op U)) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U c =
      ((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op U)).hom c := by
  rw [← AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_id]
  rfl

/-- The **explicit** ring isomorphism `A(U) ≅ Γ(Spec_X A, π⁻¹U)` on an affine open `U`: forward map
`sectionsToFunctions A U`, inverse `topIso⁻¹ ≫ (affineIso⁻¹)^♯ ≫ ΓSpecIso`; both directions unfold. -/
noncomputable def AlgebraicGeometry.Scheme.relativeSpec.sectionsIso {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens) :
    CommRingCat.of (A.sectionsRing U.1) ≅
      Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (A.sectionsRing U.1))).symm ≪≫
    { hom := (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).hom.appTop
      inv := (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv.appTop
      hom_inv_id := by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, CategoryTheory.Iso.inv_hom_id,
          AlgebraicGeometry.Scheme.Hom.id_appTop]
      inv_hom_id := by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, CategoryTheory.Iso.hom_inv_id,
          AlgebraicGeometry.Scheme.Hom.id_appTop] } ≪≫
    ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).topIso

theorem AlgebraicGeometry.Scheme.relativeSpec.sectionsIso_hom {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens) :
    (AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U).hom =
      AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A U := rfl

/-- On an affine open, the section map of `structureHom` is the forward map of the explicit isomorphism
`sectionsIso`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_affine {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens) (c : A.carrier.val.obj (Opposite.op U.1)) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U.1 c =
      (AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U).hom.hom c := by
  rw [AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_apply,
    AlgebraicGeometry.Scheme.relativeSpec.structureRingMap_app_affine]
  rfl

/-- On an affine open, the section map of `structureHom` is bijective. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_bijective {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens) :
    Function.Bijective ((AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U.1).hom := by
  have hbij : Function.Bijective (AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U).hom.hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (CategoryTheory.Iso.isIso_hom (AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U))
  have heq := AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_affine A U
  exact ⟨fun a b hab => hbij.1 ((heq a).symm.trans (hab.trans (heq b))),
    fun y => (hbij.2 y).imp fun a ha => (heq a).trans ha⟩

/-- Variable level: a morphism of sheaves of modules that is bijective on sections over every affine open
is an isomorphism. Same proof as `Scheme.Modules.isIso_of_affine`, without the two quasi-coherence
hypotheses that are not used there. -/
theorem AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_on_affineOpens {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Bijective (φ.app U.1).hom) : CategoryTheory.IsIso φ := by
  have hb : TopologicalSpace.Opens.IsBasis (Set.range (fun U : X.affineOpens => (U.1 : X.Opens))) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  have h1 : CategoryTheory.IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    TopCat.Sheaf.isIso_iff_isIso_basis hb (fun U =>
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr (h U))
  exact CategoryTheory.isIso_of_reflects_iso (C := SheafOfModules.{u} X.ringCatSheaf) φ
    (SheafOfModules.toSheaf X.ringCatSheaf)

/-- **Stacks 01LQ(2)**: the structure map `A → p_*O_{Spec_X A}` is an isomorphism. -/
instance AlgebraicGeometry.Scheme.relativeSpec.structureHom_isIso {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeSpec.structureHom A) :=
  AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_on_affineOpens _
    (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_bijective A)

noncomputable def AlgebraicGeometry.Scheme.relativeSpec.structureIso {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) :
    A.carrier ≅ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeSpec A).hom).obj
      (SheafOfModules.unit (AlgebraicGeometry.Scheme.relativeSpec A).left.ringCatSheaf) :=
  CategoryTheory.asIso (AlgebraicGeometry.Scheme.relativeSpec.structureHom A)

/-- **The inverse of `structureIso` on sections** (affine opens): the inverse is the inverse of the explicit
isomorphism `sectionsIso` (`topIso⁻¹ ≫ (affineIso⁻¹)^♯ ≫ ΓSpecIso`). Use this to unfold `structureIso.inv`
without touching `asIso`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_affine {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens)
    (s : Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1)) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U.1 s =
      (AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U).inv.hom s := by
  apply (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_bijective A U).1
  have h1 : ((AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U.1).hom
      ((AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U.1 s) = s :=
    congrArg (fun f : (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeSpec A).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.relativeSpec A).left.ringCatSheaf) ⟶ _ => (f.app U.1).hom s)
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv_hom_id
  have h2 : (AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U).hom.hom
      ((AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U).inv.hom s) = s :=
    congrArg (fun f : Γ((AlgebraicGeometry.Scheme.relativeSpec A).left,
        (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1) ⟶ _ => f.hom s)
      (AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U).inv_hom_id
  exact h1.trans ((AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_affine A U _).trans h2).symm

/-- Corollary: `p_*O_{Spec_X A}` is quasi-coherent (isomorphic to the quasi-coherent `A`; this does not use
that pushforward along an affine morphism preserves quasi-coherence). -/
theorem AlgebraicGeometry.Scheme.relativeSpec.pushforward_unit_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeSpec A).hom).obj
      (SheafOfModules.unit (AlgebraicGeometry.Scheme.relativeSpec A).left.ringCatSheaf)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso A) A.quasicoherent

end
