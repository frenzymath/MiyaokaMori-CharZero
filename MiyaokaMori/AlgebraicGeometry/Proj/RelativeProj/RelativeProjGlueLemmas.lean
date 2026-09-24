import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq

/-! # Glue lemmas for morphisms into a relative Proj

Two general lemmas used by the construction of the lift `relativeProj.lift` into a relative Proj (Stacks 01O4,
`RelativeProjLift.lean`) to check that the glued morphism is a morphism over the base:

* `glueMorphisms_comp_eq_of_forall`: a glued morphism `𝒰.glueMorphisms F _ ≫ g` equals `h` as soon as it does on
  every piece of the cover (`Cover.hom_ext` + `Cover.ι_glueMorphisms`);
* `affineIso_inv_ι_hom`: over an affine open `W ⊆ X`, the composite `Proj A(W) ≅ π⁻¹W ↪ Proj_X S → X` is
  `Proj.toSpecZero ≫ Spec (unitZero) ≫ isoSpec⁻¹ ≫ W.ι` (Stacks 01NQ: the structure morphism of the affine chart
  `projChart_hom` composed with `affineIso_inv_ι`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

section GlueLemmas

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.relativeProj

/-- A glued morphism followed by `g` equals `h` as soon as this holds on every piece of the cover
(`Cover.hom_ext` + `Cover.ι_glueMorphisms`). -/
theorem glueMorphisms_comp_eq_of_forall {X Y Z : AlgebraicGeometry.Scheme.{u}} (𝒰 : X.OpenCover)
    (F : ∀ i, 𝒰.X i ⟶ Y) (hF : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ F i = pullback.snd _ _ ≫ F j)
    (g : Y ⟶ Z) (h : X ⟶ Z) (H : ∀ i, F i ≫ g = 𝒰.f i ≫ h) :
    𝒰.glueMorphisms F hF ≫ g = h :=
  𝒰.hom_ext _ _ (fun i => by rw [← Category.assoc, 𝒰.ι_glueMorphisms, H])

/-- `affineIso.inv ≫ ι ≫ π` is the composite `Proj A(W) → Spec A(W)_0 → Spec Γ(W) ≅ W ↪ X`
(the structure morphism `projChart_hom` of the chart of Stacks 01NQ, followed by `affineIso_inv_ι`). -/
theorem affineIso_inv_ι_hom {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (W : X.affineOpens) :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv ≫
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ≫
        (AlgebraicGeometry.Scheme.relativeProj S).hom =
      AlgebraicGeometry.Proj.toSpecZero (S.sectionsGrading W.1) ≫
        Spec.map (CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero ⟨W.1, W.2⟩)) ≫
        W.2.isoSpec.inv ≫ W.1.ι := by
  rw [← Category.assoc, AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι]
  exact S.toGradedAffineAlgebra.projChart_hom ⟨W.1, W.2⟩

end AlgebraicGeometry.Scheme.relativeProj

end GlueLemmas
