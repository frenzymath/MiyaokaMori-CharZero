import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldEqResidueFieldAtGenericPoint
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDominantPullback

/-! # Function fields, residue fields at generic points, and finite covers

Bookkeeping for the affine lift after finite base change (Lemma 3.1 of the
paper): for a finite cover `η : C̃ → C̃₀` of smooth projective `k`-curves,

* `FiniteCover.pullbackFunctionHom_structureGerm`: pulling back functions along `η` is a
  `k`-algebra map for the structures `SmoothProjectiveCurve.functionFieldAlgebra` (stated with the
  structure maps unfolded to germs; because `η` is a `k`-morphism:
  `η ≫ (C̃₀ → Spec k) = (C̃ → Spec k)`);
* `FiniteCover.SpecMap_residueFieldCongr_residueFieldMap`: the morphism
  `Spec κ(η_{C̃}) → Spec κ(η_{C̃₀})` induced by `η` at the generic points (`residueFieldMap`, after
  `residueFieldCongr` for `η(η_{C̃}) = η_{C̃₀}`) is `Spec` of `K(C̃₀) → K(C̃)` (pullback of
  functions) transported by `functionFieldIsoResidueField` on both sides — the same computation
  as `FiniteCover.degree_eq_functionFieldDegree`;
* `AlgebraicGeometry.Scheme.SpecMap_functionFieldIsoResidueField_inv_fromSpecResidueField`:
  `Spec K(X) → Spec κ(η_X) → X` is `fromSpecStalk` at the generic point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Spec K(X) → Spec κ(η_X) → X` is `Spec K(X) → X` (`fromSpecStalk` at the generic point):
`fromSpecResidueField = Spec (residue) ≫ fromSpecStalk` and `functionFieldIsoResidueField.hom` is
the residue map. -/
theorem AlgebraicGeometry.Scheme.SpecMap_functionFieldIsoResidueField_inv_fromSpecResidueField
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] :
    AlgebraicGeometry.Spec.map X.functionFieldIsoResidueField.inv ≫
        X.fromSpecResidueField (genericPoint X) =
      X.fromSpecStalk (genericPoint X) := by
  unfold AlgebraicGeometry.Scheme.fromSpecResidueField
  rw [← Category.assoc, ← AlgebraicGeometry.Spec.map_comp]
  change AlgebraicGeometry.Spec.map (X.functionFieldIsoResidueField.hom ≫
    X.functionFieldIsoResidueField.inv) ≫ _ = _
  rw [Iso.hom_inv_id, AlgebraicGeometry.Spec.map_id, Category.id_comp]

variable {k : Type u} [Field k]

/-- The pullback of functions along a finite cover `η : C̃ → C̃₀` (a `k`-morphism) respects the
structure maps `k → K(C̃₀)`, `k → K(C̃)` (global functions of `Spec k` → global functions of the
curve → germ at the generic point; this is `algebraMap` for `SmoothProjectiveCurve.functionFieldAlgebra`):
both sides are the germ at the generic point of `C̃` of
the function `(C̃ → Spec k)^* r = η^* ((C̃₀ → Spec k)^* r)`
(`AlgebraicGeometry.Intersection.dominantFunctionFieldMap_germToFunctionField`, `FiniteCover.isOver`). -/
theorem FiniteCover.pullbackFunctionHom_structureGerm {Ct₀ : SmoothProjectiveCurve k}
    (η : FiniteCover k Ct₀) (r : k) :
    haveI : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
    haveI : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
    pullbackFunctionHom η.hom η.hom_genericPoint
        (Ct₀.toScheme.presheaf.germ ⊤ (genericPoint Ct₀.toScheme) (by simp)
          ((Ct₀.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
            ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) =
      η.source.toScheme.presheaf.germ ⊤ (genericPoint η.source.toScheme) (by simp)
        ((η.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) := by
  have : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
  have : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
  have : AlgebraicGeometry.IsDominant η.hom := inferInstance
  have : Nonempty (⊤ : Ct₀.toScheme.Opens) := ⟨⟨genericPoint Ct₀.toScheme, trivial⟩⟩
  have : Nonempty (⊤ : η.source.toScheme.Opens) := ⟨⟨genericPoint η.source.toScheme, trivial⟩⟩
  have : Nonempty (η.hom ⁻¹ᵁ (⊤ : Ct₀.toScheme.Opens)) :=
    ⟨⟨genericPoint η.source.toScheme, trivial⟩⟩
  -- the left-hand side is `dominantFunctionFieldMap η.hom` applied to a germ over `⊤`
  change AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom
      (Ct₀.toScheme.germToFunctionField ⊤
        ((Ct₀.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) =
    η.source.toScheme.germToFunctionField ⊤
      ((η.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv r))
  rw [AlgebraicGeometry.Intersection.dominantFunctionFieldMap_germToFunctionField η.hom ⊤]
  have hover : (η.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop =
      (Ct₀.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫ η.hom.appTop := by
    rw [← η.isOver]
    rfl
  rw [hover]
  rfl

/-- The morphism `Spec κ(η_{C̃}) → Spec κ(η_{C̃₀})` induced at the generic points by a finite cover
`η : C̃ → C̃₀` is `Spec` of the pullback of rational functions `K(C̃₀) → K(C̃)`
(`AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom`, which is `pullbackFunctionHom η.hom _` as a ring
map), read through `functionFieldIsoResidueField` on both curves (`dominantFunctionFieldMap` factors through the
residue maps: `residue_residueFieldMap`, `residue_residueFieldCongr`). -/
theorem FiniteCover.SpecMap_residueFieldCongr_residueFieldMap {Ct₀ : SmoothProjectiveCurve k}
    (η : FiniteCover k Ct₀) :
    haveI : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
    haveI : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
    haveI : AlgebraicGeometry.IsDominant η.hom := inferInstance
    AlgebraicGeometry.Spec.map ((Ct₀.toScheme.residueFieldCongr η.hom_genericPoint.symm).hom ≫
        η.hom.residueFieldMap (genericPoint η.source.toScheme)) =
      AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
        AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom) ≫
        AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv := by
  have : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
  have : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
  have : AlgebraicGeometry.IsDominant η.hom := inferInstance
  have hmap : AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom =
      Ct₀.toScheme.functionFieldIsoResidueField.hom ≫
        (Ct₀.toScheme.residueFieldCongr η.hom_genericPoint.symm).hom ≫
        η.hom.residueFieldMap (genericPoint η.source.toScheme) ≫
        η.source.toScheme.functionFieldIsoResidueField.inv := by
    unfold AlgebraicGeometry.Scheme.dominantFunctionFieldMap
    apply (cancel_mono (η.source.toScheme.residue (genericPoint η.source.toScheme))).1
    simp only [Category.assoc]
    rw [← AlgebraicGeometry.Scheme.residue_residueFieldMap]
    rw [← Category.assoc]
    rw [← AlgebraicGeometry.Scheme.residue_residueFieldCongr]
    simp [AlgebraicGeometry.Scheme.functionFieldIsoResidueField]
    exact η.hom_genericPoint.symm
  rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  calc (Ct₀.toScheme.residueFieldCongr η.hom_genericPoint.symm).hom ≫
        η.hom.residueFieldMap (genericPoint η.source.toScheme)
      = (Ct₀.toScheme.functionFieldIsoResidueField.inv ≫ AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom) ≫
          η.source.toScheme.functionFieldIsoResidueField.hom := by
        rw [hmap]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := rfl

end
