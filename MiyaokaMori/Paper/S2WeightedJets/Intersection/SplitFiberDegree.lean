import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationPreservesFiber
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberDegree
import MiyaokaMori.Paper.S2WeightedJets.Ygg.FiberDegreePositive
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra

/-! # The fiber degree of the split tautological class

After the two deformations the fiber degree of `H^sp` is still `v_k`, and still positive (Lemma 2.3 of the paper; eq. (2.6)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem split_fiberDegree_eq {k : Type u} [Field k] [IsAlgClosed k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) {n r : ℕ} (hr : 1 ≤ r)
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (F : SubbundleFiltration E (n + 1)) (m : ℕ)
    (hm : ((jetGradedAlgebra (k := k) Z sec hs r).1).SufficientlyDivisible m)
    (hdiv : ∀ q ∈ Finset.Icc 1 r, q ∣ m) (c : C.toScheme) (hc : IsClosed ({c} : Set C.toScheme))
    (h₁ : letI := (splitWeightedProjectivization F r).hom.fiberOverSpecResidueField c;
      IsProperOver (C.toScheme.residueField c) ((splitWeightedProjectivization F r).hom.fiber c))
    (h₂ : letI := (weightedJetProjectivization (k := k) Z sec hs r).hom.fiberOverSpecResidueField c;
      IsProperOver (C.toScheme.residueField c) ((weightedJetProjectivization (k := k) Z sec hs r).hom.fiber c))
    [SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ))] :
    haveI : SheafOfModules.IsLineBundle
        (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)) :=
      AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (jetGradedAlgebra (k := k) Z sec hs r).1 m hm;
    AlgebraicGeometry.relativePolarizationFiberDegree (splitWeightedProjectivization F r).hom
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ)) c h₁
      = AlgebraicGeometry.relativePolarizationFiberDegree
        (weightedJetProjectivization (k := k) Z sec hs r).hom
        (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)) c h₂ ∧
      0 < AlgebraicGeometry.relativePolarizationFiberDegree (splitWeightedProjectivization F r).hom
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ)) c h₁ := by
  classical
  letI : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)) :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist
      (jetGradedAlgebra (k := k) Z sec hs r).1 m hm
  letI := (splitWeightedProjectivization F r).hom.fiberOverSpecResidueField c
  letI := (weightedJetProjectivization (k := k) Z sec hs r).hom.fiberOverSpecResidueField c
  obtain ⟨e, he, htw⟩ := deformations_preserve_fiber (k := k) Z sec hs E hE hloc F
    (m : ℤ) c
  have heq :
      AlgebraicGeometry.relativePolarizationFiberDegree (splitWeightedProjectivization F r).hom
          (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ)) c h₁ =
        AlgebraicGeometry.relativePolarizationFiberDegree
          (weightedJetProjectivization (k := k) Z sec hs r).hom
          (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1
            (m : ℤ)) c h₂ := by
    change AlgebraicGeometry.topSelfIntersection
        ((splitWeightedProjectivization F r).hom.fiber c) h₁
          ((AlgebraicGeometry.Scheme.Modules.pullback
            ((splitWeightedProjectivization F r).hom.fiberι c)).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ))) =
      AlgebraicGeometry.topSelfIntersection
        ((weightedJetProjectivization (k := k) Z sec hs r).hom.fiber c) h₂
          ((AlgebraicGeometry.Scheme.Modules.pullback
            ((weightedJetProjectivization (k := k) Z sec hs r).hom.fiberι c)).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist
              (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)))
    have he' : e.hom ≫
        ((weightedJetProjectivization (k := k) Z sec hs r).hom.fiber c ↘
          AlgebraicGeometry.Spec (CommRingCat.of (C.toScheme.residueField c))) =
          ((splitWeightedProjectivization F r).hom.fiber c ↘
            AlgebraicGeometry.Spec (CommRingCat.of (C.toScheme.residueField c))) ≫
            CategoryTheory.CategoryStruct.id _ := by
      rw [CategoryTheory.Category.comp_id]
      change e.hom ≫
          ((weightedJetProjectivization (k := k) Z sec hs r).hom.fiber c ↘
            AlgebraicGeometry.Spec (CommRingCat.of (C.toScheme.residueField c))) =
        ((splitWeightedProjectivization F r).hom.fiber c ↘
          AlgebraicGeometry.Spec (CommRingCat.of (C.toScheme.residueField c)))
      exact he
    exact topSelfIntersection_eq_of_iso (k := C.toScheme.residueField c)
      (k' := C.toScheme.residueField c) (σ := RingEquiv.refl _)
      (e := e) (by simpa using he') h₁ h₂
      ((AlgebraicGeometry.Scheme.Modules.pullback
        ((weightedJetProjectivization (k := k) Z sec hs r).hom.fiberι c)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist
          (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)))
      ((AlgebraicGeometry.Scheme.Modules.pullback
        ((splitWeightedProjectivization F r).hom.fiberι c)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ))) htw
  constructor
  · exact heq
  · rw [heq]
    exact fiberDegree_pos (k := k) Z sec hs n r hr hloc m hm hdiv c hc h₂

end
