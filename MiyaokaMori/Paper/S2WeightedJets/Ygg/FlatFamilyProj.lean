import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationFamilyProj
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S2WeightedJets.Intersection.FamilyFiberAtOne
import MiyaokaMori.Paper.S2WeightedJets.Intersection.FamilyFiberAtZero
import MiyaokaMori.Paper.S2WeightedJets.Intersection.FamilyFlatOverLine
import MiyaokaMori.Paper.S2WeightedJets.Intersection.FamilyProjectiveOverLine
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationOfBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # The deformation family of weighted projectivizations

The relative Proj `𝒴` of the deformed jet algebra is flat and projective over `C × 𝔸¹`, hence
projective over `𝔸¹`; its fiber at `λ = 1` is `Y_k^GG` and its fiber at `λ = 0` is the weighted
projectivization of copies of `E` (the deformation to a split weighted bundle in the proof of
Lemma 2.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem deformationFamily_flat_projective {k : Type u} [Field k] [CharZero k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) [AlgebraicGeometry.IsClosedImmersion sec]
    (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)]
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (hr : 1 ≤ r) (m : ℕ) (hm : m = (n + 1) * r * jetWeight r) :
    AlgebraicGeometry.Flat ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme) ∧
      AlgebraicGeometry.IsProjectiveMorphism ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme) ∧
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (deformedJetAlgebra Z sec hs r) (m : ℤ)).IsLineBundle ∧
      (∃ e : (((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiber (AlgebraicGeometry.Scheme.affineLineOver.point k 1) ≅ (weightedJetProjectivization (k := k) Z sec hs r).left),
      e.hom ≫ (weightedJetProjectivization (k := k) Z sec hs r).hom =
          ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k 1) ≫ (deformationFamily Z sec hs r).hom ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ∧
      ∀ m : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k 1))).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist (deformedJetAlgebra Z sec hs r) m) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 m))) ∧
      (∃ e : (((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiber (AlgebraicGeometry.Scheme.affineLineOver.point k 0) ≅ (@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).left),
      e.hom ≫ (@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).hom =
          ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k 0) ≫ (deformationFamily Z sec hs r).hom ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ∧
      ∀ m : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k 0))).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist (deformedJetAlgebra Z sec hs r) m) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist ((@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType))) m))) := by
  have hflat := deformationFamily_flat Z sec hs n r E hE hEZ hloc
  obtain ⟨hproj, hline⟩ := deformationFamily_projective Z sec hs n r E hE hEZ hloc hr m hm
  have hone := deformationFamily_fiber_one Z sec hs n r E hE hEZ hloc
  have hzero := deformationFamily_fiber_zero Z sec hs Zx hsZx n r E hE hEZ hloc
  exact ⟨hflat, hproj, hline, hone, hzero⟩

end
