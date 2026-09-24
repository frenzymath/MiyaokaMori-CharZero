import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.RingTheory.PolynomialLowDegreeDivisibleZero
import MiyaokaMori.Paper.S3PositiveLine.Realization.SubstitutedPolynomialDegree
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # The equations vanish identically

`F_j(P_0,…,P_N)` has `ξ`-degree `≤ δr₀ < k` and vanishes on `C̃_(k)(L)` (i.e. is divisible by `t^{k+1}`),
hence it vanishes identically on `Tot(L)` (proof of Theorem 4.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry BigOperators CategoryTheory.MonoidalCategory

noncomputable section

private lemma sheaf_hom_app_zero {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules}
    (f : A ⟶ B) :
    ((f.val.app (Opposite.op ⊤)).hom (0 : (A.val.obj (Opposite.op ⊤) : Type u))) = 0 := by
  exact (f.val.app (Opposite.op ⊤)).hom.map_zero

private lemma pushforwardSectionToPullback_zero {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) :
    AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules 0 = 0 := by
  unfold AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback
  simp only [map_zero]
  exact sheaf_hom_app_zero _

private lemma monomial_zero {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (q : ℕ) :
    AlgebraicGeometry.Scheme.totalSpace.monomial L.toModules M.toModules q 0 = 0 := by
  unfold AlgebraicGeometry.Scheme.totalSpace.monomial
  rw [show ((AlgebraicGeometry.Scheme.totalSpace.monomialHom L.toModules M.toModules q).val.app
      (Opposite.op ⊤)).hom 0 = 0 by
        exact ((AlgebraicGeometry.Scheme.totalSpace.monomialHom
          L.toModules M.toModules q).val.app (Opposite.op ⊤)).hom.map_zero]
  exact pushforwardSectionToPullback_zero L M

theorem equations_vanish_identically {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {N r₀ δ κ : ℕ} {ι : Type u}
    (L M : LineBundle C.toVariety)
    (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) (hdeg : ∀ j, deg j ≤ δ)
    (hδr : δ * r₀ < κ)
    (P : Fin (N + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L M (P ℓ) ≤ (r₀ : WithBot ℕ))
    (θ : ∀ j, AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) (deg j) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.zpow (deg j)).toModules)
    (hjet : ∀ j, restrictToThickening L (M.zpow (deg j)) κ
        ((θ j).hom.app ⊤ (evalHomogeneousAtSections _ (F j) (hF j) P)) = 0) (j : ι) :
    evalHomogeneousAtSections _ (F j) (hF j) P = 0 := by
  let Q := (θ j).hom.app ⊤ (evalHomogeneousAtSections _ (F j) (hF j) P)
  have hdegQ : xiDegree L (M.zpow (deg j)) Q ≤ ((deg j * r₀ : ℕ) : WithBot ℕ) := by
    exact substituted_equation_degree L M P hP (F j) (hF j) (θ j)
  have hdegκ : xiDegree L (M.zpow (deg j)) Q ≤ (κ : WithBot ℕ) := by
    apply le_of_lt
    exact lt_of_le_of_lt hdegQ (by
      exact_mod_cast (lt_of_le_of_lt (Nat.mul_le_mul_right r₀ (hdeg j)) hδr))
  have hcoeff : ∀ q : ℕ, xiCoefficient L (M.zpow (deg j)) Q q = 0 := by
    intro q
    by_cases hq : q ≤ κ
    · have hrestrict := xiCoefficient_restrictToThickening
        L (M.zpow (deg j)) κ q hq Q
      have hz : xiCoefficientThickening L (M.zpow (deg j)) κ q 0 = 0 := by
        unfold xiCoefficientThickening
        rw [dif_pos hq]
        simp only [AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward]
        let a := ((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso
          (jetNeighborhood.proj L κ) (M.zpow (deg j)).toModules
          (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).inv.val.app
            (Opposite.op ⊤)).hom
        let b := ((MonoidalCategoryStruct.rightUnitor
          ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
            (M.zpow (deg j)).toModules)).inv.val.app (Opposite.op ⊤)).hom
        let c := ((CategoryTheory.MonoidalCategoryStruct.whiskerLeft
            (M.zpow (deg j)).toModules
            ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
              CategoryTheory.Limits.biproduct.π
                (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
                ⟨q, Nat.lt_succ_of_le hq⟩ ≫
              (truncatedJetAlgebra.pieceIso L q).hom ≫
              (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
                (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q).hom) ≫
            (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
              (M.zpow (deg j)).toModules
              (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv ≫
            (L.coefficientModuleIso (M.zpow (deg j)) q).hom).val.app
              (Opposite.op ⊤)).hom
        change c (a (b 0)) = 0
        have hb : b (0 : _) = 0 := b.map_zero
        have ha : a (0 : _) = 0 := a.map_zero
        calc
          c (a (b 0)) = c (a 0) := by rw [hb]; rfl
          _ = c 0 := by rw [ha]; rfl
          _ = 0 := c.map_zero
      have hzero : restrictToThickening L (M.zpow (deg j)) κ Q = 0 := by
        simpa [Q] using hjet j
      rw [hzero] at hrestrict
      rw [← hrestrict, hz]
    · have hq' : q > κ := Nat.lt_of_not_ge hq
      exact (xiDegree_lt_iff L (M.zpow (deg j)) Q κ).mp hdegκ q hq'
  have hsum := eq_sum_xiMonomial L (M.zpow (deg j)) Q
  have hQzero : Q = 0 := by
    rw [hsum]
    apply Finset.sum_eq_zero
    intro q hq
    rw [hcoeff q]
    unfold xiMonomial
    rw [show ((L.coefficientModuleIso (M.zpow (deg j)) q).inv.val.app
      (Opposite.op ⊤)).hom 0 = 0 by
        exact ((L.coefficientModuleIso (M.zpow (deg j)) q).inv.val.app
          (Opposite.op ⊤)).hom.map_zero]
    exact monomial_zero L (M.zpow (deg j)) q
  apply (ConcreteCategory.bijective_of_isIso ((θ j).hom.app ⊤)).injective
  have hmap : (θ j).hom.app ⊤ (evalHomogeneousAtSections _ (F j) (hF j) P) = 0 := by
    simpa [Q] using hQzero
  calc
    (θ j).hom.app ⊤ (evalHomogeneousAtSections _ (F j) (hF j) P) = 0 := hmap
    _ = (θ j).hom.app ⊤ 0 := (map_zero _).symm

end
