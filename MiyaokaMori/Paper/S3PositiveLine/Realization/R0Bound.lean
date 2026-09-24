import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.CoefficientSections
import MiyaokaMori.Paper.S3PositiveLine.Realization.DeltaR0LtK
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalar
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.Paper.S3PositiveLine.Realization.NonnegDegreeVanishing
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.PullbackDegreeFiniteCover
import MiyaokaMori.Paper.S3PositiveLine.Realization.R0GeOne

/-! # The bounds on `r₀`

`r₀ = ⌊ae/d_L⌋` satisfies `r₀ ≥ 1` and `δ·r₀ < k` (equation (4.3) in the proof of Theorem 4.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

lemma realization_module_iso_map_zero_iff {k : Type u} [Field k]
    {Y : AlgebraicGeometry.Scheme} {M N : Y.Modules} (τ : M ≅ N)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (τ.hom.val.app (Opposite.op ⊤)).hom x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hcomp := τ.hom_inv_id
    have hcomp' := congrArg (fun g => (g.val.app (Opposite.op ⊤)).hom) hcomp
    have hcomp'' := congrArg (fun g => g x) hcomp'
    change (τ.inv.val.app (Opposite.op ⊤)).hom
        ((τ.hom.val.app (Opposite.op ⊤)).hom x) = x at hcomp''
    rw [hx, map_zero] at hcomp''
    exact hcomp''.symm
  · intro hx
    rw [hx, map_zero]

theorem r0_bound {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ δ : ℕ} (J : BasedJet f ρ L κ)
    (A : LineBundle C.toVariety) (hA : A = LineBundle.pullback f (X.OX 1))
    (hL : 0 < L.degree) (hA0 : 0 ≤ A.degree) (he : 0 < (ρ.degree : ℤ))
    (hns : ¬ J.IsGenericallyScalar)
    (hslope : (δ : ℤ) * A.degree * (ρ.degree : ℤ) < (κ : ℤ) * L.degree) :
    1 ≤ A.degree * (ρ.degree : ℤ) / L.degree ∧
      (δ : ℤ) * (A.degree * (ρ.degree : ℤ) / L.degree) < (κ : ℤ) := by
  let A0 : LineBundle C.toVariety := LineBundle.pullback f (X.OX 1)
  have hbound : L.degree ≤ A0.degree * (ρ.degree : ℤ) := by
    obtain ⟨ℓ, q, hq⟩ := jet_coefficient_ne_zero_of_not_scalar J hns
    let B : LineBundle ρ.source.toVariety := LineBundle.pullback ρ.hom A0
    let τ₀ : AlgebraicGeometry.Scheme.Modules.tensor (B.zpow 1).toModules
        (L.zpow (-((q : ℕ) + 1 : ℤ))).toModules ≅
        AlgebraicGeometry.Scheme.Modules.tensor B.toModules
          (L.zpow (-((q : ℕ) + 1 : ℤ))).toModules :=
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (B.zpow 1).toModules (L.zpow (-((q : ℕ) + 1 : ℤ))).toModules) ≪≫
        (CategoryTheory.MonoidalCategory.tensorIso B.zpowOneIso
          (CategoryTheory.Iso.refl _)) ≪≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B.toModules
          (L.zpow (-((q : ℕ) + 1 : ℤ))).toModules).symm
    let τ : ((B.zpow 1).tensor (L.zpow (-((q : ℕ) + 1 : ℤ)))).toModules ≅
        (B.tensor (L.zpow (-((q : ℕ) + 1 : ℤ)))).toModules :=
      (CategoryTheory.eqToIso
        (LineBundle.tensor_toModules (B.zpow 1)
          (L.zpow (-((q : ℕ) + 1 : ℤ))))) ≪≫ τ₀ ≪≫
        (CategoryTheory.eqToIso
          (LineBundle.tensor_toModules B
            (L.zpow (-((q : ℕ) + 1 : ℤ))))).symm
    let c' : ((((B.tensor
        (L.zpow (-((q : ℕ) + 1 : ℤ)))).toModules.val.obj
        (Opposite.op ⊤)) : Type u)) :=
      (τ.hom.val.app (Opposite.op ⊤)).hom (BasedJet.coefficient J ℓ ((q : ℕ) + 1))
    have hc' : c' ≠ 0 := by
      intro hz
      apply hq
      exact (realization_module_iso_map_zero_iff (k := k)
        (Y := ρ.source.toScheme) τ
        (BasedJet.coefficient J ℓ ((q : ℕ) + 1))).mp (by simpa [c'] using hz)
    have hqbound : ((q : ℕ) + 1 : ℤ) * L.degree ≤ A0.degree * (ρ.degree : ℤ) := by
      exact coefficient_degree_bound A0 ρ L ((q : ℕ) + 1) c' hc'
    have hqpos : 0 < ((q : ℕ) + 1 : ℤ) := by omega
    have hmul : L.degree ≤ ((q : ℕ) + 1 : ℤ) * L.degree := by
      nlinarith
    exact le_trans hmul hqbound
  have hboundA : L.degree ≤ A.degree * (ρ.degree : ℤ) := by
    simpa [A0, hA] using hbound
  constructor
  · exact r0_ge_one hL hboundA
  · exact delta_r0_lt_k hL he hA0 hslope

end
