import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivize
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.NormalizedTupleNowhereZero
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.ProjQuotientGivesLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluation
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowLineBundle

/-! # Pullback of the polarization along `τ`

`τ^*B_k ≅ L^{-m}` (with `τ` the projectivization `ȷ.projectivize` of the normalized tuple of `ȷ`, `hτJ`): the
`m/q`-th power of a unit among the weight-`q` coefficients is again a unit, so the evaluation map
`ρ^*S_m → L^{-m}` is surjective everywhere (Section 3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- For general lift data `D` (with line bundle `L^∨`): if `τ = lift D`, then `τ^*B_κ ≅ L^{-(n+1)}`.
   `Ψ_{n+1}` is induced by `τ` and is an epimorphism; `(L^∨)^{⊗(n+1)} ≅ L^{-(n+1)}` compares the two encodings of
   tensor powers; then apply the degree-one presentation. -/

private theorem tau_pullback_polarization_aux {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ n : ℕ)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible (n + 1))]
    (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData (jetAlgebra f κ) ρ.hom
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules))
    (τ : ρ.source.toScheme ⟶ YGG f κ)
    (hτD : τ = AlgebraicGeometry.Scheme.relativeProj.lift (jetAlgebra f κ) ρ.hom
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) D)
    (hτ : τ ≫ YGG.proj f κ = ρ.hom) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj (polarization f κ (n + 1))
      ≅ (L.zpow (-((n + 1 : ℕ) : ℤ))).toModules) := by
  subst hτD
  let bridge : AlgebraicGeometry.Scheme.Modules.monoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (n + 1) ≅
      (L.zpow (-((n + 1 : ℕ) : ℤ))).toModules :=
    AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (n + 1)
  have : CategoryTheory.Epi (D.Ψ (n + 1)) :=
    AlgebraicGeometry.Scheme.relativeProj.LiftData.epi_of_sufficientlyDivisible _ _ _ D (n + 1) Fact.out
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.Scheme.relativeProj.lift_inducedBy (jetAlgebra f κ) ρ.hom
    (AlgebraicGeometry.Scheme.Modules.dual L.toModules) D (n + 1) hτ
  refine pullback_polarization_of_surjection f κ (n + 1) ρ L _ hτ
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).hom.app ((jetAlgebra f κ).part (n + 1)) ≫
      D.Ψ (n + 1)) ≫ bridge.hom) inferInstance ⟨ψ ≫ bridge.hom, ?_⟩
  exact (congrArg (· ≫ bridge.hom) hψ).trans (by simp only [Category.assoc]; rfl)

theorem tau_pullback_polarization {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) (hm : ∀ q ∈ Finset.Icc 1 κ, q ∣ m)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
    (hnz : NormalizedTupleNowhereZero J)
    (τ : ρ.source.toScheme ⟶ YGG f κ) (hτJ : τ = J.projectivize hnz)
    (hτ : τ ≫ YGG.proj f κ = ρ.hom) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj (polarization f κ m)
      ≅ (L.zpow (-(m : ℤ))).toModules) := by
  have hm' : (jetAlgebra f κ).SufficientlyDivisible m := Fact.out
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero hm'.1.ne'
  exact tau_pullback_polarization_aux f κ n ρ L _ τ hτJ hτ

end
