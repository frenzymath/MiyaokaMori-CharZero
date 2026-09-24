import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetGenericChartCoords
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Basis
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpace
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftLocalRingHomInFrame
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PieceIsoFramePow
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftPrecompInFrame

/-! # The local ring map of `precompLiftData` at a chart coordinate, read in a frame

The computation of `BasedJet.exists_genericTrivialization_of_frame` at the level of an arbitrary morphism
`g : T' ⟶ C̃` (the specialisation `T' = Spec κ(η_{C̃})`, `g = η` is `BasedJet.genericLiftData`, by definition
`J.precompLiftData η _`): if `Ψ_{w p}(x_p)|_U = r • μ^{⊗ w p}` on `U ⊆ ρ⁻¹V` and `e` is a trivialization of
`𝟙^*g^*L^∨` with `e(𝟙^*g^*δ|_⊤) = 1` (`δ = zpowNegOneIso μ`), then the value of the local ring map of the lift at
`x_p` is `𝟙^♯(g^♯ r)`. Stated over a general `T'` because elaborating the same equalities directly at
`Spec κ(η_{C̃})` is very slow (cf. the remark on `BasedJet.precompLiftData` in `JetProjectivize`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

theorem BasedJet.liftLocalPieceAux_precompLiftData_eq_of_frame {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    {T' : AlgebraicGeometry.Scheme.{u}} (g : T' ⟶ ρ.source.toScheme)
    (hgen : ∀ t : T', ∃ (U : T'.Opens) (_ : t ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map
        (AlgebraicGeometry.Scheme.relativeProj.precompΨ g J.weightComponent m)))
    {V : C.toScheme.Opens} (chart : HonestJetChart f κ V)
    (hW : (⊤ : T'.Opens) ≤ (𝟙 T' ≫ (g ≫ ρ.hom)) ⁻¹ᵁ V)
    {U : ρ.source.toScheme.Opens} (hUV : U ≤ ρ.hom ⁻¹ᵁ V)
    (hι : (⊤ : T'.Opens) ≤ (𝟙 T') ⁻¹ᵁ (g ⁻¹ᵁ U))
    (μ : Γ((L.zpow (-1)).toModules, U))
    (e : (AlgebraicGeometry.Scheme.Modules.pullback (𝟙 T')).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit T'.ringCatSheaf)
    (he : AlgebraicGeometry.Scheme.Modules.Hom.app e.hom ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullback (𝟙 T')).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules))).res hι
        (MiyaokaMori.DualPullback.unitSec (𝟙 T') _
          (MiyaokaMori.DualPullback.unitSec g (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (AlgebraicGeometry.Scheme.Modules.Hom.app L.zpowNegOneIso.hom U μ)))) = (1 : Γ(T', ⊤)))
    (p : Fin (X.toVariety.dim + 1) × Fin κ) (r : Γ(ρ.source.toScheme, U))
    (hΨ : (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨p⟩), U) from
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)).val.map (CategoryTheory.homOfLE hUV).op).hom
          (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
            (J.weightComponent (jetWeights.{u} X.toVariety.dim κ ⟨p⟩))).val.app
              (Opposite.op V)).hom (chart.coords p))) =
          r • (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨p⟩), U) from
            (((truncatedJetAlgebra.pieceIso L (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)).hom.val.app
              (Opposite.op U)).hom
              (truncatedJetAlgebra.framePow L U μ (jetWeights.{u} X.toVariety.dim κ ⟨p⟩))))) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux (J.precompLiftData g hgen) (𝟙 T') e V hW
        (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) (chart.coords p) =
      AlgebraicGeometry.Scheme.Hom.appLE (𝟙 T') (g ⁻¹ᵁ U) ⊤ hι (g.app U r) := by
  have hWT : g ⁻¹ᵁ U ≤ (g ≫ ρ.hom) ⁻¹ᵁ V := fun y hy => hUV hy
  have hx₀ : (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
        (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)).res hUV
      (AlgebraicGeometry.Scheme.Modules.Hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _
          (J.weightComponent (jetWeights.{u} X.toVariety.dim κ ⟨p⟩))) V (chart.coords p) :
        Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          (jetWeights.{u} X.toVariety.dim κ ⟨p⟩), ρ.hom ⁻¹ᵁ V)) =
      r • AlgebraicGeometry.Scheme.Modules.sectionPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) U
        (AlgebraicGeometry.Scheme.Modules.Hom.app L.zpowNegOneIso.hom U μ) (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) :=
    hΨ.trans (congrArg (fun z => r • z)
      (truncatedJetAlgebra.pieceIso_hom_app_framePow L U μ (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)))
  have hx := AlgebraicGeometry.Scheme.relativeProj.res_homEquiv_precompΨ_app_eq_smul_sectionPow
    J.weightComponent g (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) V (chart.coords p) U hUV
    (AlgebraicGeometry.Scheme.Modules.Hom.app L.zpowNegOneIso.hom U μ) r hx₀ hWT
  exact AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_eq_appLE_of_res_eq_smul_sectionPow
    (J.precompLiftData g hgen) (𝟙 T') e V hW (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) (chart.coords p)
    (g ⁻¹ᵁ U) hWT hι
    (MiyaokaMori.DualPullback.unitSec g (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
      (AlgebraicGeometry.Scheme.Modules.Hom.app L.zpowNegOneIso.hom U μ))
    (g.app U r) hx he

end
