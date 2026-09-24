import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfFreeAffineSections
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.EtaleChart
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Morphisms.GmActionGradingCorrespondence
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetChartTransitionSubstitution
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetCoordinateAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetLocalCoordinates
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetTransition
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetWeightOfOrderQ
import MiyaokaMori.Paper.S2WeightedJets.Charts.TransitionPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundleLocalFrame
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetWeightPartMonomialFrame
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback

/-! # The graded pieces of the jet algebra are locally free

The graded piece `S_j` of the jet algebra is locally free, with the monomials of weight `j` as a
basis over an affine open `U` on which `E` is trivial: locally `J_k^s|_U ≅ 𝔸_U^{(n+1)k}`, the
coordinate algebra is `O_U[x_{i,q}]`, and rescaling the jet parameter gives `x_{i,q}` weight `q`
(§2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem gradedPiece_isLocallyFree {k' : Type u} [Field k'] {C : SmoothProjectiveCurve k'}
    (Z : CategoryTheory.Over C.toScheme) (s : C.toScheme ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s] [AlgebraicGeometry.IsAffineHom Z.hom]
    (Zx : Z.left.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (k j : ℕ) :
    SheafOfModules.IsLocallyFree ((jetGradedAlgebra (k := k') Z s hs k).1.part j) ∧
      ∀ U : C.toScheme.affineOpens,
        Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle Z.hom s hs) ≅
          AlgebraicGeometry.Scheme.Modules.free (ULift.{u} (Fin (n + 1)))) →
        Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj
            ((jetGradedAlgebra (k := k') Z s hs k).1.part j) ≅
          AlgebraicGeometry.Scheme.Modules.free
            (ULift.{u} {m : (Fin (n + 1) × Fin k) →₀ ℕ |
              Finsupp.weight (fun iq => ((iq.2 : ℕ) + 1)) m = j})) := by
  let M := (jetGradedAlgebra (k := k') Z s hs k).1.part j
  have hlocal : ∀ x : C.toScheme, ∃ (U : C.toScheme.Opens) (I : Type u), x ∈ U ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) := by
    intro x
    obtain ⟨U, hxU, htriv⟩ := coneTangentBundle_exists_affine_frame
      Z.hom s hs Zx hsZx n x
    exact ⟨U.1, ULift.{u} {m : (Fin (n + 1) × Fin k) →₀ ℕ |
      Finsupp.weight (fun iq ↦ ((iq.2 : ℕ) + 1)) m = j}, hxU,
      jetWeightPart_pullback_iso_free_of_trivial Z s hs Zx hsZx n k j U htriv⟩
  have hM : M.IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_pullback_iso_free M hlocal
  refine ⟨hM, ?_⟩
  intro U htriv
  exact jetWeightPart_pullback_iso_free_of_trivial Z s hs Zx hsZx n k j U htriv

end
