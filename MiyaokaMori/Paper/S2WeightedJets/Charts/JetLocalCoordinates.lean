import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAsSectionFiber
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetOpenRestriction
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S2WeightedJets.Charts.EtaleBaseChangeJets
import MiyaokaMori.AlgebraicGeometry.Varieties.EtaleChart
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetOfAffineSpace
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetLocalCoordinatesEtaleChart
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.UnbasedRelativeJetScheme
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # Local coordinates on the based jet scheme

The local coordinatization `J_k^s|_U ≃ 𝔸_U^{(n+1)k}` of the based jet scheme: an étale chart
replaces `Z|_U` by `𝔸^{n+1}_U`, the constant term is fixed at `s`, and formal étaleness gives a
unique lift of each truncated coordinate tuple (eq. (2.5) of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Local coordinates on the based jet scheme: over an affine open `U` on which `E` is trivial,
`J_k^s|_U ≃ 𝔸_U^{(n+1)k}` as `U`-schemes (eq. (2.5) of the paper). -/
theorem jet_local_coordinates {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    [C.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C.toScheme ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s]
    /- Based jets land in `Z^×`; here we only require an open neighbourhood of `s` that is smooth
       of relative dimension `n+1` over `C`. -/
    (Zx : Z.left.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (r : ℕ)
    (U : C.toScheme.affineOpens)
    /- An affine open `U` on which `E = s^*T_{Z/C}` is trivial. -/
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle Z.hom s hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    /- `J_k^s|_U ≃ 𝔸_U^{(n+1)k}` is an isomorphism of `U`-schemes: `φ` is compatible with the
       projections to `U`. -/
    ∃ φ : ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1).toScheme ≅
        AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme,
      φ.hom ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme ↘ U.1.toScheme) =
        (relativeJetScheme (k := k) Z s hs r).hom ∣_ U.1 := by
  obtain ⟨V, hVaff, hsV, hVU, hVx, ψ, hψet, hψover, hψs⟩ :=
    exists_etale_chart (k := k) Z.hom s hs Zx hsZx n U htriv
  letI : AlgebraicGeometry.IsAffine V.toScheme := hVaff
  letI : AlgebraicGeometry.IsAffineHom (Z.hom.resLE U.1 V hVU) := by
    apply AlgebraicGeometry.isAffineHom_of_isAffine
  exact relativeJetScheme_etale_chart (k := k) Z s hs U.1 V hsV hVU (n + 1) r ψ hψover hψs

end
