import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.CoordinatePowerSection
import MiyaokaMori.Paper.S2WeightedJets.Intersection.CoordinatesNotAllVanish
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveDivisor

/-! # The coordinate divisors have empty total intersection

The intersection of the supports of all `s_k = (n+1)k` coordinate divisors is empty: all coordinates cannot vanish
at a point of a projective fiber (proof of Proposition 2.4 of the paper, eq. (2.10)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem splitWeightedCoord_iInter_support_empty {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ} (hkk : 1 ≤ kk) {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) :
    (⋂ p : Fin (n + 1) × Fin kk,
        haveI := coordPowSection_isLineBundle F m hm hdiv p
        SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection _ (coordPowSection F m hdiv p)).support)
      = (∅ : Set (splitWeightedProjectivization F kk).left) := by
  ext y
  constructor
  · intro hy
    obtain ⟨p, hp⟩ := splitWeightedCoord_not_all_vanish hkk F m hm hdiv y
    exact False.elim (hp (Set.mem_iInter.mp hy p))
  · intro hy
    exact False.elim hy

end
