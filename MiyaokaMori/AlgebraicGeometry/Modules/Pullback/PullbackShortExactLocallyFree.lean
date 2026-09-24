import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ShortExactLocalOnOpenCover
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ShortExactLocallySplit
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackOpenImmersionShortExact

/-! # Pullback of a short exact sequence with locally free quotient

A short exact sequence whose third term is finite locally free is locally split, hence its
pullback along any morphism is again short exact (used to pull back the relative tangent
sequence along a section).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The pullback of a short exact sequence with finite locally free third term is short exact. -/
theorem AlgebraicGeometry.Scheme.Modules.pullback_shortExact_of_locallyFree
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {S : CategoryTheory.ShortComplex Y.Modules}
    (hS : S.ShortExact) [S.X₃.IsLocallyFree] [S.X₃.IsFiniteType] :
    (S.map (AlgebraicGeometry.Scheme.Modules.pullback f)).ShortExact := by
  open AlgebraicGeometry in
  -- for each `x`, the sequence has a section on an open neighbourhood `U x` of `f x`
  choose U hU σ hσ using fun x : X => Scheme.Modules.shortExact_locallySplit hS (f x)
  have hcov : IsOpenCover fun x : X => f ⁻¹ᵁ U x :=
    IsOpenCover.mk (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hU x⟩)
  refine Scheme.Modules.shortExact_of_openCover _
    (X.openCoverOfIsOpenCover (fun x : X => f ⁻¹ᵁ U x) hcov) fun x => ?_
  -- split on `U x`; split short exact sequences are preserved by the additive functor `f'^*`
  have hSU := Scheme.Modules.shortExact_map_pullback_of_isOpenImmersion (U x).ι hS
  let spl : (S.map (Scheme.Modules.pullback (U x).ι)).Splitting :=
    ShortComplex.Splitting.ofExactOfSection _ hSU.exact (σ x) (hσ x) hSU.mono_f
  let f' : (f ⁻¹ᵁ U x).toScheme ⟶ (U x).toScheme := f ∣_ U x
  have h1 : ((S.map (Scheme.Modules.pullback (U x).ι)).map (Scheme.Modules.pullback f')).ShortExact :=
    (spl.map (Scheme.Modules.pullback f')).shortExact
  -- (W.ι)^* ∘ f^* ≅ f'^* ∘ (U.ι)^*
  let τ : Scheme.Modules.pullback (U x).ι ⋙ Scheme.Modules.pullback f' ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (f ⁻¹ᵁ U x).ι :=
    Scheme.Modules.pullbackComp f' (U x).ι ≪≫
      Scheme.Modules.pullbackCongr (morphismRestrict_ι f (U x)) ≪≫
      (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U x).ι f).symm
  exact ShortComplex.shortExact_of_iso (S.mapNatIso τ) h1

end
