import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ShortExactLocalOnOpenCover
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ShortExactLocallySplit
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackOpenImmersionShortExact
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualShortExactLocallyFreeDualSheafFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheafOld

/-! # The dual of a short exact sequence of locally free sheaves

A short exact sequence of finite locally free sheaves stays short exact after applying the dual
`Hom(−, O_X)` (the sequence is locally split). Used for the dual of the tangent sequence
(2.2) in §2.1 of the paper.

## Route

Work with the sheafification-free dual `dualSheaf` (`DualSheaf`), made into an
additive contravariant functor `T = dualSheafFunctor X` in
`DualShortExactLocallyFreeDualSheafFunctor`; `dualSheafIsoOld M : dualSheaf M ≅ Modules.dual M`
transports the result to the locked statement (the maps `i`, `π` are the conjugates of
`T S.g`, `T S.f` by these isomorphisms).

1. (Local splitting.) `S.X₃` finite locally free and `S.g` epi: every `x` has an open `U ∋ x`
   with a section `σ` of `S.g|_U` (`shortExact_locallySplit`).
   `S|_U` is short exact (`shortExact_map_pullback_of_isOpenImmersion`), hence
   `Splitting.ofExactOfSection` splits it.
2. (Dual of a split sequence.) An additive functor sends a splitting to a splitting
   (`Splitting.op`, `Splitting.map`), and a split short complex is short exact
   (`Splitting.shortExact`). So `(S|_U)ᵒᵖ` mapped by `T_U` is short exact.
3. (Dual commutes with restriction, naturally.) `dualSheafRestrictNatIso`:
   `T_X ⋙ restrictFunctor U.ι ≅ (restrictFunctor U.ι)ᵒᵖ ⋙ T_U`, whiskered with
   `restrictFunctorIsoPullback`, gives `(S.op.map T_X).map (pullback U.ι) ≅ (S|_U).op.map T_U`
   (`ShortComplex.mapNatIso`); short exactness transports along it (`shortExact_of_iso`).
4. (Global.) Short exactness is local on an open cover
   (`shortExact_of_openCover`).

The hypotheses `[S.X₁.IsLocallyFree] [S.X₂.IsLocallyFree]` of the locked statement are not used.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

attribute [local instance] AlgebraicGeometry.Scheme.Modules.dualSheafFunctor_additive

/-- The dual (sheafification-free version `dualSheaf`) of a short exact sequence of
`𝒪_X`-modules whose quotient term is finite locally free is short exact:
`0 → S.X₃^∨ → S.X₂^∨ → S.X₁^∨ → 0`. Proof: steps 1–4 of the module docstring. -/
theorem AlgebraicGeometry.Scheme.Modules.dualSheafFunctor_shortExact {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₃.IsLocallyFree] [S.X₃.IsFiniteType] :
    (S.op.map (Scheme.Modules.dualSheafFunctor X)).ShortExact := by
  choose U hU σ hσ using fun x : X => Scheme.Modules.shortExact_locallySplit hS x
  have hcov : IsOpenCover U :=
    IsOpenCover.mk (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hU x⟩)
  refine Scheme.Modules.shortExact_of_openCover _ (X.openCoverOfIsOpenCover U hcov) fun x => ?_
  -- on `U x` the sequence splits, so its dual splits, hence is short exact
  have hSU := Scheme.Modules.shortExact_map_pullback_of_isOpenImmersion (U x).ι hS
  let spl : (S.map (Scheme.Modules.pullback (U x).ι)).Splitting :=
    ShortComplex.Splitting.ofExactOfSection _ hSU.exact (σ x) (hσ x) hSU.mono_f
  have h1 : ((S.map (Scheme.Modules.pullback (U x).ι)).op.map
      (Scheme.Modules.dualSheafFunctor (U x).toScheme)).ShortExact :=
    (spl.op.map (Scheme.Modules.dualSheafFunctor (U x).toScheme)).shortExact
  -- dual commutes with restriction, naturally
  let e := Scheme.Modules.restrictFunctorIsoPullback (U x).ι
  let τ : Scheme.Modules.dualSheafFunctor X ⋙ Scheme.Modules.pullback (U x).ι ≅
      (Scheme.Modules.pullback (U x).ι).op ⋙ Scheme.Modules.dualSheafFunctor (U x).toScheme :=
    Functor.isoWhiskerLeft (Scheme.Modules.dualSheafFunctor X) e.symm ≪≫
      Scheme.Modules.dualSheafRestrictNatIso X (U x) ≪≫
      Functor.isoWhiskerRight (NatIso.op e).symm (Scheme.Modules.dualSheafFunctor (U x).toScheme)
  exact ShortComplex.shortExact_of_iso (S.op.mapNatIso τ).symm h1

theorem AlgebraicGeometry.Scheme.Modules.dual_shortExact {X : AlgebraicGeometry.Scheme.{u}}
    {S : CategoryTheory.ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsLocallyFree] [S.X₂.IsLocallyFree]
    [S.X₃.IsLocallyFree] [S.X₃.IsFiniteType] :
    ∃ (i : AlgebraicGeometry.Scheme.Modules.dual S.X₃ ⟶ AlgebraicGeometry.Scheme.Modules.dual S.X₂)
      (π : AlgebraicGeometry.Scheme.Modules.dual S.X₂ ⟶ AlgebraicGeometry.Scheme.Modules.dual S.X₁)
      (hz : i ≫ π = 0), (CategoryTheory.ShortComplex.mk i π hz).ShortExact := by
  have hS' := Scheme.Modules.dualSheafFunctor_shortExact hS
  let T := S.op.map (Scheme.Modules.dualSheafFunctor X)
  let e : ∀ M : X.Modules, Scheme.Modules.dualSheaf M ≅ Scheme.Modules.dual M :=
    fun M => Scheme.Modules.dualSheafIsoOld M
  -- `T.f`, `T.g` retyped with the objects spelled as `dualSheaf`, so that `rw` can see them
  let f' : Scheme.Modules.dualSheaf S.X₃ ⟶ Scheme.Modules.dualSheaf S.X₂ := T.f
  let g' : Scheme.Modules.dualSheaf S.X₂ ⟶ Scheme.Modules.dualSheaf S.X₁ := T.g
  have hfg : f' ≫ g' = 0 := T.zero
  refine ⟨(e S.X₃).inv ≫ f' ≫ (e S.X₂).hom, (e S.X₂).inv ≫ g' ≫ (e S.X₁).hom, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc f' g', hfg,
      zero_comp, comp_zero]
  · refine ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (e S.X₃) (e S.X₂) (e S.X₁) ?_ ?_) hS'
    · show (e S.X₃).hom ≫ ((e S.X₃).inv ≫ f' ≫ (e S.X₂).hom) = f' ≫ (e S.X₂).hom
      exact Iso.hom_inv_id_assoc (e S.X₃) (f' ≫ (e S.X₂).hom)
    · show (e S.X₂).hom ≫ ((e S.X₂).inv ≫ g' ≫ (e S.X₁).hom) = g' ≫ (e S.X₁).hom
      exact Iso.hom_inv_id_assoc (e S.X₂) (g' ≫ (e S.X₁).hom)

end
