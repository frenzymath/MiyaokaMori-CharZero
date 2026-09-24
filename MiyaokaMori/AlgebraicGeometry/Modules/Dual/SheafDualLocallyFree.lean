import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFreeSheafFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor

/-! # The dual of a locally free sheaf is locally free of the same rank

The dual of a locally free sheaf is locally free of the same rank; this is what turns
"`Ω_{X/k}` is locally free" into "`T_X` is a vector bundle".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry in
/-- The dual of a locally free sheaf `E` of finite type is, near every point `x`, isomorphic to the free
sheaf of rank `rankAtStalk E x`. -/
private theorem dualLF.exists_trivialization {X : Scheme.{u}} (E : X.Modules) [E.IsFiniteType]
    [E.IsLocallyFree] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (Scheme.Modules.dual E) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf)
          (ULift.{u} (Fin (Scheme.Modules.rankAtStalk E x)))) := by
  obtain ⟨U, I, hxU, ⟨e⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree E x
  have : Finite I := Scheme.Modules.finite_index_of_restrict_iso_free E U I e x hxU
  have := Fintype.ofFinite I
  have hr := Scheme.Modules.rankAtStalk_of_restrict_iso_free E U I e x hxU
  have hcard : Fintype.card I = Fintype.card (ULift.{u} (Fin (Scheme.Modules.rankAtStalk E x))) := by
    rw [Fintype.card_ulift, Fintype.card_fin, hr]
  let eqv : I ≃ ULift.{u} (Fin (Scheme.Modules.rankAtStalk E x)) := Fintype.equivOfCardEq hcard
  let e' : (Scheme.Modules.pullback U.ι).obj E ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf)
        (ULift.{u} (Fin (Scheme.Modules.rankAtStalk E x))) :=
    e ≪≫ (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso eqv.toIso
  obtain ⟨d1⟩ := Scheme.Modules.dual_restrict E U
  obtain ⟨d2⟩ := Scheme.Modules.dual_free_iso (X := U.toScheme) (Scheme.Modules.rankAtStalk E x)
  exact ⟨U, hxU, ⟨d1 ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso e'.symm ≪≫ d2⟩⟩

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) [E.IsFiniteType] (r : ℕ) (hE : E.IsLocallyFree)
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = r) :
    (AlgebraicGeometry.Scheme.Modules.dual E).IsLocallyFree ∧
      ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk (AlgebraicGeometry.Scheme.Modules.dual E) x = r := by
  refine ⟨AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_pullback_iso_free _ fun x => ?_,
    fun x => ?_⟩
  · obtain ⟨U, hxU, he⟩ := dualLF.exists_trivialization E x
    exact ⟨U, _, hxU, he⟩
  · obtain ⟨U, hxU, ⟨e⟩⟩ := dualLF.exists_trivialization E x
    rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free _ U _ e x hxU,
      Fintype.card_ulift, Fintype.card_fin, hr x]

/-- The dual of a locally free sheaf of finite type is locally free. Unlike `isLocallyFree_dual`,
which packages "the dual is locally free" and "the dual has the same rank" together and therefore
carries the unused constant-rank hypothesis `hr`, this version needs no rank hypothesis
(`dualLF.exists_trivialization` takes the frame `ULift (Fin (rankAtStalk E x))` pointwise). -/
theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) [E.IsFiniteType] [E.IsLocallyFree] :
    (AlgebraicGeometry.Scheme.Modules.dual E).IsLocallyFree := by
  refine AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_pullback_iso_free _ fun x => ?_
  obtain ⟨U, hxU, he⟩ := dualLF.exists_trivialization E x
  exact ⟨U, _, hxU, he⟩

theorem AlgebraicGeometry.Scheme.Modules.isFiniteType_dual {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) [E.IsFiniteType] (hE : E.IsLocallyFree) :
    (AlgebraicGeometry.Scheme.Modules.dual E).IsFiniteType := by
  refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback _ fun x => ?_
  obtain ⟨U, hxU, ⟨e⟩⟩ := dualLF.exists_trivialization E x
  exact ⟨U, _, inferInstance, e.inv, hxU, @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv e)⟩

end
