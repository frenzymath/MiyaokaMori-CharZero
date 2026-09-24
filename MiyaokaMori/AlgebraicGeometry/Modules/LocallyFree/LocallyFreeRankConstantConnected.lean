import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # The rank of a locally free sheaf on a connected scheme is constant

On a connected scheme, the rank (fibre dimension) of a locally free sheaf of finite type is the
same at every point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry in
private theorem trivialization_of_over_iso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (I : Type u) (e0 : SheafOfModules.free I ≅ M.over U) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) := by
  let F : SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    (Scheme.Modules.overEquiv U).functor
  have : F.IsEquivalence := inferInstanceAs (Scheme.Modules.overEquiv U).functor.IsEquivalence
  have : PreservesColimitsOfShape (Discrete I) F :=
    (F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits.{u, u}).preservesColimitsOfShape
  have e1 : F.obj (M.over U) ≅ (Scheme.Modules.restrictFunctor U.ι).obj M :=
    (Scheme.Modules.overFunctorEquiv U).app M
  have e2 := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  have η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm
  have e3 := SheafOfModules.mapFreeIso F I η
  exact ⟨e2.symm ≪≫ e1.symm ≪≫ F.mapIso e0.symm ≪≫ e3.symm⟩

open AlgebraicGeometry in
private theorem exists_trivialization {X : Scheme.{u}} (M : X.Modules) [M.IsLocallyFree] (x : X) :
    ∃ (U : X.Opens) (I : Type u), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  have hx : x ∈ (⨆ i, q.X i : X.Opens) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hiso : IsIso (q.generators i).π := hq.isIso i
  exact ⟨q.X i, (q.generators i).I, hi,
    trivialization_of_over_iso M (q.X i) _ (asIso (q.generators i).π)⟩

/-- On a connected scheme, a locally free sheaf of finite type has the same rank at any two points. -/
theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_of_connected {X : AlgebraicGeometry.Scheme.{u}}
    [ConnectedSpace X] (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType] (x y : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk M x = AlgebraicGeometry.Scheme.Modules.rankAtStalk M y := by
  have hloc : IsLocallyConstant (fun z : X => AlgebraicGeometry.Scheme.Modules.rankAtStalk M z) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    obtain ⟨U, I, hzU, ⟨e⟩⟩ := exists_trivialization M z
    have : Finite I := AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free M U I e z hzU
    have := Fintype.ofFinite I
    refine ⟨U, U.isOpen, hzU, fun y hy => ?_⟩
    rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free M U I e y hy,
      AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free M U I e z hzU]
  exact hloc.apply_eq_of_preconnectedSpace x y

end
