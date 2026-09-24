import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestrictionIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerFiniteFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # The top exterior power of a locally free module is a line bundle

For an `O_X`-module `E` that is locally free of finite type with pointwise rank `r`, the **top**
exterior power `⋀^r E` is a line bundle: locally free, of finite type, of pointwise rank `1`. (This is
the case `n = r` of `ExteriorPowerLocallyFree`; `VectorBundle.det` uses only this case.)

Proof:
1. On a frame neighbourhood `U` of `x` take `E|_U ≅ O_U^{⊕I}`; finite type makes `I` finite and the
   pointwise rank gives `|I| = r`; reindex by `ULift (Fin r)`.
2. `(⋀^r E)|_U ≅ ⋀^r(E|_U)` (`moduleExteriorPowerRestrictIso`) `≅ ⋀^r(O_U^r)` (`moduleExteriorIso`)
   `≅ O_U` (`moduleExteriorPowerFiniteFreeIso`), so `⋀^r E` is `IsLineBundle`, hence locally free of
   finite type.
3. Pointwise rank: the same trivialization followed by `moduleFreeOneIsoUnit`, then
   `rankAtStalk_of_restrict_iso_free` with `|ULift (Fin 1)| = 1`.

Source: Stacks Project, `modules.tex`; `det T_X` in the paper.
-/


set_option autoImplicit false
universe u
open CategoryTheory
noncomputable section

/-- A locally free module of finite type and pointwise rank `r` has, near every point, a frame indexed
by `ULift (Fin r)` (on the scheme, no base field needed). -/
theorem AlgebraicGeometry.Scheme.Modules.exists_restrict_iso_free_fin
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) (r : ℕ)
    [E.IsLocallyFree] [E.IsFiniteType]
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = r) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty (E.restrict U.ι ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  obtain ⟨U, I, hxU, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree E x
  have hfinite : Finite I :=
    AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free E U I e x hxU
  let _ : Fintype I := Fintype.ofFinite I
  have hrank := AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free E U I e x hxU
  have hcard : Fintype.card I = Fintype.card (ULift.{u} (Fin r)) := by
    rw [Fintype.card_ulift, Fintype.card_fin]
    exact hrank.symm.trans (hr x)
  exact ⟨U, hxU, ⟨(AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app E ≪≫ e ≪≫
    (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso
      (Fintype.equivOfCardEq hcard).toIso⟩⟩

/-- Trivialization of the top exterior power on a frame neighbourhood: `(⋀^r E)|_U ≅ O_U`. -/
theorem AlgebraicGeometry.Scheme.Modules.exteriorPower_top_restrict_iso_unit
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) (r : ℕ)
    [E.IsLocallyFree] [E.IsFiniteType]
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = r) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.exteriorPower E r).restrict U.ι ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨U, hxU, ⟨e'⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_restrict_iso_free_fin E r hr x
  exact ⟨U, hxU,
    ⟨MiyaokaMori.ExteriorPowerRestrictionIso.moduleExteriorPowerRestrictIso X U E r ≪≫
      AlgebraicGeometry.Scheme.Modules.moduleExteriorIso U.toScheme r e' ≪≫
      MiyaokaMori.ExteriorPowerFiniteFree.moduleExteriorPowerFiniteFreeIso U.toScheme r⟩⟩

theorem AlgebraicGeometry.Scheme.Modules.exteriorPower_top_isLineBundle
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) (r : ℕ)
    [E.IsLocallyFree] [E.IsFiniteType]
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = r) :
    (AlgebraicGeometry.Scheme.Modules.exteriorPower E r).IsLineBundle :=
  ⟨fun x => AlgebraicGeometry.Scheme.Modules.exteriorPower_top_restrict_iso_unit E r hr x⟩

theorem AlgebraicGeometry.Scheme.Modules.exteriorPower_top_isLocallyFree
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) (r : ℕ)
    (hE : E.IsLocallyFree) (hfin : E.IsFiniteType)
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = r) :
    (AlgebraicGeometry.Scheme.Modules.exteriorPower E r).IsLocallyFree ∧
      (AlgebraicGeometry.Scheme.Modules.exteriorPower E r).IsFiniteType ∧
      ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (AlgebraicGeometry.Scheme.Modules.exteriorPower E r) x = 1 := by
  have := hE; have := hfin
  have := AlgebraicGeometry.Scheme.Modules.exteriorPower_top_isLineBundle E r hr
  refine ⟨SheafOfModules.IsLineBundle.isLocallyFree _, SheafOfModules.IsLineBundle.isFiniteType _,
    fun x => ?_⟩
  obtain ⟨U, hxU, ⟨t⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exteriorPower_top_restrict_iso_unit E r hr x
  have h := AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
    (AlgebraicGeometry.Scheme.Modules.exteriorPower E r) U (ULift.{u} (Fin 1))
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫ t ≪≫
      (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).symm) x hxU
  simpa using h

end
