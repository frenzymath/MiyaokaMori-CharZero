import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestrictionIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankBridge
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerFiniteFreeIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerTopLocallyFree

/-! # Exterior powers of locally free modules are locally free

For an `O_X`-module `E` that is locally free of finite type with pointwise rank `r`, the exterior
power `⋀^n E` is again locally free of finite type with pointwise rank `C(r,n)`; in particular `⋀^r E`
is a line bundle (the determinant line bundle).

Source: Stacks 01CK (exterior powers preserve finite type and local freeness); `det T_X` and
`ω_X = ⋀^n Ω` in the paper.

Proof:
1. Every point `x` has an open neighbourhood `U` and a frame `E|_U ≅ O_U^{⊕ r}`
   (`exists_restrict_iso_free_fin`: local freeness gives a free frame, finite type makes the index set
   finite, pointwise rank `r` makes its cardinality `r`).
2. Exterior powers commute with restriction to opens: `(⋀^n E)|_U ≅ ⋀^n (E|_U)`
   (`moduleExteriorPowerRestrictIso`); along the frame `⋀^n (E|_U) ≅ ⋀^n (O_U^{⊕ r})`
   (`moduleExteriorIso`); finally `⋀^n (O_U^{⊕ r}) ≅ O_U^{⊕ C(r,n)}`
   (`moduleExteriorPowerFiniteFreeIsoGen`: Mathlib's basis `Module.Basis.exteriorPower` of the exterior
   power, indexed by the `n`-element subsets of `Fin r`, of cardinality `C(r,n)`; the wedge coordinates
   are minors of the coordinate matrix and are compatible with restriction).
3. So `⋀^n E` has local frames of rank `C(r,n)` at every point; `isLocallyFree_of_localFrames`,
   `isFiniteType_of_localFrames` and `rankAtStalk_eq_of_localFrames` give the three conclusions.

Edge cases: for `n > r`, `C(r,n) = 0` and `⋀^n E` is locally the zero sheaf (rank 0); for
`r = 0`, `n = 0`, `C(0,0) = 1` and `⋀^0 E ≅ O_X`; on the empty scheme everything is trivial. All are
covered by the same argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Local frames of the exterior power: on a neighbourhood `U` carrying a rank `r` frame of `E`,
`(⋀^n E)|_U ≅ O_U^{⊕ C(r,n)}`. -/
theorem AlgebraicGeometry.Scheme.Modules.exteriorPower_exists_restrict_iso_free
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) (r n : ℕ)
    [E.IsLocallyFree] [E.IsFiniteType]
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = r) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.exteriorPower E n).restrict U.ι ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (r.choose n)))) := by
  obtain ⟨U, hxU, ⟨e'⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_restrict_iso_free_fin E r hr x
  exact ⟨U, hxU,
    ⟨MiyaokaMori.ExteriorPowerRestrictionIso.moduleExteriorPowerRestrictIso X U E n ≪≫
      AlgebraicGeometry.Scheme.Modules.moduleExteriorIso U.toScheme n e' ≪≫
      MiyaokaMori.ExteriorPowerFiniteFree.moduleExteriorPowerFiniteFreeIsoGen U.toScheme r n⟩⟩

/-- The exterior power `⋀^n E` of a locally free module of finite type and pointwise rank `r` is
locally free of finite type with pointwise rank `C(r,n)`. -/
theorem AlgebraicGeometry.Scheme.Modules.exteriorPower_isLocallyFree {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (r n : ℕ) (hE : E.IsLocallyFree) (hfin : E.IsFiniteType)
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = r) :
    (AlgebraicGeometry.Scheme.Modules.exteriorPower E n).IsLocallyFree ∧
      (AlgebraicGeometry.Scheme.Modules.exteriorPower E n).IsFiniteType ∧
      ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (AlgebraicGeometry.Scheme.Modules.exteriorPower E n) x = r.choose n := by
  have := hE; have := hfin
  have h := AlgebraicGeometry.Scheme.Modules.exteriorPower_exists_restrict_iso_free E r n hr
  exact ⟨AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_localFrames _ _ h,
    AlgebraicGeometry.Scheme.Modules.isFiniteType_of_localFrames _ _ h,
    AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_of_localFrames _ _ h⟩

end
