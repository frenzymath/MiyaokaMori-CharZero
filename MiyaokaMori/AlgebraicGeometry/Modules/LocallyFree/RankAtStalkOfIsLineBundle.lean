import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # A line bundle has rank one at every stalk

A line bundle `M` on a scheme `X` (unpackaged: `M.IsLineBundle`, i.e. locally isomorphic to the
structure sheaf) has `rankAtStalk M x = 1` at every point; hence an unpackaged line bundle on a
variety `X` can be packaged as a `LineBundle X` (`LineBundle.ofIsLineBundle`), so that results
stated for packaged line bundles (such as `shortExact_of_regular_section`) apply to it.

Proof sketch:
1. Take an open neighbourhood `U` of `x` and a trivialization `M|_U ≅ O_U`
   (`IsLineBundle.locally_trivial`).
2. `O_U` is the free sheaf on a one-point index type: `free PUnit = ∐_{PUnit} O_U ≅ O_U`
   (`Limits.coproductUniqueIso`); restriction and pullback are canonically isomorphic
   (`Scheme.Modules.restrictFunctorIsoPullback`).
3. `rankAtStalk_of_restrict_iso_free` gives `rankAtStalk M x = #PUnit = 1`.
4. Packaging: `rank := 1`, locally free and finite type from the instances of `IsLineBundle`, the
   rank from step 3.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsLineBundle] (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk M x = 1 := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) x
  have h := AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free M U PUnit.{u + 1}
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e ≪≫
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit U.toScheme.ringCatSheaf)).symm) x hxU
  simpa using h

/-- Packaging an unpackaged line bundle on a variety as a `LineBundle` (the underlying module is
unchanged, `rank = 1`). -/
def LineBundle.ofIsLineBundle {k : Type u} [Field k] {X : Variety k}
    (M : X.carrier.Modules) [M.IsLineBundle] : LineBundle X where
  toModules := M
  rank := 1
  locallyFree := inferInstance
  isFiniteType := inferInstance
  rankAtStalk_eq := AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle M
  rank_eq_one := rfl

@[simp]
theorem LineBundle.ofIsLineBundle_toModules {k : Type u} [Field k] {X : Variety k}
    (M : X.carrier.Modules) [M.IsLineBundle] :
    (LineBundle.ofIsLineBundle M).toModules = M := rfl

end
