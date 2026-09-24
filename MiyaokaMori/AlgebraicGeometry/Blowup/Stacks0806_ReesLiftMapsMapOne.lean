import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupReesLiftMaps

/-! # The `map_one` field of the Rees lift data

The `map_one` field of the Rees lift data: graded maps `Ψ_n : f^*(Iⁿ) ⟶ J^{⊗n}` with `Ψ_n ≫ μ_n = θ_n`
automatically satisfy `f^*(O_X = I⁰) ≫ Ψ_0 = (f^*O_X ≅ O_Y)`.

Source: Stacks 01O4 (the degree-`0` condition on a graded map into `⊕ L^{⊗n}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- **Degree `0` of the Rees lift data.** If `Ψ_n ≫ μ_n = θ_n` for all `n`, then
`f^*(reesAlgebra.one) ≫ Ψ_0 = (pullbackUnitIso f).hom` (the `map_one` field of `relativeProj.LiftData`).

Proof. `μ_0 = ε_Y := monoidalUnitIso Y` (`monoidalPowToUnit_zero`), an isomorphism, so it suffices to compare after
composing with it. `f^*(powOne) ≫ Ψ_0 ≫ ε_Y = f^*(powOne) ≫ θ_0 = f^*(powOne ≫ powι 0) ≫ pb = f^*(ε_X) ≫ pb`
(`liftPow_powι`, `rfl`), with `pb := (pullbackUnitIso f).hom`. Both `ε_X` and `ε_Y` are `eqToHom`s of the
definitional equality `𝟙_ = SheafOfModules.unit`, so `f^*(ε_X) ≫ pb = pb ≫ ε_Y` (`eqToHom_map`, then both
`eqToHom`s are identities after unfolding: `with_unfolding_all rfl`). Because the statement mixes `𝟙_` and
`SheafOfModules.unit`, `rw` on the goal fails its motive check; the proof is written as an `Eq.trans` chain
(cf. section `ZeroDegree` of `RelativeProjLiftData`). -/
theorem AlgebraicGeometry.Scheme.blowup_reesLiftMaps_map_one {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (Ψ : ∀ n : ℕ, (AlgebraicGeometry.Scheme.Modules.pullback f).obj (I.reesAlgebra.part n) ⟶
        AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules n)
    (hΨ : ∀ n : ℕ, Ψ n ≫ (I.comap f).monoidalPowToUnit n = I.reesPullbackToUnit f n) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map I.reesAlgebra.one ≫ Ψ 0 =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom := by
  have h0 := hΨ 0
  rw [AlgebraicGeometry.Scheme.IdealSheafData.monoidalPowToUnit_zero] at h0
  have hΨ0 : Ψ 0 = I.reesPullbackToUnit f 0 ≫
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv :=
    (Iso.eq_comp_inv _).mpr h0
  refine (congrArg (fun k => (AlgebraicGeometry.Scheme.Modules.pullback f).map I.reesAlgebra.one ≫ k)
    hΨ0).trans ?_
  refine (Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).mpr ?_)
  unfold AlgebraicGeometry.Scheme.IdealSheafData.reesPullbackToUnit
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom)
    (Functor.map_comp _ _ _).symm).trans ?_
  show (AlgebraicGeometry.Scheme.Modules.pullback f).map
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).hom ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom =
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom ≫
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso, eqToIso.hom, eqToHom_map]
  with_unfolding_all rfl

end
