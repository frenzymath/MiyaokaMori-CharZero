import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFreeSheafFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaTotalSpaceIsoPullbackDual
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedTautologicalSectionFrame
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentPullbackIso
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.TotLinePunctured
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates

/-! # The Euler section trivializes the relative tangent sheaf of the punctured total space

The relative tangent sheaf of the punctured total space `Tot(V)^× → B` of a line bundle is
trivialized by the Euler vector field: the derivative at `λ = 1` of the fibrewise scalar
`G_m`-action is a nowhere-vanishing global section of `T_{Tot(V)^×/B}`, giving
`O ≅ T_{Tot(V)^×/B}`. The paper uses this to trivialize the first term of the tangent sequence
(with `B = C ×_k X`, `V = pr_1^*A ⊗ pr_2^*O_X(-1)`).

Route. Write `T := Tot(V) = Spec_B Sym(V^∨)`, `p : T → B`, `P := Tot(V)^× ⊆ T`, `π := P.ι ≫ p`.
* `Ω_{T/B} ≅ p^*(V^∨)` (`Omega_totalSpace_iso_pullback_dual`): the differentials of the total
  space are the pulled-back linear forms (`d` of the coordinate).
* `Ω_{P/B} ≅ P.ι^* Ω_{T/B}` (Stacks 01US, `Omega.pullbackIsoOfIsOpenImmersion`), so
  `Ω_{P/B} ≅ π^*(V^∨) ≅ (π^*V)^∨` (`dual_pullback`).
* On `P` the tautological section of `π^*V` is nowhere zero, hence a global frame: `O_P ≅ π^*V`
  (`totalSpacePunctured.unit_iso_pullback`). This is the intrinsic form of "the Euler section is
  nowhere zero": under `Ω_{P/B} ≅ (π^*V)^∨` the generator `dt/t` of `Ω_{P/B}` is the dual of the
  tautological section, and the Euler field `t ∂_t` is its dual.
* Hence `Ω_{P/B} ≅ O_P^∨ ≅ O_P` (`dual_unit_iso`) and `T_{P/B} = Ω_{P/B}^∨ ≅ O_P^∨ ≅ O_P`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `O_X^∨ ≅ O_X`: through `O_X ≅ O_X^{⊕ 1}` (`moduleFreeOneIsoUnit`) and `dual_free_iso 1`. -/
theorem AlgebraicGeometry.Scheme.Modules.dual_unit_iso (X : AlgebraicGeometry.Scheme.{u}) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.Modules.dual_free_iso (X := X) 1
  exact ⟨AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit X) ≪≫
    d ≪≫ AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit X⟩

/-- `Ω_{Tot(V)^×/B} ≅ O`: `Ω_{P/B} ≅ P.ι^*Ω_{T/B} ≅ π^*(V^∨) ≅ (π^*V)^∨ ≅ O_P^∨ ≅ O_P`
(see the module docstring). -/
theorem AlgebraicGeometry.Omega_totalSpacePunctured_iso_unit {B : AlgebraicGeometry.Scheme.{u}}
    (V : B.Modules) [V.IsLineBundle] :
    Nonempty (AlgebraicGeometry.Omega
        ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom) ≅
      SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpacePunctured V).toScheme.ringCatSheaf) := by
  obtain ⟨c⟩ := AlgebraicGeometry.Omega_totalSpace_iso_pullback_dual V
  obtain ⟨dp⟩ := AlgebraicGeometry.Scheme.Modules.dual_pullback
    ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom) V
  obtain ⟨fr⟩ := AlgebraicGeometry.Scheme.totalSpacePunctured.unit_iso_pullback V
  obtain ⟨du⟩ := AlgebraicGeometry.Scheme.Modules.dual_unit_iso
    (AlgebraicGeometry.Scheme.totalSpacePunctured V).toScheme
  refine ⟨(AlgebraicGeometry.Omega.pullbackIsoOfIsOpenImmersion
      (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι (AlgebraicGeometry.Scheme.totalSpace V).hom).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι).mapIso c ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
      (AlgebraicGeometry.Scheme.totalSpace V).hom).app (AlgebraicGeometry.Scheme.Modules.dual V) ≪≫
    dp.symm ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso ?_ ≪≫ du⟩
  exact fr

theorem eulerVectorField_trivializes_punctured {B : AlgebraicGeometry.Scheme.{u}} (V : B.Modules)
    [V.IsLineBundle] :
    Nonempty (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpacePunctured V).toScheme.ringCatSheaf ≅
      AlgebraicGeometry.relativeTangent
        ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom)) := by
  obtain ⟨e⟩ := AlgebraicGeometry.Omega_totalSpacePunctured_iso_unit V
  obtain ⟨du⟩ := AlgebraicGeometry.Scheme.Modules.dual_unit_iso
    (AlgebraicGeometry.Scheme.totalSpacePunctured V).toScheme
  exact ⟨du.symm ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso e⟩

end
