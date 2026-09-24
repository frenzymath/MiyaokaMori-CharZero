import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.TangentBundle
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeAdditiveFiltration

/-! # Positive degree of `f^*T_X` forces `dim X ≥ 1`

Statement: if `deg f^*T_X ≠ 0` (in particular if `deg f^*T_X > 0`, the hypothesis of the main
theorem), then `dim X ≥ 1`.

Source: §2 of the paper ("`n = dim X ≥ 1`": if `X` were a point, `T_X = 0` and
`deg f^*T_X = 0`); `n ≥ 1` is used silently through `θ = d h_κ/(2(n+1)κ)` and `s_κ = (n+1)κ`.

Natural-language proof: the rank of `T_X` is `dim X` (`tangentBundle_rank`) and pullback preserves the
rank (`VectorBundle.pullback` has `rank := E.rank`). If `dim X = 0` then `f^*T_X` has rank `0`, its
top exterior power `Λ^0` is the structure sheaf, whose degree is `0` (`LineBundle.degree_one`), so
`deg f^*T_X = 0` (`VectorBundle.degree_spec` + uniqueness of the curve-module degree). ∎ -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

local instance {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- `Λ^0 M ≅ O` at the presheaf level (copy of the private `exteriorZeroPresheafIso` of
`Paper/S2WeightedJets/DegreeAdditiveFiltration.lean`). -/
private def exteriorZeroPresheafIso' {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf X M.val 0 ≅
      (SheafOfModules.unit X.ringCatSheaf).val :=
  PresheafOfModules.isoMk
    (fun U => ModuleCat.exteriorPower.iso₀ (M.val.obj U)) (by
    intro U V i
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    change (ModuleCat.exteriorPower.iso₀ (M.val.obj V)).hom.hom
        (AlgebraicGeometry.Scheme.Modules.exteriorRestriction X M.val 0 i
          (ModuleCat.exteriorPower.mk v)) =
      ((SheafOfModules.unit X.ringCatSheaf).val.map i)
        ((ModuleCat.exteriorPower.iso₀ (M.val.obj U)).hom.hom
          (ModuleCat.exteriorPower.mk v))
    rw [AlgebraicGeometry.Scheme.Modules.exteriorRestriction_mk,
      ModuleCat.exteriorPower.iso₀_hom_apply,
      ModuleCat.exteriorPower.iso₀_hom_apply]
    exact (PresheafOfModules.unit_map_one X.ringCatSheaf.val i).symm)

/-- `Λ^0 M ≅ O` as sheaves of modules. -/
private def exteriorZeroIso' {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X M 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (exteriorZeroPresheafIso' M) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit X.ringCatSheaf)

/-- A vector bundle of rank `0` on a curve has degree `0` (its `Λ^0` is `O`, of degree `0`). Public
version of the private `vectorBundle_degree_zero_of_rank_zero` in `DegreeAdditiveFiltration.lean`. -/
theorem VectorBundle.degree_eq_zero_of_rank_eq_zero {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = 0) :
    VectorBundle.degree E = 0 := by
  rw [VectorBundle.degree_eq_lineBundle_degree_det, ← LineBundle.degree_one C]
  apply LineBundle.degree_congr
  dsimp only [AlgebraicGeometry.VectorBundle.det]
  rw [LineBundle.one_toModules]
  exact eqToIso (by rw [hE]) ≪≫ exteriorZeroIso' E.toModules

/-- `deg f^*T_X ≠ 0 ⇒ dim X ≥ 1` (§2 of the paper). -/
theorem SmoothProjectiveVariety.one_le_dim_of_pullbackDegree_ne_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) (hd : TangentBundle.pullbackDegree f ≠ 0) :
    1 ≤ X.toVariety.dim := by
  by_contra h
  apply hd
  have h0 : X.toVariety.dim = 0 := by omega
  apply VectorBundle.degree_eq_zero_of_rank_eq_zero
  change (tangentBundle X).rank = 0
  rw [tangentBundle_rank, h0]

end
