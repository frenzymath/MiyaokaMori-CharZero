import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeGlue
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjBaseChangeTwistCone
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjBaseChangeTwistLocalIso
import MiyaokaMori.AlgebraicGeometry.Morphisms.ModulesGlueOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC

/-! # Base change of the twisting sheaf of a relative Proj

Statement: **Stacks 01O3, second assertion** (the map `θ`): pulling back the twisting sheaf
`O_{Proj_S 𝒜}(d)` along the comparison map `baseChangeHom g 𝒜 : Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)`
(`RelativeProjBaseChangeGlue`) gives the twisting sheaf `O_{Proj_{S'}(g^*𝒜)}(d)`.

Route: glue the local comparison maps `ψ_i` of
`RelativeProjBaseChangeTwistCone` along the small-chart cover with
`Modules.exists_hom_of_restrict_compat` (Stacks 04TN);
the glued morphism is an isomorphism because each `ψ_i` is
(`RelativeProjBaseChangeTwistLocalIso`) and isomorphisms of modules are local
(`Modules.isIso_of_restrict_isIso_cover`). The local directedness of the small-chart cover is
`baseChangeChart_directed`, transported to points with
Mathlib `Scheme.Pullback.exists_preimage_pullback`.

Source: Stacks 01O3, 01N2 (last sentence), 01LI, 04TN; Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) (𝒜 : S.GradedQCAlgebra)

/-- The small charts cover `Proj_{S'}(g^*𝒜)` (`baseChangeChart_covers`, in terms of `opensRange`). -/
theorem exists_mem_projChart_opensRange (x : (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).left) :
    ∃ i : BaseChangeChartIndex g,
      x ∈ ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2).opensRange := by
  obtain ⟨i, y, hy⟩ := baseChangeChart_covers g 𝒜 x
  exact ⟨i, y, hy⟩

/-- Local directedness of the small-chart cover at the level of points: two charts containing `x`
are refined near `x` by a common smaller chart, through the transition maps
(`baseChangeChart_directed` + `Scheme.Pullback.exists_preimage_pullback`). -/
theorem baseChangeChart_directed_point {i j : BaseChangeChartIndex g}
    (x : (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).left)
    (hi : x ∈ ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2).opensRange)
    (hj : x ∈ ((𝒜.pullback g).toGradedAffineAlgebra.projChart j.1.2).opensRange) :
    ∃ (k : BaseChangeChartIndex g) (hki : k ⟶ i) (hkj : k ⟶ j),
      baseChangeChartTrans g 𝒜 hki ≫ (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 =
          (𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2 ∧
      baseChangeChartTrans g 𝒜 hkj ≫ (𝒜.pullback g).toGradedAffineAlgebra.projChart j.1.2 =
          (𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2 ∧
      x ∈ ((𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2).opensRange := by
  obtain ⟨p, hp⟩ := hi
  obtain ⟨q, hq⟩ := hj
  have hp' : (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 p = x := hp
  have hq' : (𝒜.pullback g).toGradedAffineAlgebra.projChart j.1.2 q = x := hq
  obtain ⟨z, hz1, hz2⟩ :=
    AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback p q (hp'.trans hq'.symm)
  obtain ⟨k, hki, hkj, y, hy⟩ := baseChangeChart_directed g 𝒜 z
  have e1 := AlgebraicGeometry.Scheme.Hom.comp_apply
    (pullback.lift (baseChangeChartTrans g 𝒜 hki) (baseChangeChartTrans g 𝒜 hkj)
      ((baseChangeChartTrans_f g 𝒜 hki).trans (baseChangeChartTrans_f g 𝒜 hkj).symm))
    (pullback.fst ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2) ((𝒜.pullback g).toGradedAffineAlgebra.projChart j.1.2)) y
  erw [pullback.lift_fst] at e1
  have e2 : (baseChangeChartTrans g 𝒜 hki ≫ (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2) y =
      (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 (baseChangeChartTrans g 𝒜 hki y) :=
    AlgebraicGeometry.Scheme.Hom.comp_apply _ _ y
  have e2' : (baseChangeChartTrans g 𝒜 hki ≫ (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2) y = (𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2 y :=
    congrArg (fun f => f y) (baseChangeChartTrans_f g 𝒜 hki)
  have e3 : (𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2 y = x := by
    rw [← e2', e2, ← hp', ← hz1, ← hy]
    erw [← e1]
  exact ⟨k, hki, hkj, baseChangeChartTrans_f g 𝒜 hki, baseChangeChartTrans_f g 𝒜 hkj, y, e3⟩

/-- **Stacks 01O3 (θ)**: `(baseChangeHom g 𝒜)^* O_{Proj_S 𝒜}(d) ≅ O_{Proj_{S'}(g^*𝒜)}(d)`.

Source: Stacks 01O3 (last paragraph), 01N2 (last sentence, via 01MX), 01LI (uniqueness of glued
sheaves), 04TN (gluing morphisms of sheaves).

Proof. Let `φ = baseChangeHom g 𝒜` (spelled `baseChangeHom'`), `T = O_{Proj_S 𝒜}(d)`, `T' = O_{Proj_{S'}(g^*𝒜)}(d)`.
(1) **Local comparison maps.** For every small chart `i = (U, V)` (`BaseChangeChartIndex g`, with
chart `ι'_V : Proj (g^*𝒜)(V) ⟶ Proj_{S'}(g^*𝒜)`) the map `c_i = twistπ d U ≫ twistPushTransition ψ_i :
T ⟶ (ι'_V ≫ φ)_* O_V(d)` (Stacks 01MX, legitimate since `ι'_V ≫ φ = ψ_i ≫ ι_U`) has adjoint transposes
`χ_i^♯ : φ^* T ⟶ (ι'_V)_* O_V(d)` and `σ_i : (φ^* T)|_V ⟶ O_V(d)`; with `τ_V : T'|_V ≅ O_V(d)` the
transpose of `twistπ d V` (an isomorphism by Stacks 01LI) put `ψ_i = σ_i ≫ τ_V⁻¹ : (φ^* T)|_V ⟶ T'|_V`
(`RelativeProjBaseChangeTwistCone`).
(2) **Local isomorphisms.** `σ_i` is, through the uniqueness of left adjoints,
`(pullback ψ_i).map τ_U ≫ twistPullbackHom ψ_i`, an isomorphism by 01LI for `U` and 01N2
(`isIso_baseChangeProjMap_twistPullbackHom`); hence `ψ_i` is an isomorphism
(`RelativeProjBaseChangeTwistLocalIso`).
(3) **Compatibility.** For `k ≤ i` the `ψ` agree after restriction along the transition map
`Proj (g^*𝒜)(V_k) ⟶ Proj (g^*𝒜)(V_i)`: Stacks 01NP (`twistPushTransition_comp`), `twistπ_transition`,
and the unit commutes with restriction (`restrictGraded_comp_baseChangeUnitGraded`).
(4) **Gluing.** The small charts cover `Proj_{S'}(g^*𝒜)` and the cover is locally directed
(`baseChangeChart_directed`), so the `ψ_i` glue to `Φ : φ^* T ⟶ T'` restricting to them
(`Modules.exists_hom_of_restrict_compat`, Stacks 04TN); `Φ` is an isomorphism since it is one on
each chart (`Modules.isIso_of_restrict_isIso_cover`, stalks). -/
theorem baseChangeHom_twist (d : ℤ) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (baseChangeHom g 𝒜)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 d) ≅
      AlgebraicGeometry.Scheme.relativeProj.twist (𝒜.pullback g) d) := by
  obtain ⟨Φ, hΦ⟩ := AlgebraicGeometry.Scheme.Modules.exists_hom_of_restrict_compat
    (fun i : BaseChangeChartIndex g =>
      AlgebraicGeometry.Proj ((𝒜.pullback g).toGradedAffineAlgebra.grading i.1.2))
    (fun i => (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2)
    (exists_mem_projChart_opensRange g 𝒜)
    (fun i k t => ∃ hki : k ⟶ i, t = (Proj.map ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V (leOfHom hki))) ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V (leOfHom hki)))))
    (fun i j x hi hj => by
      obtain ⟨k, hki, hkj, -, -, hx⟩ := baseChangeChart_directed_point g 𝒜 x hi hj
      exact ⟨k, _, _, (𝒜.pullback g).toGradedAffineAlgebra.map_projChart' (BaseChangeChartIndex.le_V (leOfHom hki)),
        (𝒜.pullback g).toGradedAffineAlgebra.map_projChart' (BaseChangeChartIndex.le_V (leOfHom hkj)), hx, ⟨hki, rfl⟩, ⟨hkj, rfl⟩⟩)
    _ _ (fun i => haveI := (𝒜.pullback g).toGradedAffineAlgebra.isIso_restrictTranspose_twistπ d i.1.2; bcPsi[g, 𝒜, d, i])
    (fun i k t _ hg h => by
      obtain ⟨hki, rfl⟩ := hg
      exact twistBaseChangePsi_compat g 𝒜 d (leOfHom hki))
  haveI : IsIso Φ := AlgebraicGeometry.Scheme.Modules.isIso_of_restrict_isIso_cover
    (fun i : BaseChangeChartIndex g => AlgebraicGeometry.Proj ((𝒜.pullback g).toGradedAffineAlgebra.grading i.1.2))
    (fun i => (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2) (exists_mem_projChart_opensRange g 𝒜) Φ
    (fun i => by rw [hΦ i]; exact isIso_twistBaseChangePsi g 𝒜 d i)
  exact ⟨(asIso Φ : (AlgebraicGeometry.Scheme.Modules.pullback (baseChangeHom' g 𝒜)).obj
    (𝒜.toGradedAffineAlgebra.twist d) ≅ (𝒜.pullback g).toGradedAffineAlgebra.twist d)⟩

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
