import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMulEvaluationLocal
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoEvaluationUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowIsoSection

/-! # The right unit law of `twistMul`, for an abstract unit section

For a graded quasi-coherent algebra `S` on `X` with relative Proj `π : Proj_X S → X`, and a morphism
`u : 𝟙_ ⟶ O(0)` whose value on `1` over every `π⁻¹U` (`U ⊆ X` affine) is the local evaluation of the unit
`S.one.app U 1 ∈ Γ(U, S_0)` (this is the property of `twistUnitSection S`, `twistUnitSection_app_one`), the
composite `O(a) ⊗ 𝟙_ --(𝟙 ⊗ u)--> O(a) ⊗ O(0) --twistMul--> O(a)` is the right unitor, up to the index transport
`a + 0 = a` (Stacks 01MO: the multiplication maps `O(a) ⊗ O(b) → O(a+b)` are compatible with the unit).

**Route (through the chart projections, without unfolding `twistMul`)**:
1. `twistπ_app_unit_val`: over `V ≤ π⁻¹U`, the chart projection `twistπ 0 U` (Stacks 01LI) sends `u.app V 1` to
   the constant function `1`: `u.app V 1` is the restriction of `u.app (π⁻¹U) 1 = evaluationLocal S 0 U (S.one 1)`,
   whose chart value is `(sectionsOf U 0 (S.one 1))/1 = 1/1 = 1` (`twistπ_app_evaluationLocal_val`,
   `sectionsOf_one_app_one`, `Localization.mk_one`).
2. `twistMul_app_moduleTensorSection_unit_of_le`: over `V ≤ π⁻¹U`, `twistMul S a 0 (s ⊗ u(1)) = eqToHom s`: `twistπ (a+0) U`
   is injective on sections over `V` (`twistπ_app_injective`), commutes with `eqToHom` (`twistπ_app_eqToHom_app`,
   `eqToHom_pushforward_twist_app_val`) and turns `twistMul` into the pointwise product (`twistπ_app_twistMul_app_val`);
   pointwise the claim is `x · 1 = x`.
3. `twistMul_app_moduleTensorSection_unit`: the same over every open `V`, by the sheaf property of `O(a+0)` along the
   cover `{V ⊓ π⁻¹U}` (`TopCat.Sheaf.eq_of_locally_eq'`), restrictions commuting with `Hom.app`, `moduleTensorSection`
   and `1`.
4. `twistMul_unit_right_of_app_one`: the morphism-level statement, by cancelling `(ρ_ O(a)).inv` and checking on
   sections: `(ρ_).inv s = s ⊗ 1` (`rightUnitor_inv_app_eq_tensorSections`), `(O(a) ◁ u)(s ⊗ 1) = s ⊗ u(1)`
   (`whiskerLeft_app_tensorSections`), `tensorIsoTensorObj.inv` turns `tensorSections` into `moduleTensorSection`.

Sources: Stacks 01MO, 01LI, 01NR; the proof of Proposition 2.4 of the paper. Used by `twistMul_unit_right`
(`TwistPullbackPowCore`), which instantiates `u := twistUnitSection S`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- Restriction of `1` in the monoidal unit `𝟙_ Y.Modules` (a ring homomorphism on the structure sheaf). -/
theorem unitObj_presheaf_map_one {Y : AlgebraicGeometry.Scheme.{u}} {W' W : Y.Opens} (h : W' ≤ W) :
    (𝟙_ Y.Modules).presheaf.map (homOfLE h).op (1 : Γ(Y, W)) = (1 : Γ(Y, W')) :=
  map_one (Y.presheaf.map (homOfLE h).op).hom

/-- **Step 1.** Over `V ≤ π⁻¹U`, the chart projection `twistπ 0 U` sends the unit section `u.app V 1` to the
constant function `1` on the chart (`u` is any morphism `𝟙_ ⟶ O(0)` whose value on `1` over `π⁻¹U` is the local
evaluation of `S.one.app U 1`). -/
theorem twistπ_app_unit_val (u : 𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S 0) (U : X.affineOpens)
    (hu : u.app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
        (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S 0 U (S.one.app U.1 (1 : Γ(X, U.1))))
    (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (hV : V ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
    (p : (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V :
      (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U))).Opens)) :
    Subtype.val ((S.toGradedAffineAlgebra.twistπ 0 (AlgebraicGeometry.Scheme.affineSite U)).app V
        (u.app V (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, V))) :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) 0
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V)) p = 1 := by
  -- `u.app V 1` is the restriction of `u.app (π⁻¹U) 1`
  have h1 : u.app V (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, V)) =
      (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE hV).op
        (u.app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
          (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1))) :=
    ((AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map u hV _).trans
      (congrArg (u.app V) (unitObj_presheaf_map_one hV))).symm
  -- `twistπ` commutes with restriction
  have h2 : (S.toGradedAffineAlgebra.twistπ 0 (AlgebraicGeometry.Scheme.affineSite U)).app V
      ((AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE hV).op
        (u.app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
          (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)))) =
      ((AlgebraicGeometry.Scheme.Modules.pushforward
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U))).obj
        (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) 0)).presheaf.map
        (homOfLE hV).op
        ((S.toGradedAffineAlgebra.twistπ 0 (AlgebraicGeometry.Scheme.affineSite U)).app
          ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
          (u.app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
            (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)))) :=
    (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map
      (S.toGradedAffineAlgebra.twistπ 0 (AlgebraicGeometry.Scheme.affineSite U)) hV _).symm
  refine (congrArg (fun z => Subtype.val
    ((S.toGradedAffineAlgebra.twistπ 0 (AlgebraicGeometry.Scheme.affineSite U)).app V z :
      MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
        (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) 0
        (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V)) p) h1).trans ?_
  refine (congrArg (fun z => Subtype.val (z :
      MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
        (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) 0
        (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V)) p) h2).trans ?_
  -- the restricted chart section, evaluated at `p`, is the original section at `p`
  refine (pushforward_twist_map_val S (AlgebraicGeometry.Scheme.affineSite U) 0 hV _ p).trans ?_
  refine (congrArg (fun z => Subtype.val
    ((S.toGradedAffineAlgebra.twistπ 0 (AlgebraicGeometry.Scheme.affineSite U)).app
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) z :
      MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
        (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) 0
        (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)))
    ⟨p.1, (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U)).preimage_mono hV p.2⟩) hu).trans ?_
  refine (twistπ_app_evaluationLocal_val S 0 U (S.one.app U.1 (1 : Γ(X, U.1))) _).trans ?_
  exact (congrArg (fun z => Localization.mk z 1) (sectionsOf_one_app_one S U.1)).trans Localization.mk_one

/-- **Step 2.** Over `V ≤ π⁻¹U`, `twistMul S a 0 (s ⊗ u(1)) = s` (up to the index transport `a = a + 0`). -/
theorem twistMul_app_moduleTensorSection_unit_of_le (a : ℤ)
    (u : 𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S 0) (U : X.affineOpens)
    (hu : u.app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
        (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S 0 U (S.one.app U.1 (1 : Γ(X, U.1))))
    (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (hV : V ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
    (s : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, V)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0).app V
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s (u.app V (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, V)))) =
      (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_zero a).symm)).app V s := by
  apply twistπ_app_injective S (a + 0) U V hV
  rw [twistπ_app_eqToHom_app S (AlgebraicGeometry.Scheme.affineSite U) (add_zero a).symm]
  refine Subtype.ext (funext fun p => ?_)
  have h1 := twistπ_app_twistMul_app_val S a 0 U V hV s
    (u.app V (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, V))) p
  have h2 := twistπ_app_unit_val S u U hu V hV p
  have h3 := eqToHom_pushforward_twist_app_val S (AlgebraicGeometry.Scheme.affineSite U) (add_zero a).symm V
    ((S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app V s) p
  exact h1.trans ((congrArg (_ * ·) h2).trans ((mul_one _).trans h3.symm))

/-- **Step 3.** Over every open `V`, `twistMul S a 0 (s ⊗ u(1)) = s` (up to the index transport `a = a + 0`); by
the sheaf property of `O(a+0)` along the cover `{V ⊓ π⁻¹U : U affine}`. -/
theorem twistMul_app_moduleTensorSection_unit (a : ℤ)
    (u : 𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S 0)
    (hu : ∀ U : X.affineOpens, u.app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
        (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S 0 U (S.one.app U.1 (1 : Γ(X, U.1))))
    (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (s : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, V)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0).app V
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s (u.app V (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, V)))) =
      (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_zero a).symm)).app V s := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨(AlgebraicGeometry.Scheme.relativeProj.twist S (a + 0)).presheaf,
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a + 0)).isSheaf⟩
    (fun U : X.affineOpens => V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) V
    (fun U => CategoryTheory.homOfLE inf_le_left) ?_ _ _ ?_
  · intro p hp
    have hp' : (AlgebraicGeometry.Scheme.relativeProj S).hom.base p ∈ (⊤ : X.Opens) := trivial
    rw [← AlgebraicGeometry.iSup_affineOpens_eq_top X] at hp'
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hp'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hp, hU⟩
  · intro U
    have h : V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1 ≤ V := inf_le_left
    change (AlgebraicGeometry.Scheme.relativeProj.twist S (a + 0)).presheaf.map (CategoryTheory.homOfLE h).op _ =
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a + 0)).presheaf.map (CategoryTheory.homOfLE h).op _
    have hL : (AlgebraicGeometry.Scheme.relativeProj.twist S (a + 0)).presheaf.map (CategoryTheory.homOfLE h).op
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0).app V
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s (u.app V (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, V))))) =
        (AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0).app
          (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
            ((AlgebraicGeometry.Scheme.relativeProj.twist S a).presheaf.map (CategoryTheory.homOfLE h).op s)
            (u.app (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
              (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left,
                V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)))) := by
      refine (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ h _).trans ?_
      refine congrArg _ ((AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (CategoryTheory.homOfLE h) _ _).trans ?_)
      refine congrArg (fun t => AlgebraicGeometry.Scheme.Modules.moduleTensorSection
        ((AlgebraicGeometry.Scheme.relativeProj.twist S a).presheaf.map (CategoryTheory.homOfLE h).op s) t) ?_
      refine (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map u h _).trans ?_
      exact congrArg (u.app _) (unitObj_presheaf_map_one h)
    have hR : (AlgebraicGeometry.Scheme.relativeProj.twist S (a + 0)).presheaf.map (CategoryTheory.homOfLE h).op
        ((CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_zero a).symm)).app V s) =
        (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_zero a).symm)).app
          (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
          ((AlgebraicGeometry.Scheme.relativeProj.twist S a).presheaf.map (CategoryTheory.homOfLE h).op s) :=
      AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ h _
    rw [hL, hR]
    exact twistMul_app_moduleTensorSection_unit_of_le S a u U (hu U) _ inf_le_right _

/-- **Step 4: the right unit law of `twistMul`, for an abstract unit section** `u : 𝟙_ ⟶ O(0)` whose value on `1`
over each `π⁻¹U` (`U` affine) is the local evaluation of `S.one.app U 1` (Stacks 01MO). -/
theorem twistMul_unit_right_of_app_one (a : ℤ)
    (u : 𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S 0)
    (hu : ∀ U : X.affineOpens, u.app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
        (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S 0 U (S.one.app U.1 (1 : Γ(X, U.1)))) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S a ◁ u) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.relativeProj.twist S a)
          (AlgebraicGeometry.Scheme.relativeProj.twist S 0)).inv ≫
        AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0 =
      (ρ_ (AlgebraicGeometry.Scheme.relativeProj.twist S a)).hom ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_zero a).symm) := by
  rw [← CategoryTheory.Iso.cancel_iso_inv_left (ρ_ (AlgebraicGeometry.Scheme.relativeProj.twist S a)),
    CategoryTheory.Iso.inv_hom_id_assoc]
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro V
  ext s
  change (AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0).app V
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app V
      ((AlgebraicGeometry.Scheme.relativeProj.twist S a ◁ u).app V
        ((ρ_ (AlgebraicGeometry.Scheme.relativeProj.twist S a)).inv.app V s))) =
    (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_zero a).symm)).app V s
  have e1 := AlgebraicGeometry.Scheme.Modules.rightUnitor_inv_app_eq_tensorSections
    (AlgebraicGeometry.Scheme.relativeProj.twist S a) V s
  have e2 := AlgebraicGeometry.Scheme.Modules.whiskerLeft_app_tensorSections
    (AlgebraicGeometry.Scheme.relativeProj.twist S a) u V s
    (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, V))
  have e3 := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_app_tensorSections
    (AlgebraicGeometry.Scheme.relativeProj.twist S a) (AlgebraicGeometry.Scheme.relativeProj.twist S 0) V s
    (u.app V (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, V)))
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0).app V
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app V
      ((AlgebraicGeometry.Scheme.relativeProj.twist S a ◁ u).app V z))) e1).trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0).app V
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app V z)) e2).trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0).app V z) e3).trans ?_
  exact twistMul_app_moduleTensorSection_unit S a u hu V s

end AlgebraicGeometry.Scheme.relativeProj

end
