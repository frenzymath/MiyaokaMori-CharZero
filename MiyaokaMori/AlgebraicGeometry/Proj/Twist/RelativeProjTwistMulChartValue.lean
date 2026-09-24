import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulLocalChart
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulChartSections

/-! # The chart projection `twistπ` is multiplicative

`twistπ_app_twistMul_app_val`: over `V ≤ π⁻¹U`, the chart projection `twistπ n U : O(n) ⟶ (c_U)_* O_U(n)`
(Stacks 01LI) turns the multiplication `twistMul S a b : O(a) ⊗ O(b) ⟶ O(a+b)` of the relative Proj into the pointwise
product of homogeneous fractions on the chart (Stacks 01MO). It combines `twistMulLocal_app_chart` (chart value of the
local multiplication), `tAH_rFIP_inv_app_val` (the 01NR comparison on sections is `twistπ`) and the pointwise lemmas of
`RelativeProjTwistMulPointwise`.

Source: Stacks 01MO, 01NR, 01LI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- `restrictSectionMap` applied to a section, unfolded (generic; `hr₂` may be any proof). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.restrictSectionMap_apply {X' : AlgebraicGeometry.Scheme.{u}}
    {M N : X'.Modules} {W : X'.Opens} (φ : M.restrict W.ι ⟶ N.restrict W.ι) (V : X'.Opens) (hV : V ≤ W)
    (hr₂ : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V) (s : Γ(M, V)) :
    AlgebraicGeometry.Scheme.Modules.restrictSectionMap φ V hV s =
      N.presheaf.map (homOfLE hr₂).op (φ.app (W.ι ⁻¹ᵁ V)
        (M.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op s)) := rfl

/-- **The chart projection is multiplicative on `V ≤ π⁻¹U`** (Stacks 01MO on the chart `Proj A(U)`, the heart of
the associativity of `twistMul` on sections): for `x ∈ Γ(O(a), V)`, `y ∈ Γ(O(b), V)` and a point `p` of `c_U⁻¹V`,

  `(twistπ (a+b) U (x·y))(p) = (twistπ a U x)(p) · (twistπ b U y)(p)`,

where `x·y := twistMul S a b (x ⊗ y)`. Proof: on `V ≤ π⁻¹U`, `twistMul` is the glued local multiplication
`twistMulLocal S a b U` (`glueHom_app`, `restrictSectionMap_apply`); `twistπ` commutes with restriction
(`Hom.map_app_eq_app_map`, `pushforward_twist_map_val`); on the chart the value of `twistπ` is the value of
`χ_n := twistAffineIso.hom ≫ rFIP⁻¹` (`tAH_rFIP_inv_app_val`), and `χ_{a+b}(twistMulLocal (x' ⊗ y')) =
Proj.twistMul (χ_a x' ⊗ χ_b y')` (`twistMulLocal_app_chart`) is the pointwise product
(`Proj.twistMul_app_moduleTensorSection`, `twistSectionMul_val`). -/
theorem twistπ_app_twistMul_app_val (a b : ℤ) (U : X.affineOpens) (V : (relativeProj S).left.Opens)
    (hV : V ≤ (relativeProj S).hom ⁻¹ᵁ U.1) (x : Γ(twist S a, V)) (y : Γ(twist S b, V))
    (p : (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V :
      (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U))).Opens)) :
    Subtype.val ((S.toGradedAffineAlgebra.twistπ (a + b) (AlgebraicGeometry.Scheme.affineSite U)).app V
        ((twistMul S a b).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) (a + b)
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V)) p =
      Subtype.val ((S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app V x :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) a
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V)) p *
      Subtype.val ((S.toGradedAffineAlgebra.twistπ b (AlgebraicGeometry.Scheme.affineSite U)).app V y :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) b
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V)) p := by
  have hr₂ : V ≤ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V := by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf, AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact le_inf hV le_rfl
  have hglue : (twistMul S a b).app V =
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap (twistMulLocal S a b U) V hV := by
    unfold twistMul
    dsimp only
    exact AlgebraicGeometry.Scheme.Modules.glueHom_app _ _ _ _ _ _ U V hV
  have e0 := AlgebraicGeometry.Scheme.Modules.restrictSectionMap_apply (twistMulLocal S a b U) V hV hr₂
    (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)
  have e2 : (AlgebraicGeometry.Scheme.Modules.tensor (twist S a) (twist S b)).presheaf.map
      (homOfLE (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V)).op (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection
        ((twist S a).presheaf.map (homOfLE (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V)).op x)
        ((twist S b).presheaf.map (homOfLE (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V)).op y) :=
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict _ _ _
  rw [hglue, e0, e2]
  set x' := (twist S a).presheaf.map (homOfLE (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V)).op x with hx'
  set y' := (twist S b).presheaf.map (homOfLE (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V)).op y with hy'
  set z := (twistMulLocal S a b U).app (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V)
    (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x' y') with hz
  have e1 : (S.toGradedAffineAlgebra.twistπ (a + b) (AlgebraicGeometry.Scheme.affineSite U)).app V
      ((twist S (a + b)).presheaf.map (homOfLE hr₂).op z) =
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U))).obj
        (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U))
          (a + b))).presheaf.map (homOfLE hr₂).op
        ((S.toGradedAffineAlgebra.twistπ (a + b) (AlgebraicGeometry.Scheme.affineSite U)).app
          (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) z) :=
    (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ hr₂ z).symm
  rw [e1, pushforward_twist_map_val]
  -- the point q ∈ e''A
  have hpA : p.1 ∈ S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ
      (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) :=
    (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U)).preimage_mono hr₂ p.2
  have hq : p.1 ∈ (affineIso S U).hom ''ᵁ (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) := by
    rw [affineIso_image_eq_projChart_preimage S U]
    exact hpA
  have hz' := tAH_rFIP_inv_app_val S U (a + b) (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) z ⟨p.1, hq⟩
  have hx'' := tAH_rFIP_inv_app_val S U a (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) x' ⟨p.1, hq⟩
  have hy'' := tAH_rFIP_inv_app_val S U b (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) y' ⟨p.1, hq⟩
  have hchart := (twistMulLocal_app_chart S U a b (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) x' y').trans
    (AlgebraicGeometry.Proj.twistMul_app_moduleTensorSection (S.sectionsGrading U.1) a b
      ((affineIso S U).hom ''ᵁ (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V)) _ _)
  have hmul := (congrArg (fun s => Subtype.val (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
    (S.sectionsGrading U.1) (a + b) ((affineIso S U).hom ''ᵁ (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V)))
    ⟨p.1, hq⟩) hchart).trans (AlgebraicGeometry.Proj.twistSectionMul_val (S.sectionsGrading U.1) a b
      ((affineIso S U).hom ''ᵁ (((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V)) _ _ ⟨p.1, hq⟩)
  have ex : (S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app
      (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) x' =
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U))).obj
        (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U))
          a)).presheaf.map (homOfLE (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V)).op
        ((S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app V x) :=
    (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ _ x).symm
  have ey : (S.toGradedAffineAlgebra.twistπ b (AlgebraicGeometry.Scheme.affineSite U)).app
      (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) y' =
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U))).obj
        (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U))
          b)).presheaf.map (homOfLE (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V)).op
        ((S.toGradedAffineAlgebra.twistπ b (AlgebraicGeometry.Scheme.affineSite U)).app V y) :=
    (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ _ y).symm
  have hx3 : Subtype.val ((S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app
      (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) x' :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) a
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ
            (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V))) ⟨p.1, hpA⟩ =
      Subtype.val ((S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app V x :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) a
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V)) p :=
    (congrArg (fun s => Subtype.val (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
      (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) a
      (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ
        (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V))) ⟨p.1, hpA⟩) ex).trans
      (pushforward_twist_map_val S (AlgebraicGeometry.Scheme.affineSite U) a
        (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V) _ ⟨p.1, hpA⟩)
  have hy3 : Subtype.val ((S.toGradedAffineAlgebra.twistπ b (AlgebraicGeometry.Scheme.affineSite U)).app
      (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V) y' :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) b
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ
            (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V))) ⟨p.1, hpA⟩ =
      Subtype.val ((S.toGradedAffineAlgebra.twistπ b (AlgebraicGeometry.Scheme.affineSite U)).app V y :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) b
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ V)) p :=
    (congrArg (fun s => Subtype.val (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
      (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) b
      (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ
        (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ V))) ⟨p.1, hpA⟩) ey).trans
      (pushforward_twist_map_val S (AlgebraicGeometry.Scheme.affineSite U) b
        (((relativeProj S).hom ⁻¹ᵁ U.1).ι.image_preimage_le V) _ ⟨p.1, hpA⟩)
  exact hz'.symm.trans (hmul.trans (congrArg₂ (· * ·) (hx''.trans hx3) (hy''.trans hy3)))

end AlgebraicGeometry.Scheme.relativeProj

end
