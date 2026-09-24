import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulChartValue

/-! # Associativity of the twist multiplication on sections

**Associativity** on sections of the multiplication `twistMul : O(a) ⊗ O(b) ⟶ O(a+b)` of the twisting sheaves of a
relative Proj (Stacks 01MO: these multiplication maps satisfy the obvious compatibilities).

Source: Stacks 01MO.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Associativity of `twistMul` on sections over `V ≤ π⁻¹U`** (the local case of `twistMul_app_assoc`): both sides
are sections of `O(a+b+c)` over `V`; `twistπ (a+b+c) U` is injective on such sections (Stacks 01LI,
`twistπ_app_injective`), commutes with the index transport `eqToHom` (`twistπ_app_eqToHom_app`), and turns each
`twistMul` into the pointwise product of homogeneous fractions on the chart (`twistπ_app_twistMul_app_val`); so the claim
is `mul_assoc` pointwise. -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistMul_app_assoc_of_le {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b c : ℤ) (U : X.affineOpens) (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (hV : V ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
    (x : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, V)) (y : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, V)) (z : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S c, V)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistMul S (a + b) c).app V
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) z) =
      (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm)).app V
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a (b + c)).app V
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x ((AlgebraicGeometry.Scheme.relativeProj.twistMul S b c).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection y z)))) := by
  apply AlgebraicGeometry.Scheme.relativeProj.twistπ_app_injective S (a + b + c) U V hV
  rw [AlgebraicGeometry.Scheme.relativeProj.twistπ_app_eqToHom_app S (AlgebraicGeometry.Scheme.affineSite U) (add_assoc a b c).symm]
  refine Subtype.ext (funext fun p => ?_)
  have h1 := AlgebraicGeometry.Scheme.relativeProj.twistπ_app_twistMul_app_val S (a + b) c U V hV
    ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) z p
  have h2 := AlgebraicGeometry.Scheme.relativeProj.twistπ_app_twistMul_app_val S a b U V hV x y p
  have h3 := AlgebraicGeometry.Scheme.relativeProj.eqToHom_pushforward_twist_app_val S (AlgebraicGeometry.Scheme.affineSite U) (add_assoc a b c).symm V
    ((S.toGradedAffineAlgebra.twistπ (a + (b + c)) (AlgebraicGeometry.Scheme.affineSite U)).app V
      ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a (b + c)).app V
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x ((AlgebraicGeometry.Scheme.relativeProj.twistMul S b c).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection y z))))) p
  have h4 := AlgebraicGeometry.Scheme.relativeProj.twistπ_app_twistMul_app_val S a (b + c) U V hV x
    ((AlgebraicGeometry.Scheme.relativeProj.twistMul S b c).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection y z)) p
  have h5 := AlgebraicGeometry.Scheme.relativeProj.twistπ_app_twistMul_app_val S b c U V hV y z p
  exact (h1.trans (congrArg (· * _) h2)).trans ((mul_assoc _ _ _).trans
    ((congrArg (_ * ·) h5.symm).trans (h4.symm.trans h3.symm)))


/-- **Associativity of `twistMul` (section version)**: for `V ⊆ Proj_X S` open, `x ∈ Γ(O(a), V)`, `y ∈ Γ(O(b), V)`,
`z ∈ Γ(O(c), V)`, one has `(x·y)·z = x·(y·z)` in `Γ(O(a+b+c), V)` (the right-hand side transported by the `eqToHom`
of `a + (b + c) = a + b + c`).

**Proof (Stacks 01MO, 01LI; via the chart projections)**:
1. Locality: `O(a+b+c)` is a sheaf, `{V ⊓ π⁻¹U : U affine}` covers `V` (`iSup_affineOpens_eq_top`), and restriction
   commutes with `twistMul.app`, `eqToHom.app` and `moduleTensorSection` (`Hom.map_app_eq_app_map`,
   `moduleTensorSection_restrict`), so it suffices to treat the case `V ≤ π⁻¹U` (`twistMul_app_assoc_of_le`).
2. On `V ≤ π⁻¹U`, the chart projection `twistπ (a+b+c) U : O(a+b+c) ⟶ (c_U)_* O_U(a+b+c)` is injective on sections
   (Stacks 01LI, `twistπ_app_injective`) and commutes with `eqToHom` (`twistπ_app_eqToHom_app`), so it suffices to
   compare pointwise values.
3. `twistπ` turns `twistMul` into the pointwise multiplication of homogeneous fractions on the chart `Proj A(U)`
   (`twistπ_app_twistMul_app_val`, `RelativeProjTwistMulChartValue`), so the two sides are pointwise `(x·y)·z` and
   `x·(y·z)`, and `mul_assoc` finishes.

**Edge cases**: `a, b, c` are arbitrary integers (possibly negative); for `V = ⊥` the section group is zero and the
statement is trivial. -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistMul_app_assoc {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b c : ℤ) (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (x : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, V))
    (y : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, V))
    (z : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S c, V)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistMul S (a + b) c).app V
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) z) =
      (CategoryTheory.eqToHom
          (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm)).app V
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a (b + c)).app V
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x
            ((AlgebraicGeometry.Scheme.relativeProj.twistMul S b c).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection y z)))) := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨(AlgebraicGeometry.Scheme.relativeProj.twist S (a + b + c)).presheaf, (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b + c)).isSheaf⟩
    (fun U : X.affineOpens => V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) V
    (fun U => CategoryTheory.homOfLE inf_le_left) ?_ _ _ ?_
  · intro p hp
    have hp' : (AlgebraicGeometry.Scheme.relativeProj S).hom.base p ∈ (⊤ : X.Opens) := trivial
    rw [← AlgebraicGeometry.iSup_affineOpens_eq_top X] at hp'
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hp'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hp, hU⟩
  · intro U
    have h : V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1 ≤ V := inf_le_left
    change (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b + c)).presheaf.map (CategoryTheory.homOfLE h).op _ =
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b + c)).presheaf.map (CategoryTheory.homOfLE h).op _
    have hL : (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b + c)).presheaf.map (CategoryTheory.homOfLE h).op
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S (a + b) c).app V
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) z)) =
        (AlgebraicGeometry.Scheme.relativeProj.twistMul S (a + b) c).app (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
            ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
              (AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((AlgebraicGeometry.Scheme.relativeProj.twist S a).presheaf.map (CategoryTheory.homOfLE h).op x)
                ((AlgebraicGeometry.Scheme.relativeProj.twist S b).presheaf.map (CategoryTheory.homOfLE h).op y)))
            ((AlgebraicGeometry.Scheme.relativeProj.twist S c).presheaf.map (CategoryTheory.homOfLE h).op z)) := by
      refine (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ h _).trans ?_
      refine congrArg _ ((AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (CategoryTheory.homOfLE h) _ _).trans ?_)
      refine congrArg (fun t => AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
        ((AlgebraicGeometry.Scheme.relativeProj.twist S c).presheaf.map (CategoryTheory.homOfLE h).op z)) ?_
      exact (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ h _).trans
        (congrArg _ (AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (CategoryTheory.homOfLE h) _ _))
    have hR : (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b + c)).presheaf.map (CategoryTheory.homOfLE h).op
        ((CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm)).app V
          ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a (b + c)).app V
            (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x ((AlgebraicGeometry.Scheme.relativeProj.twistMul S b c).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection y z))))) =
        (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm)).app (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
          ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a (b + c)).app (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
            (AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((AlgebraicGeometry.Scheme.relativeProj.twist S a).presheaf.map (CategoryTheory.homOfLE h).op x)
              ((AlgebraicGeometry.Scheme.relativeProj.twistMul S b c).app (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
                (AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((AlgebraicGeometry.Scheme.relativeProj.twist S b).presheaf.map (CategoryTheory.homOfLE h).op y)
                  ((AlgebraicGeometry.Scheme.relativeProj.twist S c).presheaf.map (CategoryTheory.homOfLE h).op z))))) := by
      refine (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ h _).trans ?_
      refine congrArg _ ((AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ h _).trans ?_)
      refine congrArg _ ((AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (CategoryTheory.homOfLE h) _ _).trans ?_)
      refine congrArg (fun t => AlgebraicGeometry.Scheme.Modules.moduleTensorSection
        ((AlgebraicGeometry.Scheme.relativeProj.twist S a).presheaf.map (CategoryTheory.homOfLE h).op x) t) ?_
      exact (AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map _ h _).trans
        (congrArg _ (AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (CategoryTheory.homOfLE h) _ _))
    rw [hL, hR]
    exact AlgebraicGeometry.Scheme.relativeProj.twistMul_app_assoc_of_le S a b c U (V ⊓ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) inf_le_right _ _ _


end
