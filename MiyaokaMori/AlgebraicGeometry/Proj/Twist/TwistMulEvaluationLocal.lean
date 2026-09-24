import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulChartValue

/-! # Multiplicativity of the local evaluation with respect to the twist multiplication

On the relative Proj `π : Proj_X S → X` of a graded
quasi-coherent algebra `S`, for an affine `V ⊆ X`, `u ∈ Γ(V, S_a)`, `v ∈ Γ(V, S_b)`,
`twistMul S a b (evaluationLocal S a V u ⊗ evaluationLocal S b V v) = evaluationLocal S (a+b) V (u·v)`
in `Γ(π⁻¹V, O(a+b))`, where `u·v = sectionsGMul u v ∈ Γ(V, S_{a+b})` is the graded product of sections and the
`eqToHom` only transports the index `(a : ℤ) + b = ((a + b : ℕ) : ℤ)`. Informally: `(u/1)·(v/1) = uv/1`
(Stacks 01MO, `Localization.mk_mul`).

**Proof route** (via the chart projection, instead of unfolding the seven isomorphisms of `twistMulLocal`): the chart
projection `twistπ n (affineSite V) : O(n) ⟶ (c_V)_* O_V(n)` (Stacks 01LI) is injective on sections over `π⁻¹V`
(`twistπ_app_injective`, `…TwistMulAssoc_Pointwise`), commutes with the index transport (`twistπ_app_eqToHom_app`,
`eqToHom_pushforward_twist_app_val`), turns `twistMul` into the pointwise product of homogeneous fractions
(`twistπ_app_twistMul_app_val`, `…TwistMulAssoc_ChartMulValue`) and sends `evaluationLocal S m V x` to the constant
function `p ↦ (sectionsOf V m x)/1` (`twistπ_app_res_evaluationLocal`, `RelativeProjEvaluation`; specialised here
as `twistπ_app_evaluationLocal_val`). The claim is then `(u/1)·(v/1) = (uv)/1` pointwise (`Localization.mk_mul`,
`sectionsOf_sectionsGMul`).

Source: Stacks 01MO (multiplication `O(a) ⊗ O(b) → O(a+b)` on `Proj`, `(a/1)(b/1) = ab/1`), 01NR, 01LI;
the proof of Proposition 2.4 of the paper (coordinate sections).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- `twistπ (affineSite V)` on `evaluationLocal S m V x` over `π⁻¹V` itself: pointwise `a/1`, `a = sectionsOf V m x`
(the case `W' = affineSite V`, `Ω = π⁻¹V` of `twistπ_app_res_evaluationLocal`; `restrictGraded le_rfl = id`). -/
theorem twistπ_app_evaluationLocal_val (m : ℕ) (V : X.affineOpens) (x : Γ(S.part m, V.1))
    (p : (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite V) ⁻¹ᵁ
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) :
      (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite V))).Opens)) :
    Subtype.val ((S.toGradedAffineAlgebra.twistπ (m : ℤ) (AlgebraicGeometry.Scheme.affineSite V)).app
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x) :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite V)) (m : ℤ)
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite V) ⁻¹ᵁ
            ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))) p =
      Localization.mk (S.sectionsOf V.1 m x).1 1 := by
  have h := twistπ_app_res_evaluationLocal S m V (le_refl (AlgebraicGeometry.Scheme.affineSite V))
    (le_refl ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) x p
  have hid : (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map
      (homOfLE (le_refl ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))).op
      (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x := by
    have e : (homOfLE (le_refl ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))).op =
        𝟙 (op ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) := rfl
    rw [e, CategoryTheory.Functor.map_id]
    rfl
  rw [hid] at h
  refine h.trans ?_
  rw [S.toGradedAffineAlgebra.restrictGraded_refl]
  rfl

/-- `of (m+n) (u·v) = of m u * of n v` in the section ring (`DirectSum.of_mul_of`; used by
`TwistPullbackPowLocal`, which imports this module). -/
theorem sectionsOf_sectionsGMul {m n : ℕ} (V : X.Opens) (u : Γ(S.part m, V)) (v : Γ(S.part n, V)) :
    ((S.sectionsOf V (m + n) (S.sectionsGMul V u v) : S.sectionsGrading V (m + n)) : S.sectionsRing V) =
      ((S.sectionsOf V m u : S.sectionsGrading V m) : S.sectionsRing V) *
        ((S.sectionsOf V n v : S.sectionsGrading V n) : S.sectionsRing V) :=
  (DirectSum.of_mul_of (A := S.sectionsPiece V) u v).symm

/-- **`twistMul` on evaluated sections** (Stacks 01MO on the chart `π⁻¹V ≅ Proj A(V)`): for affine `V`, `u ∈ Γ(V, S_a)`, `v ∈ Γ(V, S_b)`,
`twistMul S a b (u/1 ⊗ v/1) = (uv)/1` in `Γ(π⁻¹V, O(a+b))`, where `u/1 := evaluationLocal S a V u` and
`uv := S.sectionsGMul V u v ∈ Γ(V, S_{a+b})`; the `eqToHom` transports `(a : ℤ) + b = ((a + b : ℕ) : ℤ)`.

Proof (chart projection, Stacks 01LI + 01MO): `twistπ ((a+b : ℕ) : ℤ) (affineSite V)` is injective on sections over
`π⁻¹V` (`twistπ_app_injective`), so it suffices to compare the values of the two sides at every point `p` of the chart:
`twistπ` commutes with `eqToHom` (`twistπ_app_eqToHom_app`; the transport does not change the underlying function,
`eqToHom_pushforward_twist_app_val`), is multiplicative on `twistMul` (`twistπ_app_twistMul_app_val`), and
`twistπ (evaluationLocal S m V x)` has the constant value `(sectionsOf V m x)/1` (`twistπ_app_evaluationLocal_val`); so
the left value is `(ū/1)(v̄/1) = (ū v̄)/1` (`Localization.mk_mul`) and `ū v̄ = of (a+b) (uv)`
(`sectionsOf_sectionsGMul`). Edge cases: `a` or `b` may be `0`; `V = ⊥`: no point `p`, both sides equal. -/
theorem twistMul_app_moduleTensorSection_evaluationLocal (a b : ℕ) (V : X.affineOpens)
    (u : Γ(S.part a, V.1)) (v : Γ(S.part b, V.1)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S)
          (Nat.cast_add a b).symm)).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S a V u)
          (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S b V v)) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S (a + b) V (S.sectionsGMul V.1 u v) := by
  apply twistπ_app_injective S ((a + b : ℕ) : ℤ) V ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) le_rfl
  refine Subtype.ext (funext fun p => ?_)
  have hL := twistπ_app_eqToHom_app S (AlgebraicGeometry.Scheme.affineSite V) (Nat.cast_add a b).symm
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
    ((AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ)).app
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S a V u)
        (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S b V v)))
  have hL' := congrArg (fun s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
      (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite V)) ((a + b : ℕ) : ℤ)
      (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite V) ⁻¹ᵁ
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) => Subtype.val s p) hL
  have hE := eqToHom_pushforward_twist_app_val S (AlgebraicGeometry.Scheme.affineSite V) (Nat.cast_add a b).symm
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
    ((S.toGradedAffineAlgebra.twistπ ((a : ℤ) + (b : ℤ)) (AlgebraicGeometry.Scheme.affineSite V)).app
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      ((AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ)).app
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S a V u)
          (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S b V v)))) p
  have hM := twistπ_app_twistMul_app_val S (a : ℤ) (b : ℤ) V ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
    le_rfl (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S a V u)
    (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S b V v) p
  have hu := twistπ_app_evaluationLocal_val S a V u p
  have hv := twistπ_app_evaluationLocal_val S b V v p
  have huv := twistπ_app_evaluationLocal_val S (a + b) V (S.sectionsGMul V.1 u v) p
  have hmul := sectionsOf_sectionsGMul S V.1 u v
  refine hL'.trans (hE.trans (hM.trans ?_))
  refine (congrArg₂ (· * ·) hu hv).trans (Eq.trans ?_ huv.symm)
  refine (Localization.mk_mul _ _ _ _).trans ?_
  congr 1
  · exact hmul.symm
  · exact Subtype.ext (one_mul (1 : S.sectionsRing V.1))

end AlgebraicGeometry.Scheme.relativeProj

end
