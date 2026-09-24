import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetWeightDefect
import MiyaokaMori.AlgebraicGeometry.Morphisms.GmLaurentIndependence

/-! # Sections of the weight defect

For a `𝔾_m`-action `α : 𝔾_m ×_k T → T` (with `T` over `S`), the section formula for the weight-`m` defect
`φ_m = weightDefect α m`, and the linear independence of eigensections of different weights:
* `snd_comp_preimage_eq_act_preimage`: `pr₂⁻¹(π⁻¹U) = act⁻¹(π⁻¹U)` (take preimages on both sides of `act_over`);
* `weightDefect_val_app_apply`: `φ_m(a) = act^♯(a) − λ^m · pr₂^♯(a)` on every open set and section, with
  `λ = Gm.lambdaOn`;
* `eq_zero_of_weightDefect_eq_zero_of_sum_eq_zero`: if `y_n ∈ Γ(π⁻¹U)` satisfy `φ_n(y_n) = 0` (`n ∈ ℕ`, finite
  support) and `Σ_n y_n = 0`, then `y = 0` (apply the ring homomorphism `act^♯` to `Σ y_n = 0` to get
  `Σ λ^n pr₂^♯(y_n) = 0`, then use `Gm_pullback_lambda_pow_independent`). This is the section-level form of the
  relative version of Stacks 0EKK ("`A = ⊕ A_n` is a direct sum").

References: §2 of the paper (the grading by parameter rescaling); Stacks 0EKK.

`weightDefect_val_app_apply` has the same content as `GroupSchemeAction.weightDefect_app_apply` in
`JetRescalingChart`, which lies downstream of `JetGrading`; it is restated here with `λ` written as `Gm.lambdaOn`
(definitionally equal), matching the notation of `Gm_pullback_lambda_pow_independent`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace GroupSchemeAction

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}

/-- `pr₂⁻¹(π⁻¹U) = act⁻¹(π⁻¹U)`: take preimages of `U` on both sides of `act_over` (`comp_preimage` is `rfl`). -/
theorem snd_comp_preimage_eq_act_preimage (α : GmActionOver k T) (U : S.Opens) :
    CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⁻¹ᵁ (T.hom ⁻¹ᵁ U) =
      α.act ⁻¹ᵁ (T.hom ⁻¹ᵁ U) := by
  exact (congrArg (fun f => f ⁻¹ᵁ U) α.act_over).symm

/-- The section formula for the weight-`m` defect: `φ_m(a) = act^♯(a) − λ^m · pr₂^♯(a)`.
Here `W := 𝔾_m ×_k T`, `act^♯ = α.act.appLE (π⁻¹U) (pr₂⁻¹(π⁻¹U))` (the inclusion `hle` comes from
`snd_comp_preimage_eq_act_preimage`), `pr₂^♯ = pr₂.appLE (π⁻¹U) (pr₂⁻¹(π⁻¹U))`, and
`λ = Gm.lambdaOn (π ≫ (S → Spec k)) (π⁻¹U)` (the coordinate `T 1` of `𝔾_m` pulled back along `pr₁` to `W` and
restricted).

Proof: unfold `weightDefect` and evaluate each piece on sections over `U` (all `rfl`-level unfolding): the first
term is `presheaf.map (eqToHom _).op (act.app _ a)`, which differs from `appLE` only by a `Subsingleton` of
`Opens`-homomorphisms (`congr 3`); the second term is, by definition of `unitMul` / `unitHomEquiv.symm`,
`x ↦ x • res c = x * res c`, then `mul_comm` and `appLE_eq_app`. -/
theorem weightDefect_val_app_apply (α : GmActionOver k T) (m : ℕ) (U : S.Opens)
    (a : Γ(T.left, T.hom ⁻¹ᵁ U))
    (hle : CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⁻¹ᵁ (T.hom ⁻¹ᵁ U) ≤
      α.act ⁻¹ᵁ (T.hom ⁻¹ᵁ U)) :
    (show Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))),
        CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⁻¹ᵁ (T.hom ⁻¹ᵁ U)) from
      ((GroupSchemeAction.weightDefect α m).val.app (Opposite.op U)).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
          (SheafOfModules.unit T.left.ringCatSheaf)).val.obj (Opposite.op U) : Type u) from a)) =
    (α.act.appLE (T.hom ⁻¹ᵁ U) _ hle).hom a -
      Gm.lambdaOn (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) (T.hom ⁻¹ᵁ U) ^ m *
      ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appLE (T.hom ⁻¹ᵁ U) _ le_rfl).hom a := by
  -- first term on sections: restricting `act^♯ a` along `eqToHom` is `appLE`
  have hA : (show Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))), CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⁻¹ᵁ (T.hom ⁻¹ᵁ U)) from
      ((((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).map
          (SheafOfModules.unitToPushforwardObjUnit α.act.toRingCatSheafHom) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp α.act T.hom).hom.app _ ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardCongr α.act_over).hom.app _).val.app (Opposite.op U)).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
          (SheafOfModules.unit T.left.ringCatSheaf)).val.obj (Opposite.op U) : Type u) from a))) =
      (α.act.appLE (T.hom ⁻¹ᵁ U) _ hle).hom a := by
    show ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map (CategoryTheory.eqToHom
          (by rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, α.act_over])).op).hom
        ((α.act.app (T.hom ⁻¹ᵁ U)).hom a) = _
    show _ = ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map (CategoryTheory.homOfLE hle).op).hom ((α.act.app (T.hom ⁻¹ᵁ U)).hom a)
    congr 3
  -- second term on sections: `pr₂^♯ a` times the restriction of `c` (`unitMul` is `x ↦ x • res c`)
  have hB : (show Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))), CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⁻¹ᵁ (T.hom ⁻¹ᵁ U)) from
      ((((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).map
          (SheafOfModules.unitToPushforwardObjUnit (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).toRingCatSheafHom) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) T.hom).hom.app _ ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom)).map
          (AlgebraicGeometry.Scheme.Modules.unitMul ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
          (LaurentPolynomial.T 1)) ^ m))).val.app (Opposite.op U)).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
          (SheafOfModules.unit T.left.ringCatSheaf)).val.obj (Opposite.op U) : Type u) from a))) =
      Gm.lambdaOn (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) (T.hom ⁻¹ᵁ U) ^ m *
        ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appLE (T.hom ⁻¹ᵁ U) _ le_rfl).hom a := by
    show ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).app (T.hom ⁻¹ᵁ U)).hom a *
        ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map (CategoryTheory.homOfLE le_top).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
          (LaurentPolynomial.T 1)) ^ m) = _
    rw [mul_comm]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [map_pow]
      rfl
    exact (congrArg (fun φ : Γ(T.left, T.hom ⁻¹ᵁ U) ⟶ Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))), CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⁻¹ᵁ (T.hom ⁻¹ᵁ U)) => φ.hom a)
      (AlgebraicGeometry.Scheme.Hom.appLE_eq_app (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))))).symm
  exact (congrArg₂ (· - ·) hA hB : _)

/-- **Eigensections of different weights are linearly independent** (the "direct sum" half of the relative
version of Stacks 0EKK, on sections). Let `U ⊆ S` be an affine open, `π := T.hom` affine (so `V := π⁻¹U` is
affine) and `y : ℕ →₀ Γ(V)`; if every `y_n` is a `λ^n`-eigensection (`φ_n(y_n) = 0`) and `Σ_n y_n = 0`, then
`y = 0`.

Proof: `act^♯ := α.act.appLE V (pr₂⁻¹V)` is a ring homomorphism; by `weightDefect_val_app_apply` and
`φ_n(y_n) = 0` we get `act^♯(y_n) = λ^n · pr₂^♯(y_n)`; applying `act^♯` to `Σ y_n = 0` gives
`Σ λ^n · pr₂^♯(y_n) = 0`, and `Gm_pullback_lambda_pow_independent` (the powers of `λ` are linearly independent
over `Γ(V)`) gives `y = 0`. -/
theorem eq_zero_of_weightDefect_eq_zero_of_sum_eq_zero [AlgebraicGeometry.IsAffineHom T.hom]
    (α : GmActionOver k T) (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (y : ℕ →₀ Γ(T.left, T.hom ⁻¹ᵁ U))
    (h0 : ∀ n, ((GroupSchemeAction.weightDefect α n).val.app (Opposite.op U)).hom
      (show (((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
          (SheafOfModules.unit T.left.ringCatSheaf)).val.obj (Opposite.op U) : Type u) from y n) = 0)
    (hsum : y.sum (fun _ a => a) = 0) : y = 0 := by
  have hV : AlgebraicGeometry.IsAffineOpen (T.hom ⁻¹ᵁ U) := hU.preimage T.hom
  have hle := (GroupSchemeAction.snd_comp_preimage_eq_act_preimage α U).le
  have key : ∀ n, (α.act.appLE (T.hom ⁻¹ᵁ U) _ hle).hom (y n) =
      Gm.lambdaOn (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) (T.hom ⁻¹ᵁ U) ^ n *
        ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appLE (T.hom ⁻¹ᵁ U) _ le_rfl).hom (y n) := by
    intro n
    have h := GroupSchemeAction.weightDefect_val_app_apply α n U (y n) hle
    rw [h0 n] at h
    exact sub_eq_zero.mp h.symm
  refine Gm_pullback_lambda_pow_independent (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (T.hom ⁻¹ᵁ U) hV y ?_
  have h2 : (α.act.appLE (T.hom ⁻¹ᵁ U) _ hle).hom (y.sum (fun _ a => a)) = 0 := by
    rw [hsum]; exact map_zero _
  rw [Finsupp.sum, map_sum] at h2
  rw [Finsupp.sum]
  exact (Finset.sum_congr rfl (fun n _ => (key n).symm)).trans h2

end GroupSchemeAction

end
