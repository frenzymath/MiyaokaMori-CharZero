import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Divisors.OrdNonnegOfRegularX
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffCartierLineBundlePairing

/-! # An effective Cartier divisor gives a Cartier divisor with nonnegative Weil coefficients

An effective Cartier divisor `D` on a variety corresponds to a Cartier divisor `D'` (in the sense of
`CartierDivisor`) all of whose Weil coefficients are nonnegative, with `O_X(D') ≅ O_X(D)`. The curve
case is used for the degree bounds in the proofs of Lemma 3.1 and Theorem 4.2 of the paper.

Proof (for any variety `X`; `EffCartier.exists_cartierDivisor_nonneg_variety`):
1. Local equations: at every point `p` take a frame `(W_p, e_p)` of `I_D` (`EffCartier.exists_frame_ideal`);
   `a_p := ι(e_p) ∈ Γ(X, W_p)` is nonzero (frame, `ι` injective, `Γ(X, W_p)` nontrivial); let `f_p` be the
   value of `a_p` at the generic point, in `K(X)^×` (`X` integral, `germToFunctionField_injective`).
2. Compatibility: on `W_i ∩ W_j` the two frames differ by a unit `u` (`IsFrame.exists_unit`), so
   `a_i = u·a_j` and `f_i / f_j` is the generic value of `u`, which is the germ of `u` at `x`
   (`algebraMap_germ_eq_germToFunctionField`), a unit of `O_{X,x}`. This gives
   `CartierDivisor.IsLocalData W f`; put `D' := CartierDivisor.ofLocalData W f`.
3. Nonnegative coefficients: `weilCycle_ofLocalData` gives the coefficient of `[D']` at `p` as
   `ord_p(f_p)`, the order of the generic value of `a_p`, which is regular and nonzero on `W_p`, so
   `ord_nonneg_of_regular` gives `≥ 0`.
4. Line bundle isomorphism: `local_section_ofLocalData` gives a local equation `t_p` of `D'` on `W_p`
   with generic value `f_p`; it has the same generic value as `ι(a_p)`, so `t_p = ι(a_p)` by the
   injectivity half of Stacks 01X5 (`rationalSectionToFunctionField_injective`). Thus `(e_p, t_p)` is an
   `EffCartierPairing.LocalPair`, and `lineBundleModulesIsoSheaf` gives `O_X(D') ≅ I_D^∨ = O_X(D)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.EffCartierPairing

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules CartierDivisor

variable {k : Type u} [Field k] {X : Variety k}

/-- The image `ι(e)` of a frame `e` is nonzero (for `W` nonempty). -/
theorem idealIota_frame_ne_zero (D : X.toScheme.EffCartier) {W : X.toScheme.Opens} [Nonempty W]
    {e : Γ(D.ideal.toModules, W)} (he : IsFrame D.ideal.toModules W e) :
    EffCartier.idealIota D.ideal W e ≠ 0 := by
  intro h0
  have h1 : (1 : Γ(X.toScheme, W)) • D.ideal.toModules.res le_rfl e =
      (0 : Γ(X.toScheme, W)) • D.ideal.toModules.res le_rfl e := by
    apply EffCartier.idealIota_injective
    rw [_root_.map_smul, _root_.map_smul, smul_eq_mul, smul_eq_mul, res_self, h0, mul_zero, mul_zero]
  exact one_ne_zero ((he W le_rfl).1 h1)

/-- On any variety, an effective Cartier divisor `D` gives a Cartier divisor `D'` with nonnegative Weil
coefficients and `O_X(D') ≅ O_X(D)`. -/
theorem _root_.AlgebraicGeometry.Scheme.EffCartier.exists_cartierDivisor_nonneg_variety
    (X : Variety k) (D : X.toScheme.EffCartier) :
    ∃ D' : CartierDivisor X,
      (∀ p : X.toScheme, 0 ≤ (CartierDivisor.weilCycle X D' :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) p) ∧
      Nonempty (lineBundleModules D' ≅ D.sheaf) := by
  classical
  choose W hpW e he using D.exists_frame_ideal
  have hne : ∀ p, Nonempty (W p) := fun p => ⟨⟨p, hpW p⟩⟩
  let a : ∀ p : X.toScheme, Γ(X.toScheme, W p) := fun p => EffCartier.idealIota D.ideal (W p) (e p)
  have ha : ∀ p, a p ≠ 0 := fun p => by
    have := hne p
    exact idealIota_frame_ne_zero D (he p)
  have hga : ∀ p, (have := hne p; (X.toScheme.germToFunctionField (W p)).hom (a p)) ≠ 0 := by
    intro p h0
    have := hne p
    exact ha p (X.toScheme.germToFunctionField_injective (W p) (h0.trans (map_zero _).symm))
  let f : X.toScheme → (X.toScheme.functionField)ˣ := fun p =>
    have := hne p
    Units.mk0 ((X.toScheme.germToFunctionField (W p)).hom (a p)) (hga p)
  have hf : ∀ p, (have := hne p; (f p : X.toScheme.functionField)) =
      (have := hne p; (X.toScheme.germToFunctionField (W p)).hom (a p)) := fun p => rfl
  have hcover : (⨆ p, W p) = ⊤ :=
    top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hpW x⟩
  -- compatibility: f_i / f_j is a unit of the stalk at x ∈ W_i ∩ W_j
  have hratio : ∀ i j : X.toScheme, ∀ x ∈ W i ⊓ W j,
      ((f i / f j : (X.toScheme.functionField)ˣ) : X.toScheme.functionField) ∈
        Set.range (fun v : (X.toScheme.presheaf.stalk x)ˣ =>
          algebraMap (X.toScheme.presheaf.stalk x) X.toScheme.functionField v) := by
    intro i j x hx
    have := hne i
    have := hne j
    have hWij : Nonempty (W i ⊓ W j : X.toScheme.Opens) := ⟨⟨x, hx⟩⟩
    have hij₁ : (W i ⊓ W j : X.toScheme.Opens) ≤ W i := inf_le_left
    have hij₂ : (W i ⊓ W j : X.toScheme.Opens) ≤ W j := inf_le_right
    obtain ⟨u, hu⟩ := ((he j).restrict hij₂).exists_unit ((he i).restrict hij₁)
    -- a_i|_{W_i ∩ W_j} = u · a_j|_{W_i ∩ W_j}
    have hau : X.toScheme.presheaf.map (homOfLE hij₁).op (a i) =
        (u : Γ(X.toScheme, W i ⊓ W j)) * X.toScheme.presheaf.map (homOfLE hij₂).op (a j) := by
      have h1 : EffCartier.idealIota D.ideal (W i ⊓ W j) (D.ideal.toModules.res hij₁ (e i)) =
          X.toScheme.presheaf.map (homOfLE hij₁).op (a i) :=
        EffCartier.idealIota_map D.ideal (homOfLE hij₁) (e i)
      have h2 : EffCartier.idealIota D.ideal (W i ⊓ W j) (D.ideal.toModules.res hij₂ (e j)) =
          X.toScheme.presheaf.map (homOfLE hij₂).op (a j) :=
        EffCartier.idealIota_map D.ideal (homOfLE hij₂) (e j)
      have h3 := congrArg (EffCartier.idealIota D.ideal (W i ⊓ W j)) hu
      rw [_root_.map_smul, smul_eq_mul, h1, h2] at h3
      exact h3.symm
    -- in the function field: f_i = u_η · f_j
    have hK : (f i : X.toScheme.functionField) =
        (X.toScheme.germToFunctionField (W i ⊓ W j)).hom (u : Γ(X.toScheme, W i ⊓ W j)) *
          (f j : X.toScheme.functionField) := by
      have h1 := congrArg (X.toScheme.germToFunctionField (W i ⊓ W j)).hom hau
      rw [map_mul] at h1
      rw [hf i, hf j]
      refine Eq.trans ?_ (h1.trans ?_)
      · exact (X.toScheme.presheaf.germ_res_apply (homOfLE hij₁) (genericPoint X.toScheme) _ (a i)).symm
      · congr 1
        exact X.toScheme.presheaf.germ_res_apply (homOfLE hij₂) (genericPoint X.toScheme) _ (a j)
    refine ⟨Units.map (X.toScheme.presheaf.germ (W i ⊓ W j) x hx).hom u, ?_⟩
    change algebraMap (X.toScheme.presheaf.stalk x) X.toScheme.functionField
      ((X.toScheme.presheaf.germ (W i ⊓ W j) x hx).hom (u : Γ(X.toScheme, W i ⊓ W j))) = _
    rw [Units.val_div_eq_div_val, hK, mul_div_cancel_right₀ _ (Units.ne_zero (f j))]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X.toScheme hx (u : Γ(X.toScheme, W i ⊓ W j))
  have hUf : CartierDivisor.IsLocalData W f :=
    ⟨hcover, fun i j x hx => ⟨hratio i j x hx, hratio j i x ⟨hx.2, hx.1⟩⟩⟩
  refine ⟨CartierDivisor.ofLocalData W f, ?_, ?_⟩
  · -- nonnegative coefficients
    intro p
    rw [CartierDivisor.weilCycle_ofLocalData X W f hUf p p (hpW p)]
    have := hne p
    rw [hf p]
    exact ord_nonneg_of_regular (hpW p) (ha p)
  · -- line bundle isomorphism
    have hrel : HasLocalPairs D (CartierDivisor.ofLocalData W f) := by
      intro p
      have := hne p
      obtain ⟨t, hval, hloc⟩ :=
        CartierToWeilLocalSection.local_section_ofLocalData W f hUf p p (hpW p)
      refine ⟨W p, hpW p, ⟨⟨e p, he p, t, hloc, ?_⟩⟩⟩
      apply X.toScheme.rationalSectionToFunctionField_injective (W p)
      have h1 : (X.toScheme.rationalSectionToFunctionField (W p)).hom (unitVal t) =
          (f p : X.toScheme.functionField) := congrArg Units.val hval
      have h2 : (X.toScheme.rationalSectionToFunctionField (W p)).hom
          ((X.toScheme.toRationalFunctionsSheaf.hom.app (op (W p))).hom (a p)) =
          (X.toScheme.germToFunctionField (W p)).hom (a p) :=
        congrArg (fun φ => φ.hom (a p))
          (X.toScheme.toRationalFunctionsSheaf_rationalSectionToFunctionField (W p))
      rw [h1, h2, hf p]
    exact ⟨lineBundleModulesIsoSheaf hrel⟩

end MiyaokaMori.EffCartierPairing

/-- On a smooth projective curve, an effective Cartier divisor `D` gives a Cartier divisor `D'` with
nonnegative Weil coefficients and `O_C(D') ≅ O_C(D)`. -/
theorem EffectiveCartierDivisor.exists_cartierDivisor_nonneg {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (D : AlgebraicGeometry.EffectiveCartierDivisor C.toScheme) :
    ∃ D' : CartierDivisor C.toVariety,
      (∀ p : C.toScheme, 0 ≤ (CartierDivisor.weilCycle C.toVariety D' :
        AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) p) ∧
      Nonempty ((CartierDivisor.lineBundle D').toModules ≅
        AlgebraicGeometry.EffectiveCartierDivisor.lineBundle D) := by
  obtain ⟨D', hD', hiso⟩ :=
    AlgebraicGeometry.Scheme.EffCartier.exists_cartierDivisor_nonneg_variety C.toVariety D
  exact ⟨D', hD', hiso⟩

end
