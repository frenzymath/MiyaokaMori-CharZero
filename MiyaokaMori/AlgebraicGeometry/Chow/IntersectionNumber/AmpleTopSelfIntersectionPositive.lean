import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapEffectiveEqDivisorCycle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.AmpleTopSelfIntersectionPositive_CapDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.AmpleTopSelfIntersectionPositive_EffectiveCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks01pu

/-! # Positivity of the top self-intersection of an ample line bundle

An ample line bundle has positive top self-intersection on every integral closed subscheme of
positive dimension: if `H` is ample, `V ↪ X` integral and proper with `dim V > 0`, then
`((H|_V)^{dim V}) > 0` (the "only if" direction of the Nakai criterion; the Chow form of Stacks 0BEV).

Source: Lazarsfeld, Positivity in Algebraic Geometry I, Thm 1.2.23 ("only if", p. 34); Stacks 0BEV;
used for Lemma 2.5 of the paper.

## Proof (Stacks 0BEV, Chow form)

Reduce to `L := ι^*H`, ample on `V` (Stacks 01PU). Prove by induction on `d` the statement
`P(d)`: for every integral scheme `W` proper over `k` with `dim W = d` and every ample line bundle
`M` on `W`, `(M^d) > 0`.

* `d = 0`: `(M^0) = deg [W] = [κ(W) : k] > 0`
  (`AmpleTopSelfIntersection.topSelfIntersection_pos_of_dimension_zero`).
* `d = e + 1`: ampleness at the generic point `η` gives `m > 0` and `s ∈ Γ(W, M^{⊗m})` with
  `s(η) ≠ 0` (so `s ≠ 0`) and `W_s` affine. `W_s ≠ W`: otherwise `W` is affine and proper over
  `k`, hence finite over `k`, hence zero-dimensional (`dimension_eq_zero_of_isAffine`). So `Z(s)`
  is nonempty; it has a point `x₀` of coheight `1` (Krull, `exists_mem_support_coheight_eq_one`),
  and the coefficient of `[Z(s)]_e` at `x₀` is `ord_{x₀}(s) ≥ 1`
  (`idealSheafOfSection_cycle_pos_of_coheight_eq_one`). Now
  `m · (M^{e+1}) = deg(c₁(M)^e ∩ (m · c₁(M) ∩ [W])) = deg(c₁(M)^e ∩ (c₁(M^{⊗m}) ∩ [W]))`
  (`c₁(M^{⊗m}) = m · c₁(M)`), and `c₁(M^{⊗m}) ∩ [W] = [Z(s)]_e`
  (`firstChernClass_cap_fundamentalClass_of_regular_section`, Ful98 §2.3 / Stacks 02SJ);
  `[Z(s)]_e` is effective, so `[Z(s)]_e = Σ_{x ∈ S} a_x · ι_{x*}[W_x]` with `a_x > 0`,
  `W_x` the reduced point closures of the height-`e` points of its support
  (`effective_cycle_class_eq_sum_pointClosure`), and `x₀ ∈ S`. By the projection formula and
  degree invariance under pushforward, `deg(c₁(M)^e ∩ ι_{x*}[W_x]) = ((ι_x^*M)^e)`
  (`capDegree_chowPushforward_fundamentalChowClass`), which is `> 0` by `P(e)` since `ι_x^*M` is
  ample (01PU) and `dim W_x = e`. A nonempty sum of positive terms is positive, so
  `m · (M^{e+1}) > 0` and hence `(M^{e+1}) > 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.AmpleTopSelfIntersection

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure

/-- The induction statement `P(d)` of Stacks 0BEV: every ample line bundle on an integral
`d`-dimensional scheme proper over `k` has positive top self-intersection. -/
theorem topSelfIntersection_pos_of_isAmple_aux {k : Type u} [Field k] (d : ℕ) :
    ∀ (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.IsIntegral W] (hW : IsProperOver k W), W.dimension = d →
      ∀ (M : W.Modules) [M.IsLineBundle], AlgebraicGeometry.IsAmple M →
        0 < AlgebraicGeometry.topSelfIntersection W hW M := by
  induction d with
  | zero =>
    intro W _ _ hW hdim M _ _
    exact topSelfIntersection_pos_of_dimension_zero W hW hdim M
  | succ e ih =>
    intro W _ _ hW hdim M _ hM
    classical
    haveI hprop : AlgebraicGeometry.IsProper (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hW
    haveI : AlgebraicGeometry.IsLocallyNoetherian W := isLocallyNoetherian_of_isProperOver W hW
    -- Step 1: a section of `M^{⊗m}` not vanishing at the generic point, with affine nonvanishing locus.
    obtain ⟨m, hm, s, hηs, haff⟩ := hM.2 (genericPoint W)
    have hs0 : s ≠ 0 := by
      intro h
      apply (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus _ s _).mp hηs
      rw [h, map_zero]
      exact zero_mem _
    -- Step 2: `Z(s) ≠ ∅` (otherwise `W` is affine, hence zero-dimensional).
    have hex : ∃ w : W, w ∉ (AlgebraicGeometry.Scheme.Modules.tensorPow M m).nonvanishingLocus s := by
      by_contra hall
      push Not at hall
      haveI : AlgebraicGeometry.IsAffine W :=
        isAffine_of_forall_mem_nonvanishingLocus (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s
          haff hall
      have h0 := dimension_eq_zero_of_isAffine W hW
      omega
    obtain ⟨w, hw⟩ := hex
    have hwI : w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection
        (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s).support := by
      refine (AlgebraicGeometry.Scheme.mem_idealSheafOfSection_support_iff
        (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s w).mpr ?_
      by_contra hc
      exact hw ((AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus _ s w).mpr hc)
    -- Step 3: a coheight-one point `x₀` of `Z(s)` with positive multiplicity in `[Z(s)]_e`.
    obtain ⟨x₀, hx₀I, hx₀1⟩ := exists_mem_support_coheight_eq_one
      (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s hs0 hwI
    have hx₀pos : 0 < (AlgebraicGeometry.Scheme.idealSheafOfSection
        (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s).cycle e x₀ :=
      idealSheafOfSection_cycle_pos_of_coheight_eq_one (k := k)
        (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s hs0 e hdim hx₀I hx₀1
    -- Step 4: `c₁(M^{⊗m}) ∩ [W] = [Z(s)]_e` and its decomposition into point-closure classes.
    obtain ⟨hmem, hcap⟩ := AlgebraicGeometry.firstChernClass_cap_fundamentalClass_of_regular_section
      (k := k) (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s hs0 e hdim
    obtain ⟨S, hS, hht, hsum⟩ := effective_cycle_class_eq_sum_pointClosure W hW e _ hmem
      (idealSheafData_cycle_nonneg _ e)
    -- Step 5: `m · (M^{e+1}) = Σ_{x ∈ S} a_x · deg(c₁(M)^e ∩ ι_{x*}[W_x])`.
    have hT : (m : ℤ) * AlgebraicGeometry.topSelfIntersection W hW M =
        ∑ x ∈ S, (((AlgebraicGeometry.Scheme.idealSheafOfSection
            (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s).cycle e x).toNat : ℤ) *
          capDegree W hW M e (AlgebraicGeometry.chowPushforward (W.pointClosureι x) e
            ((W.pointClosure x).fundamentalChowClass e)) := by
      rw [topSelfIntersection_eq_capDegree_firstChernClass W hW M e hdim, ← nsmul_eq_mul,
        ← capDegree_nsmul, ← AddMonoidHom.nsmul_apply, ← firstChernClass_tensorPow_eq_nsmul W hW M e m,
        hcap, hsum, capDegree_finset_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [capDegree_nsmul, nsmul_eq_mul]
    -- Step 6: every term is positive (induction hypothesis on `W_x`).
    have hterm : ∀ x ∈ S, 0 <
        (((AlgebraicGeometry.Scheme.idealSheafOfSection
            (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s).cycle e x).toNat : ℤ) *
          capDegree W hW M e (AlgebraicGeometry.chowPushforward (W.pointClosureι x) e
            ((W.pointClosure x).fundamentalChowClass e)) := by
      intro x hx
      have hcx : 0 < (AlgebraicGeometry.Scheme.idealSheafOfSection
          (AlgebraicGeometry.Scheme.Modules.tensorPow M m) s).cycle e x :=
        lt_of_le_of_ne (idealSheafData_cycle_nonneg _ e x) (Ne.symm ((hS x).mp hx))
      refine mul_pos ?_ ?_
      · exact_mod_cast Int.lt_toNat.mpr (by simpa using hcx)
      · letI : (W.pointClosure x).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
          ⟨W.pointClosureι x ≫ (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
        haveI : (W.pointClosureι x).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
        have hWx : IsProperOver k (W.pointClosure x) :=
          inferInstanceAs (AlgebraicGeometry.IsProper
            (W.pointClosureι x ≫ (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
        have hdimx : (W.pointClosure x).dimension = e :=
          AlgebraicGeometry.Scheme.dimension_pointClosure x (hht x hx)
        rw [capDegree_chowPushforward_fundamentalChowClass W hW M e (W.pointClosure x) hWx
          (W.pointClosureι x) hdimx]
        exact ih (W.pointClosure x) hWx hdimx _
          (AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion (W.pointClosureι x) M hM)
    -- Step 7: conclude.
    have hSne : S.Nonempty := ⟨x₀, (hS x₀).mpr hx₀pos.ne'⟩
    have hpos : 0 < (m : ℤ) * AlgebraicGeometry.topSelfIntersection W hW M :=
      hT ▸ Finset.sum_pos hterm hSne
    exact pos_of_mul_pos_right hpos (by exact_mod_cast hm.le)

end MiyaokaMori.AmpleTopSelfIntersection

-- `hpos` is part of the recorded signature;
-- the proof does not need it because the induction also covers `dim V = 0`.
set_option linter.unusedVariables false in
theorem AlgebraicGeometry.topSelfIntersection_pos_of_isAmple {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) (H : X.Modules) [H.IsLineBundle]
    (hH : AlgebraicGeometry.IsAmple H)
    (V : AlgebraicGeometry.Scheme.{u}) [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ι : V ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsIntegral V]
    (hV : IsProperOver k V) (hpos : 0 < V.dimension) :
    0 < AlgebraicGeometry.topSelfIntersection V hV
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj H) :=
  MiyaokaMori.AmpleTopSelfIntersection.topSelfIntersection_pos_of_isAmple_aux V.dimension V hV rfl _
    (AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion ι H hH)

end
