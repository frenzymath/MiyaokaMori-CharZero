import Mathlib.Analysis.Polynomial.Basic
import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Cohomology.SnapperPolynomial
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.TopIntersectionFromEuler
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyZeroEquiv
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5t
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierRestrictionSequence
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearLongExact
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowMapIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberedTwistCapDegreeLeaves
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonzeroSectionRegular
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ConeScalingActionIdealSheafOfSectionLeKer
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ZeroSchemeOfCurveSectionDiscrete
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTrivialOfDiscrete

/-! # Three ingredients of "big on a fibration implies a section"

The lemma `exists_pos_section_of_topSelfIntersection_pos` of `NegativeCurveViaFibration` ("big on a fibration ⇒
there is a section") is split into three independent parts, collected in this file:

* **S3 (geometric input)** `exists_effectiveCartierDivisor_pullback_pullback_trivial`: the section of `F' := ι^*π^*A`
  pulled back from `s_A` gives an effective Cartier divisor `D` (`O_W(D) ≅ F'`) with `F'|_D` trivial. It uses the two
  general lemmas `nonempty_pullback_iso_unit_of_sectionPullbackAlong_eq_zero` (`g^*s = 0` and `A|_{Z(s)}` trivial ⇒
  `g^*A` trivial) and `nonempty_pullback_pullback_pullback_iso_unit` (triple pullback version), plus
  `sectionPullbackAlong_ne_zero`.
* **S1 (cohomological core)** `subsingleton_sheafCohomology_tensor_tensorPow_of_trivial_on_divisor`: if `B ⊗ F` is
  ample, `D` an effective Cartier divisor with `O(D) ≅ F` and `F|_D` trivial, then there is `j₀` such that for
  `j ≥ j₀`, **all** `t` and all `p ≥ 2`, `H^p(X, B^{⊗j} ⊗ F^{⊗t}) = 0`.
* **S2 (Snapper)** `exists_pos_tensorPow_section_ne_zero_of_eventually_subsingleton`: if `(L^{dim X}) > 0` and
  `H^{≥2}(L^{⊗n})` vanishes for `n ≫ 0`, some positive power has a nonzero global section. Assembled from
  `exists_pos_tensorPow_section_ne_zero_of_snapper` (with the Snapper polynomial `P` as data and the hypothesis
  `coeff_d P > 0`) and `snapper_coeff_pos_of_topSelfIntersection_pos` (`(L^d) > 0 ⇒ coeff_d P > 0`, a one-line
  consequence of `topSelfIntersection_eq_leadingCoeff`).

None of the three depends on `NegativeCurveViaFibration` (`fiberedTwist` appears only in the assembly, which is
`exists_pos_section_of_topSelfIntersection_pos` there).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.FiberedBigHasSection

open AlgebraicGeometry

/-- **Positive leading Snapper coefficient ⇒ a section**: `X` proper over `K`, `L` a line bundle, `P ∈ ℚ[x]` with
`deg P ≤ d := dim X`, `χ(X, L^p) = P(p)` for all `p ∈ ℤ` and `coeff_d P > 0`; assume moreover that there is `n₀`
such that `H^p(X, L^{⊗n}) = 0` for `n ≥ n₀` and `p ≥ 2`. Then there is `n > 0` such that `L^{⊗n}` has a nonzero global
section.

**Source**: Lazarsfeld, *Positivity in Algebraic Geometry I*, Thm 1.2.23, end of Step 1 of the proof (p. 35):
`P(n) → +∞`, and when `h^i(L^{⊗n}) = 0` for `i ≥ 2`, `χ = h⁰ − h¹ ≤ h⁰`.

**Proof**: `coeff_d P > 0` and `deg P ≤ d` give `natDegree P = d`. For `d = 0`, `P` is a positive constant; for
`d ≥ 1` the leading coefficient is positive and `P(x) → +∞` (Mathlib `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`),
so take `N` with `n ≥ N ⇒ P(n) ≥ 1`. Take `n = max (max N n₀) 1`. Then `χ(L^{⊗n}) = χ(L ^ (n:ℤ)) = P(n) > 0`
(`sheafEulerCharacteristic_zpow_nat`); by `sheafEulerCharacteristic_eq_sum`, `χ = Σ_{i ≤ d} (−1)^i h^i`, where the
terms with `i ≥ 2` vanish (hypothesis) and the term `i = 1` is `≤ 0`, so `χ ≤ h⁰` and `h⁰(L^{⊗n}) > 0`;
`exists_section_ne_zero_of_finrank_pos` (`H⁰ = Γ`) gives a nonzero section.

**Edge cases**: `d = 0` goes through the constant branch; `n₀ = 0` is allowed; `X` may be singular or non-reduced. -/
theorem exists_pos_tensorPow_section_ne_zero_of_snapper {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (L : X.Modules) [L.IsLineBundle]
    (P : Polynomial ℚ) (hPdeg : P.natDegree ≤ X.dimension)
    (hP : ∀ p : ℤ, (AlgebraicGeometry.sheafEulerCharacteristic (k := K) X (L ^ p) : ℚ) =
      P.eval (p : ℚ))
    (hcoeff : 0 < P.coeff X.dimension)
    (hvan : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℕ, 2 ≤ p →
      Subsingleton (AlgebraicGeometry.sheafCohomology X
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n) p)) :
    ∃ n : ℕ, 0 < n ∧
      ∃ σ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤), σ ≠ 0 := by
  classical
  obtain ⟨n₀, hn₀⟩ := hvan
  haveI : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hX
  haveI : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  -- 1. the leading term
  have hP0 : P ≠ 0 := fun h => by simp [h] at hcoeff
  have hnat : P.natDegree = X.dimension :=
    le_antisymm hPdeg (Polynomial.le_natDegree_of_ne_zero hcoeff.ne')
  -- 2. P(n) is eventually positive
  have hev : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < P.eval (n : ℚ) := by
    rcases Nat.eq_zero_or_pos X.dimension with hd0 | hdpos
    · refine ⟨0, fun n _ => ?_⟩
      rw [Polynomial.eq_C_of_natDegree_eq_zero (hnat.trans hd0), Polynomial.eval_C]
      rw [hd0] at hcoeff
      exact hcoeff
    · have hdeg : 0 < P.degree := by
        rw [Polynomial.degree_eq_natDegree hP0, hnat]
        exact_mod_cast hdpos
      have hlc : 0 ≤ P.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hnat]
        exact hcoeff.le
      have ht := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg P hdeg hlc
      obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp ht) 1
      obtain ⟨N', hN'⟩ := exists_nat_ge N
      refine ⟨N', fun n hn => ?_⟩
      have h1 : (1 : ℚ) ≤ P.eval (n : ℚ) := hN (n : ℚ) (hN'.trans (by exact_mod_cast hn))
      linarith
  obtain ⟨N, hN⟩ := hev
  -- 3. choose n
  refine ⟨max (max N n₀) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  set n := max (max N n₀) 1 with hn
  have hnN : N ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hnn₀ : n₀ ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  -- 4. χ(L^{⊗n}) = P(n) > 0
  have hchi : (AlgebraicGeometry.sheafEulerCharacteristic (k := K) X
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) : ℚ) = P.eval (n : ℚ) := by
    rw [← AlgebraicGeometry.Scheme.Modules.sheafEulerCharacteristic_zpow_nat K L n, hP (n : ℤ)]
    norm_cast
  have hchi_pos : 0 < AlgebraicGeometry.sheafEulerCharacteristic (k := K) X
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) := by
    have h := hN n hnN
    rw [← hchi] at h
    exact_mod_cast h
  -- 5. χ ≤ h⁰
  haveI : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).IsCoherent :=
    AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree _
  have hsum := AlgebraicGeometry.sheafEulerCharacteristic_eq_sum X hX
    (AlgebraicGeometry.Scheme.Modules.tensorPow L n)
  have hle : AlgebraicGeometry.sheafEulerCharacteristic (k := K) X
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) ≤
      (Module.finrank K (AlgebraicGeometry.sheafCohomology X
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n) 0) : ℤ) := by
    rw [hsum]
    have h0mem : (0 : ℕ) ∈ Finset.range (X.dimension + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
    calc ∑ i ∈ Finset.range (X.dimension + 1), (-1 : ℤ) ^ i *
          (Module.finrank K (AlgebraicGeometry.sheafCohomology X
            (AlgebraicGeometry.Scheme.Modules.tensorPow L n) i) : ℤ)
        ≤ ∑ i ∈ Finset.range (X.dimension + 1),
            (if i = 0 then (Module.finrank K (AlgebraicGeometry.sheafCohomology X
              (AlgebraicGeometry.Scheme.Modules.tensorPow L n) 0) : ℤ) else 0) := by
          apply Finset.sum_le_sum
          intro i _
          rcases i with _ | _ | i
          · simp
          · simp
          · haveI : Subsingleton (AlgebraicGeometry.sheafCohomology X
                (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (i + 2)) :=
              hn₀ n hnn₀ (i + 2) (by omega)
            simp [Module.finrank_zero_of_subsingleton]
      _ = _ := (Finset.sum_ite_eq' _ _ _).trans (if_pos h0mem)
  have hfin : 0 < Module.finrank K (AlgebraicGeometry.sheafCohomology X
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) 0) := by
    have h := lt_of_lt_of_le hchi_pos hle
    exact_mod_cast h
  exact AlgebraicGeometry.exists_section_ne_zero_of_finrank_pos _ hfin

/-- **Positive top self-intersection ⇒ the degree-`d` Snapper coefficient is positive** (`d = dim X`, `X` proper and
projective over `K`).

**Source**: `topSelfIntersection_eq_leadingCoeff`: `d!·coeff_d P = (L^d)`; `d! > 0` and `(L^d) > 0` give
`coeff_d P > 0`. (This one-line consequence is stated separately so that `..._of_snapper` does not depend on the
Chow side.) -/
theorem snapper_coeff_pos_of_topSelfIntersection_pos {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (hproj : IsProjectiveOver K X)
    (L : X.Modules) [L.IsLineBundle]
    (hpos : 0 < AlgebraicGeometry.topSelfIntersection X hX L)
    (P : Polynomial ℚ)
    (hP : ∀ p : ℤ, (AlgebraicGeometry.sheafEulerCharacteristic (k := K) X (L ^ p) : ℚ) =
      P.eval (p : ℚ)) :
    0 < P.coeff X.dimension := by
  have hlead : (Nat.factorial X.dimension : ℚ) * P.coeff X.dimension =
      (AlgebraicGeometry.topSelfIntersection X hX L : ℚ) :=
    topSelfIntersection_eq_leadingCoeff X hX hproj L X.dimension rfl P hP
  have hpos' : (0 : ℚ) < (AlgebraicGeometry.topSelfIntersection X hX L : ℚ) := by
    exact_mod_cast hpos
  rw [← hlead] at hpos'
  exact (mul_pos_iff_of_pos_left (by positivity)).mp hpos'

/-- **Snapper ⇒ a section**: `X` proper and projective over `K`, `L` a line bundle with `(L^{dim X}) > 0`, and there
is `n₀` such that `H^p(X, L^{⊗n}) = 0` for `n ≥ n₀` and `p ≥ 2`; then there is `n > 0` such that `L^{⊗n}` has a nonzero
global section.

**Source**: Lazarsfeld, *Positivity in Algebraic Geometry I*, Thm 1.2.23, end of Step 1 of the proof (p. 35).

**Proof**: `exists_snapper_polynomial` gives `P`; `snapper_coeff_pos_of_topSelfIntersection_pos` gives
`coeff_d P > 0`; `exists_pos_tensorPow_section_ne_zero_of_snapper` concludes. -/
theorem exists_pos_tensorPow_section_ne_zero_of_eventually_subsingleton {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (hproj : IsProjectiveOver K X)
    (L : X.Modules) [L.IsLineBundle]
    (hpos : 0 < AlgebraicGeometry.topSelfIntersection X hX L)
    (hvan : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℕ, 2 ≤ p →
      Subsingleton (AlgebraicGeometry.sheafCohomology X
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n) p)) :
    ∃ n : ℕ, 0 < n ∧
      ∃ σ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤), σ ≠ 0 := by
  obtain ⟨P, hPdeg, hP⟩ := exists_snapper_polynomial X hX L
  exact exists_pos_tensorPow_section_ne_zero_of_snapper X hX L P hPdeg hP
    (snapper_coeff_pos_of_topSelfIntersection_pos X hX hproj L hpos P hP) hvan

/-- **The restriction sequence along an effective divisor plus Serre vanishing ⇒ uniform vanishing of higher
cohomology in the powers of `F`.**

Setting: `X` proper over `K`, `B`, `F` line bundles on `X`, `A₀ := B ⊗ F` ample; `D` an effective Cartier divisor with
`O_X(D) ≅ F` and `F|_D := i^*F ≅ O_D` (`i : D → X`). Conclusion: there is `j₀` such that for all `j ≥ j₀`, **all**
`t ≥ 0` and all `p ≥ 2`, `H^p(X, B^{⊗j} ⊗ F^{⊗t}) = 0`.

**Source**: after Lazarsfeld, *Positivity in Algebraic Geometry I*, Thm 1.2.23, Step 1 (pp. 34–35), with the two
short exact sequences for `L = A − B` there replaced by the **restriction sequence along `D`**
`0 → G ⊗ O(D)^∨ → G → i_*i^*G → 0` (`EffectiveCartierDivisor.exists_shortExact_restriction`, Stacks 01WQ + 01E8);
Serre vanishing (`sheafCohomology_tensor_pow_subsingleton_of_isAmple`); the `K`-linear long exact sequence
(`sheafCohomology.equivOfSubsingletonRight`: both ends vanish ⇒ the middle terms are `K`-linearly isomorphic).

**Proof**:
1. **Serre vanishing twice** (`A₀` ample, `X` proper): for the coherent sheaf `i_*O_D` (a closed immersion is finite,
   `isCoherent_pushforward_of_isFinite`) get `j₀` with `H^q(X, i_*O_D ⊗ A₀^{⊗j}) = 0` for `j ≥ j₀`, `q ≥ 1`; for `O_X`
   get `n₀` with `H^q(X, O_X ⊗ A₀^{⊗j}) = 0` for `j ≥ n₀`, `q ≥ 1`. Put `j₀' := max j₀ n₀`.
2. **The third term is independent of `t`**: for `G := B^{⊗j} ⊗ F^{⊗t}`, `i_*i^*G ≅ i_*O_D ⊗ G` (projection formula for
   the closed immersion, `EffectiveCartierDivisor.exists_pushforwardUnit_tensor_iso_compat`), and
   `i^*G ≅ (i^*B)^{⊗j} ⊗ (i^*F)^{⊗t} ≅ (i^*B)^{⊗j} ⊗ O_D ≅ (i^*B)^{⊗j} ⊗ (i^*F)^{⊗j} ≅ i^*(A₀^{⊗j})`
   (`pullbackTensorIso`, `pullbackTensorPowIso`, `tensorPowMapIso` replacing `i^*F` by `O_D`, `tensorPowTensorIso`),
   so `i_*i^*G ≅ i_*O_D ⊗ A₀^{⊗j}`, whose `H^q` (`q ≥ 1`) vanishes for `j ≥ j₀` (step 1 and
   `sheafCohomology.subsingleton_of_iso`).
3. **One step**: `0 → G ⊗ O(D)^∨ → G → i_*i^*G → 0` with `G ⊗ O(D)^∨ ≅ B^{⊗j} ⊗ F^{⊗t} ⊗ F^∨ ≅ B^{⊗j} ⊗ F^{⊗(t−1)}`
   (`t ≥ 1`; `SheafOfModules.IsLineBundle.tensor_dual_iso`, Stacks 01CT). For `p ≥ 2` the third terms of `H^{p−1}` and
   `H^p` vanish, so `H^p(B^{⊗j} ⊗ F^{⊗(t−1)}) ≃ H^p(B^{⊗j} ⊗ F^{⊗t})` (`equivOfSubsingletonRight`).
4. **Anchor and induction**: for `t = j`, `B^{⊗j} ⊗ F^{⊗j} ≅ A₀^{⊗j} ≅ O_X ⊗ A₀^{⊗j}` and `H^p = 0` (second part of
   step 1, `j ≥ n₀`). Inducting with step 3 downwards (`t = j, j−1, …, 0`) and upwards (`t = j, j+1, …`) gives the
   vanishing for all `t`.

**Edge cases**: `j₀' ≥ 1` is not needed; `t = 0` is the end of the descent; `D` may be non-reduced or reducible (only the
coherence of `i_*O_D` and the triviality of `F|_D` are used); `X` need not be integral. `p ≥ 2` is necessary (for `p = 1`
the third term `H^0(i_*i^*G)` does not vanish).

Two remarks on the formal proof: in step 2, `G ⊗ O(D)^∨ ≅ B^{⊗j} ⊗ F^{⊗(t−1)}` is obtained without `dualMapIso`, by
replacing the rightmost factor `F` by `O(D)` via `eD.symm` and applying `tensor_dual_iso O(D)`; the coherence of `O_D`
and `O_X` comes from the quasi-coherence of `IsLineBundle.unit` plus the finite-type instances, and that of `i_*O_D` from
`isCoherent_pushforward_of_isFinite` (a closed immersion is finite; `X` is locally Noetherian since proper). -/
theorem subsingleton_sheafCohomology_tensor_tensorPow_of_trivial_on_divisor {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X)
    (B F : X.Modules) [B.IsLineBundle] [F.IsLineBundle]
    (hA : AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor B F))
    (D : AlgebraicGeometry.EffectiveCartierDivisor X)
    (eD : Nonempty (D.lineBundle ≅ F))
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback D.idealSheaf.subschemeι).obj F ≅
      SheafOfModules.unit D.idealSheaf.subscheme.ringCatSheaf)) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t p : ℕ, 2 ≤ p →
      Subsingleton (AlgebraicGeometry.sheafCohomology X
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.tensorPow B j)
          (AlgebraicGeometry.Scheme.Modules.tensorPow F t)) p) := by
  classical
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hX
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  set i := D.idealSheaf.subschemeι with hidef
  set A₀ := AlgebraicGeometry.Scheme.Modules.tensor B F with hA₀
  -- coherence of `O_D`, `i_*O_D`, `O_X`
  have : AlgebraicGeometry.IsFinite i :=
    ((AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
  have hOD : AlgebraicGeometry.Scheme.Modules.IsCoherent
      (SheafOfModules.unit D.idealSheaf.subscheme.ringCatSheaf) :=
    ⟨inferInstance, inferInstance⟩
  set P : X.Modules := (AlgebraicGeometry.Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit D.idealSheaf.subscheme.ringCatSheaf) with hPdef
  have hP : P.IsCoherent := AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite i _
  have hO : AlgebraicGeometry.Scheme.Modules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    ⟨inferInstance, inferInstance⟩
  -- Serre vanishing twice
  obtain ⟨j₀, hj₀⟩ := AlgebraicGeometry.sheafCohomology_tensor_pow_subsingleton_of_isAmple X hX A₀ hA P
  obtain ⟨n₀, hn₀⟩ := AlgebraicGeometry.sheafCohomology_tensor_pow_subsingleton_of_isAmple X hX A₀ hA
    (SheafOfModules.unit X.ringCatSheaf)
  refine ⟨max j₀ n₀, fun j hj t p hp => ?_⟩
  have hjj₀ : j₀ ≤ j := le_trans (le_max_left _ _) hj
  have hjn₀ : n₀ ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨eF⟩ := htriv
  obtain ⟨eD⟩ := eD
  -- notation `G t := B^{⊗j} ⊗ F^{⊗t}`
  let G : ℕ → X.Modules := fun t => AlgebraicGeometry.Scheme.Modules.tensor
    (AlgebraicGeometry.Scheme.Modules.tensorPow B j) (AlgebraicGeometry.Scheme.Modules.tensorPow F t)
  -- (a) `i^*(G t) ≅ (i^*B)^{⊗j}` for every `t`
  let ε : ∀ t, (AlgebraicGeometry.Scheme.Modules.pullback i).obj (G t) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback i).obj B) j :=
    fun t =>
      AlgebraicGeometry.Scheme.Modules.pullbackTensorIso i _ _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoLeft
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso i B j) _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoRight _
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso i F t ≪≫
          AlgebraicGeometry.Scheme.Modules.tensorPowMapIso eF t ≪≫
          AlgebraicGeometry.Scheme.Modules.unitTensorPowIso _ t) ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorUnitIso _
  -- (b) third term of the restriction sequence `≅ i_*O_D ⊗ A₀^{⊗j}` for every `t`
  obtain ⟨ePF, -⟩ := AlgebraicGeometry.EffectiveCartierDivisor.exists_pushforwardUnit_tensor_iso_compat D
    (AlgebraicGeometry.Scheme.Modules.tensorPow A₀ j)
  let third : ∀ t, (AlgebraicGeometry.Scheme.Modules.pushforward i).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (G t)) ≅
      AlgebraicGeometry.Scheme.Modules.tensor P (AlgebraicGeometry.Scheme.Modules.tensorPow A₀ j) :=
    fun t =>
      (AlgebraicGeometry.Scheme.Modules.pushforward i).mapIso
        (ε t ≪≫ (ε j).symm ≪≫
          ((AlgebraicGeometry.Scheme.Modules.pullback i).mapIso
            (AlgebraicGeometry.Scheme.Modules.tensorPowTensorIso B F j)).symm) ≪≫
      ePF.symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj P _).symm
  -- (c) its cohomology vanishes in degrees `q ≥ 1`
  have hthird : ∀ t q, 0 < q → Subsingleton (AlgebraicGeometry.sheafCohomology X
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (G t))) q) := fun t q hq =>
    have : Subsingleton (AlgebraicGeometry.sheafCohomology X
        (AlgebraicGeometry.Scheme.Modules.tensor P (AlgebraicGeometry.Scheme.Modules.tensorPow A₀ j)) q) :=
      hj₀ j hjj₀ q hq
    AlgebraicGeometry.sheafCohomology.subsingleton_of_iso (third t) q
  -- (d) one step in `t`
  obtain ⟨eDd⟩ := SheafOfModules.IsLineBundle.tensor_dual_iso D.lineBundle
  have hstep : ∀ t, Subsingleton (AlgebraicGeometry.sheafCohomology X (G t) p) ↔
      Subsingleton (AlgebraicGeometry.sheafCohomology X (G (t + 1)) p) := by
    intro t
    obtain ⟨f, w, hS⟩ := AlgebraicGeometry.EffectiveCartierDivisor.exists_shortExact_restriction D (G (t + 1))
    have : Subsingleton (AlgebraicGeometry.sheafCohomology X
        ((AlgebraicGeometry.Scheme.Modules.pullback i ⋙ AlgebraicGeometry.Scheme.Modules.pushforward i).obj
          (G (t + 1))) (p - 1)) :=
      hthird (t + 1) (p - 1) (by omega)
    have : Subsingleton (AlgebraicGeometry.sheafCohomology X
        ((AlgebraicGeometry.Scheme.Modules.pullback i ⋙ AlgebraicGeometry.Scheme.Modules.pushforward i).obj
          (G (t + 1))) p) :=
      hthird (t + 1) p (by omega)
    have e := AlgebraicGeometry.sheafCohomology.equivOfSubsingletonRight hS (p - 1) p (by omega) K
    -- `G (t+1) ⊗ O(D)^∨ ≅ G t`
    let e₁ : AlgebraicGeometry.Scheme.Modules.tensor (G (t + 1))
        (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle) ≅ G t :=
      AlgebraicGeometry.Scheme.Modules.tensorIsoLeft
        (AlgebraicGeometry.Scheme.Modules.tensorIsoRight (AlgebraicGeometry.Scheme.Modules.tensorPow B j)
          (AlgebraicGeometry.Scheme.Modules.tensorIsoRight (AlgebraicGeometry.Scheme.Modules.tensorPow F t)
            eD.symm)) _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorAssocIso _ _ _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoRight _
        (AlgebraicGeometry.Scheme.Modules.tensorAssocIso _ _ _ ≪≫
          AlgebraicGeometry.Scheme.Modules.tensorIsoRight _ eDd ≪≫
          AlgebraicGeometry.Scheme.Modules.tensorUnitIso _)
    constructor
    · intro h
      have := h
      have : Subsingleton (AlgebraicGeometry.sheafCohomology X
          (AlgebraicGeometry.Scheme.Modules.tensor (G (t + 1))
            (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle)) p) :=
        AlgebraicGeometry.sheafCohomology.subsingleton_of_iso e₁ p
      exact e.symm.toEquiv.subsingleton
    · intro h
      have := h
      have : Subsingleton (AlgebraicGeometry.sheafCohomology X
          (AlgebraicGeometry.Scheme.Modules.tensor (G (t + 1))
            (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle)) p) :=
        e.toEquiv.subsingleton
      exact AlgebraicGeometry.sheafCohomology.subsingleton_of_iso e₁.symm p
  -- (e) anchor `t = j`
  have hanchor : Subsingleton (AlgebraicGeometry.sheafCohomology X (G j) p) := by
    have : Subsingleton (AlgebraicGeometry.sheafCohomology X
        (AlgebraicGeometry.Scheme.Modules.tensor (SheafOfModules.unit X.ringCatSheaf)
          (AlgebraicGeometry.Scheme.Modules.tensorPow A₀ j)) p) :=
      hn₀ j hjn₀ p (by omega)
    exact AlgebraicGeometry.sheafCohomology.subsingleton_of_iso
      ((AlgebraicGeometry.Scheme.Modules.tensorPowTensorIso B F j).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.unitTensorIso _).symm) p
  -- (f) all `t` are equivalent
  have hall : ∀ t, Subsingleton (AlgebraicGeometry.sheafCohomology X (G t) p) ↔
      Subsingleton (AlgebraicGeometry.sheafCohomology X (G 0) p) := by
    intro t
    induction t with
    | zero => exact Iff.rfl
    | succ t ih => exact (hstep t).symm.trans ih
  exact (hall t).2 ((hall j).1 hanchor)

/-- **Triviality descends along morphisms factoring through the zero scheme**: `g : Z → C`, `A` a line bundle on `C`,
`s ∈ Γ(C, A)` with `g^*s = 0` and `A|_{Z(s)} ≅ O_{Z(s)}` (`j : Z(s) → C`); then `g^*A ≅ O_Z`.

**Source**: Stacks 02OR (universal property of the zero scheme) and Mathlib `IsClosedImmersion.lift` (lifting along a
closed immersion).

**Proof**: `g^*s = 0 ⇔ Z(s) ≤ g.ker` (`idealSheafOfSection_le_ker_iff`) and `j.ker = Z(s)` (Mathlib `ker_subschemeι`),
so `j.ker ≤ g.ker` and Mathlib's `IsClosedImmersion.lift j g` gives `g' : Z → Z(s)` with `g' ≫ j = g` (`lift_fac`). Hence
`g^*A ≅ (g' ≫ j)^*A ≅ g'^*(j^*A) ≅ g'^*O ≅ O_Z` (`pullbackCongr`, `pullbackComp`, `pullbackUnitIso`).

**Edge cases**: for `Z = ∅` the conclusion is trivial; for `s = 0`, `Z(s) = C` and `g' = g`, and the claim still holds. -/
theorem nonempty_pullback_iso_unit_of_sectionPullbackAlong_eq_zero {Z C : AlgebraicGeometry.Scheme.{u}}
    (g : Z ⟶ C) (A : C.Modules) [A.IsLineBundle] (s : Γ(A, ⊤))
    (hg : sectionPullbackAlong g s = 0)
    (e : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.idealSheafOfSection A s).subschemeι).obj A ≅
      SheafOfModules.unit (AlgebraicGeometry.Scheme.idealSheafOfSection A s).subscheme.ringCatSheaf)) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  set J := AlgebraicGeometry.Scheme.idealSheafOfSection A s with hJdef
  have hJ : J ≤ g.ker := (AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff g A s).mpr hg
  have hker : J.subschemeι.ker ≤ g.ker := by
    rw [J.ker_subschemeι]
    exact hJ
  let g' : Z ⟶ J.subscheme := AlgebraicGeometry.IsClosedImmersion.lift J.subschemeι g hker
  have hfac : g' ≫ J.subschemeι = g := AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  obtain ⟨e⟩ := e
  exact ⟨(AlgebraicGeometry.Scheme.Modules.pullbackCongr hfac.symm).app A ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp g' J.subschemeι).app A).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback g').mapIso e ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g'⟩

/-- **Triple pullback version**: for `i : Z → W`, `ι : W → V`, `π : V → C`, if `i^*ι^*π^*s = 0` and `A|_{Z(s)}` is trivial,
then `i^*ι^*π^*A ≅ O_Z`. Reduce with `sectionPullbackAlong_comp_eq_zero_iff` (twice) to `((i ≫ ι) ≫ π)^*s = 0`, apply
the previous lemma, and use `pullbackComp` (twice) to turn `((i ≫ ι) ≫ π)^*A` back into `i^*ι^*π^*A`. -/
theorem nonempty_pullback_pullback_pullback_iso_unit {Z W V C : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ W) (ι : W ⟶ V) (π : V ⟶ C) (A : C.Modules) [A.IsLineBundle] (s : Γ(A, ⊤))
    (h0 : sectionPullbackAlong i (sectionPullbackAlong ι (sectionPullbackAlong π s)) = 0)
    (e : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.idealSheafOfSection A s).subschemeι).obj A ≅
      SheafOfModules.unit (AlgebraicGeometry.Scheme.idealSheafOfSection A s).subscheme.ringCatSheaf)) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A)) ≅
      SheafOfModules.unit Z.ringCatSheaf) := by
  have h1 : sectionPullbackAlong ((i ≫ ι) ≫ π) s = 0 :=
    (sectionPullbackAlong_comp_eq_zero_iff (i ≫ ι) π s).mpr
      ((sectionPullbackAlong_comp_eq_zero_iff i ι (sectionPullbackAlong π s)).mpr h0)
  obtain ⟨e'⟩ := nonempty_pullback_iso_unit_of_sectionPullbackAlong_eq_zero ((i ≫ ι) ≫ π) A s h1 e
  exact ⟨(AlgebraicGeometry.Scheme.Modules.pullbackComp i ι).app
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp (i ≫ ι) π).app A ≪≫ e'⟩

/-- **Geometric input**: if `ρ := ι ≫ π : W → C` is nonconstant, the section of `F' := ι^*π^*A` pulled back from `s_A`
defines an effective Cartier divisor `D` (`O_W(D) ≅ F'`) with `F'|_D` trivial.

**Source**: `range_closedPoint_or_surjective`, `isRegular_germ_of_ne_zero`,
`exists_effectiveCartierDivisor_of_regular_section` (Stacks 01X0), `lineBundle_trivial_on_zeroScheme`,
Mathlib `Scheme.Hom.ker` / `Hom.toImage` / `IdealSheafData.subschemeι` (universal property of closed subschemes).

**Proof**:
1. `ρ` is surjective: `W` integral and proper ⇒ the image is irreducible and closed; `hns` excludes a single point, and
   `range_closedPoint_or_surjective` gives surjectivity.
2. `σ := sectionPullbackAlong ρ s_A ∈ Γ(W, ρ^*A)` is nonzero (transported to `F' = ι^*π^*A` via `pullbackComp`):
   `ρ` dominant ⇒ `ρ(η_W) = η_C`; the germ of `σ` at `η_W` is the image of the germ of `s_A` at `η_C` (nonzero: on an
   integral scheme a nonzero section has nonzero germ at the generic point) under the stalk map
   `A_{η_C} → (ρ^*A)_{η_W} = A_{η_C} ⊗_{κ(C)} κ(W)`, the base change of a one-dimensional `κ(C)`-space along a field
   extension, which is injective. This is `FiberedTwistCapDegreeLeaves.sectionPullbackAlong_ne_zero` (`ρ` surjective ⇒
   `η_W ↦ η_C ∉ supp Z(s_A)` ⇒ nonzero germ).
3. `W` integral ⇒ `σ` is regular (`isRegular_germ_of_ne_zero`); `exists_effectiveCartierDivisor_of_regular_section` gives
   `D` with `D.idealSheaf = idealSheafOfSection F' σ` and `O_W(D) ≅ F'`.
4. **`F'|_D` is trivial**: let `Z_C := Z(s_A) ⊂ C` (`idealSheafOfSection A s_A`), `j : Z_C → C`. The morphism
   `g := D.idealSheaf.subschemeι ≫ ρ : D → C` factors through `Z_C`: it suffices that `idealSheafOfSection A s_A ≤ g.ker`
   (`s_A^∨(φ)` pulls back to `σ^∨(ρ^*φ) ∈ I_D`, computed locally in frames), which gives `g' : D → Z_C` with `g' ≫ j = g`
   (Mathlib `Hom.toImage` and the morphism of closed subschemes given by an inclusion of ideal sheaves). Then
   `i^*F' = i^*ι^*π^*A ≅ g^*A = (g' ≫ j)^*A ≅ g'^*(j^*A) ≅ g'^*O_{Z_C} ≅ O_D`
   (`lineBundle_trivial_on_zeroScheme` gives `j^*A ≅ O_{Z_C}`; `pullbackComp`, `pullbackUnitIso`).
   The inclusion of ideal sheaves `idealSheafOfSection A s_A ≤ (i ≫ ρ).ker` of step 4 is
   `idealSheafOfSection_le_ker_iff` together with `sectionPullbackAlong_comp_eq_zero_iff` (Stacks 02OR):
   `i^*σ = 0` (`D.idealSheaf = Z(σ)`, `ker_subschemeι`) ⇒ `((i ≫ ι) ≫ π)^*s_A = 0` ⇒ the inclusion; `g'` comes from
   Mathlib's `IsClosedImmersion.lift`. These two steps are the two general lemmas above.

**Edge cases**: if `Z(s_A) = ∅` then `σ` is nowhere zero and `D = ∅` (every line bundle on the empty scheme is
trivial, so the claim still holds); `Z(s_A)` may consist of several points and be non-reduced; `W` may be singular;
`K` need not be algebraically closed. -/
theorem exists_effectiveCartierDivisor_pullback_pullback_trivial {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K}
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (A : C.toScheme.Modules) [A.IsLineBundle] (sA : Γ(A, ⊤)) (hsA : sA ≠ 0)
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W)
    (hns : ¬ ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c}) :
    ∃ D : AlgebraicGeometry.EffectiveCartierDivisor W,
      Nonempty (D.lineBundle ≅
        (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A)) ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback D.idealSheaf.subschemeι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A)) ≅
        SheafOfModules.unit D.idealSheaf.subscheme.ringCatSheaf) := by
  have hsurj : Function.Surjective (ι ≫ π).base :=
    MiyaokaMori.FiberedTwistCapDegreeLeaves.surjective_of_not_range_singleton π W ι hW hns
  set F' : W.Modules := (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) with hF'
  set σ : Γ(F', ⊤) := sectionPullbackAlong ι (sectionPullbackAlong π sA) with hσdef
  have hσ : σ ≠ 0 :=
    MiyaokaMori.FiberedTwistCapDegreeLeaves.sectionPullbackAlong_ne_zero π W ι A sA hsA hsurj
  obtain ⟨D, hD, eD⟩ := AlgebraicGeometry.exists_effectiveCartierDivisor_of_regular_section F' σ
    (isRegular_germ_of_ne_zero F' σ hσ)
  refine ⟨D, eD, ?_⟩
  have h0 : sectionPullbackAlong D.idealSheaf.subschemeι σ = 0 :=
    (AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff D.idealSheaf.subschemeι F' σ).mp
      (hD.ge.trans D.idealSheaf.ker_subschemeι.ge)
  have := MiyaokaMori.ZeroSchemeOfCurveSectionDiscrete.discreteTopology_zeroScheme C A sA hsA
  exact nonempty_pullback_pullback_pullback_iso_unit D.idealSheaf.subschemeι ι π A sA h0
    (MiyaokaMori.LineBundleTrivialOfDiscrete.nonempty_iso_unit_of_discreteTopology _)

end MiyaokaMori.FiberedBigHasSection

end
