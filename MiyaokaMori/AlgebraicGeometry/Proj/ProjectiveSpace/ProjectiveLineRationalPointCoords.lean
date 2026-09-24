import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLinePointZero
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLinePointCoordinates
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineBasicOpenExt
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Homogeneous coordinates of rational points of the projective line

Over an algebraically closed field every closed point of `P¹_k` has homogeneous coordinates:
`p = [v₀ : v₁]` with `v ≠ 0`, i.e. `p` corresponds to the homogeneous prime ideal
`(v₁X₀ − v₀X₁)`. This is used to parametrize a rational curve by `P¹` sending `0` to a chosen
point (Lemma 5.1 of the paper).

Everything is spelled over `ProjectiveLine k` and `ProjectiveSpace.toSpecBase 1 k`; a `k`-point is
passed to the chart API as `⟨p, hp⟩` with `p : Spec k ⟶ ProjectiveLine k` and
`hp : p ≫ ProjectiveSpace.toSpecBase 1 k = 𝟙 _`. Properness comes from
`ProjectiveSpace.isProper_toSpecBase`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry AlgebraicGeometry.Proj HomogeneousLocalization
open AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates

set_option backward.isDefEq.respectTransparency false in
private theorem chart_preimage_basicOpen_coords
    {k : Type u} [Field k] (i : Fin 2) {n : ℕ} (hn : 0 < n)
    {f : MvPolynomial (Fin 2) k} (hf : f.IsHomogeneous n) :
    AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.chartι (k := k) i ⁻¹ᵁ
        Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) f =
      PrimeSpectrum.basicOpen
        (AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.dehomogenization (k := k) i f) := by
  have hX : MvPolynomial.X i ∈ AlgebraicGeometry.Proj.projectiveGrading k 1 1 :=
    MvPolynomial.isHomogeneous_X k i
  have hf' : f ∈ AlgebraicGeometry.Proj.projectiveGrading k 1 n := hf
  have hloc : Away.isLocalizationElem hX hf' =
      AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.dehomogenization (k := k) i f := by
    rw [dehomogenization_of_homogeneous i hf]
    apply HomogeneousLocalization.val_injective
    change Localization.mk (f ^ 1)
        (⟨MvPolynomial.X i ^ n, n, rfl⟩ :
          Submonoid.powers (MvPolynomial.X (R := k) i)) =
      Localization.mk f
        (⟨MvPolynomial.X i ^ n, n, rfl⟩ :
          Submonoid.powers (MvPolynomial.X (R := k) i))
    simp only [pow_one]
  exact (Proj.awayι_preimage_basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1)
    hX (by decide : 0 < 1) hf' hn).trans
    (congrArg PrimeSpectrum.basicOpen hloc)

set_option backward.isDefEq.respectTransparency false in
private theorem rationalPoint_preimage_basicOpen_coords
    {k : Type u} [Field k]
    (p : Spec (CommRingCat.of k) ⟶ ProjectiveLine k)
    (hp : p ≫ ProjectiveSpace.toSpecBase 1 k = 𝟙 _) (i : Fin 2)
    (hi : p (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) (MvPolynomial.X i))
    {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous n) :
    p ⁻¹ᵁ Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) f =
      PrimeSpectrum.basicOpen
        (MvPolynomial.eval (normalizedCoordinates ⟨p, hp⟩ i hi) f) := by
  have hfac : Spec.map (CommRingCat.ofHom (chartEvaluation ⟨p, hp⟩ i hi)) ≫
      chartι (k := k) i = p :=
    chartEvaluation_fac ⟨p, hp⟩ i hi
  conv_lhs => rw [← hfac]
  rw [Scheme.Hom.comp_preimage,
    chart_preimage_basicOpen_coords i hn hf, SpecMap_preimage_basicOpen]
  exact congrArg PrimeSpectrum.basicOpen
    (RingHom.congr_fun (chartEvaluation_dehomogenization ⟨p, hp⟩ i hi) f)

set_option backward.isDefEq.respectTransparency false in
private theorem rationalPoint_mem_basicOpen_coords
    {k : Type u} [Field k]
    (p : Spec (CommRingCat.of k) ⟶ ProjectiveLine k)
    (hp : p ≫ ProjectiveSpace.toSpecBase 1 k = 𝟙 _) (i : Fin 2)
    (hi : p (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) (MvPolynomial.X i))
    {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous n) :
    p (IsLocalRing.closedPoint k) ∈
        Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) f ↔
      MvPolynomial.eval (normalizedCoordinates ⟨p, hp⟩ i hi) f ≠ 0 := by
  change IsLocalRing.closedPoint k ∈
      p ⁻¹ᵁ Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) f ↔ _
  rw [rationalPoint_preimage_basicOpen_coords p hp i hi hn hf]
  rw [PrimeSpectrum.mem_basicOpen]
  simp only [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot,
    Ideal.mem_bot, not_false_eq_true]

private lemma coordsLinear_support_nonempty {k : Type u} [Field k]
    (v : Fin 2 → k) (hv : v ≠ 0) :
    (Finsupp.single (0 : Fin 2) (v 1) +
      Finsupp.single (1 : Fin 2) (-v 0)).support.Nonempty := by
  rw [Finsupp.support_nonempty_iff]
  intro h
  have h0 := congrArg (fun c : Fin 2 →₀ k => c 0) h
  have h1 := congrArg (fun c : Fin 2 →₀ k => c 1) h
  simp at h0 h1
  apply hv
  funext i
  fin_cases i <;> simp [h0, h1]

private lemma coordsLinear_isPrimitive {k : Type u} [Field k]
    (v : Fin 2 → k) (hv : v ≠ 0) :
    ∀ r : k, (∀ i : Fin 2,
      r ∣ (Finsupp.single (0 : Fin 2) (v 1) +
        Finsupp.single (1 : Fin 2) (-v 0)) i) → IsUnit r := by
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    have h0 := hr 0
    have h1 := hr 1
    simp only [zero_dvd_iff] at h0 h1
    have hv0 : v 1 = 0 := by simpa using h0
    have hv1 : v 0 = 0 := by simpa using h1
    exact False.elim (hv (by
      funext i
      fin_cases i <;> simp [hv0, hv1]))
  · exact isUnit_iff_ne_zero.mpr hr0

/- The point with homogeneous coordinates `v`: the homogeneous prime ideal `(v 1 • X 0 - v 0 • X 1)`,
   given directly as an element of the projective spectrum, in the same way as `ProjectiveLine.zero`. -/

noncomputable def ProjectiveLine.ofCoords {k : Type u} [Field k] (v : Fin 2 → k) (hv : v ≠ 0) :
    ProjectiveLine k :=
  (⟨⟨Ideal.span {v 1 • MvPolynomial.X (0 : Fin 2) - v 0 • MvPolynomial.X (1 : Fin 2)},
      Ideal.homogeneous_span _ _ (by
        rintro _ rfl
        exact ⟨1, Submodule.sub_mem _
          (Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k 0)))
          (Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k 1)))⟩)⟩,
    (by
      change (Ideal.span
        ({v 1 • MvPolynomial.X (0 : Fin 2) -
          v 0 • MvPolynomial.X (1 : Fin 2)} :
            Set (MvPolynomial (Fin 2) k))).IsPrime
      have heq : MvPolynomial.sumSMulX
          (Finsupp.single (0 : Fin 2) (v 1) +
            Finsupp.single (1 : Fin 2) (-v 0)) =
          v 1 • MvPolynomial.X (0 : Fin 2) -
            v 0 • MvPolynomial.X (1 : Fin 2) := by
        have hs : Finsupp.single (1 : Fin 2) (-v 0) =
            -Finsupp.single (1 : Fin 2) (v 0) := by
          ext i
          fin_cases i <;> simp
        rw [hs, map_add, map_neg]
        simp [MvPolynomial.sumSMulX, Finsupp.linearCombination_apply, sub_eq_add_neg]
      let c : Fin 2 →₀ k := Finsupp.single (0 : Fin 2) (v 1) +
        Finsupp.single (1 : Fin 2) (-v 0)
      have hc : c.support.Nonempty := by
        simpa [c] using coordsLinear_support_nonempty v hv
      have hg : ∀ r, (∀ i, r ∣ c i) → IsUnit r := by
        simpa [c] using coordsLinear_isPrimitive v hv
      have hirr : Irreducible (MvPolynomial.sumSMulX c) :=
        MvPolynomial.irreducible_sumSMulX c hc hg
      have hprime : (Ideal.span
          ({MvPolynomial.sumSMulX c} : Set (MvPolynomial (Fin 2) k))).IsPrime :=
        (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
      have heqc : MvPolynomial.sumSMulX c =
          v 1 • MvPolynomial.X (0 : Fin 2) -
            v 0 • MvPolynomial.X (1 : Fin 2) := by
        simpa [c] using heq
      rw [heqc] at hprime
      exact hprime),
    (by
      intro hle
      have h0irr : MvPolynomial.X (0 : Fin 2) ∈
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toIdeal := by
        exact HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
          (MvPolynomial.isHomogeneous_X k 0)
      have h1irr : MvPolynomial.X (1 : Fin 2) ∈
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toIdeal := by
        exact HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
          (MvPolynomial.isHomogeneous_X k 1)
      have h0 := hle h0irr
      have h1 := hle h1irr
      have hell : MvPolynomial.eval v
          (v 1 • MvPolynomial.X (0 : Fin 2) -
            v 0 • MvPolynomial.X (1 : Fin 2)) = 0 := by
        simp [MvPolynomial.eval, sub_eq_add_neg]
        ring
      have hker : Ideal.span
          ({v 1 • MvPolynomial.X (0 : Fin 2) -
            v 0 • MvPolynomial.X (1 : Fin 2)} :
              Set (MvPolynomial (Fin 2) k)) ≤
            RingHom.ker (MvPolynomial.eval v) := by
        rw [Ideal.span_le]
        intro z hz
        rcases hz with rfl
        exact hell
      have e0 : v 0 = 0 := by
        have := hker h0
        simpa using this
      have e1 : v 1 = 0 := by
        have := hker h1
        simpa using this
      exact hv (by
        funext i
        fin_cases i <;> simp [e0, e1]))⟩ :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 2) k))

theorem ProjectiveLine.ofCoords_zero {k : Type u} [Field k] :
    ProjectiveLine.ofCoords ![0, 1] (by simp) = ProjectiveLine.zero k := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  simp [ProjectiveLine.ofCoords, ProjectiveLine.zero] at hp ⊢

private lemma span_mem_case1 {k : Type u} [Field k] (t : k)
    {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous n)
    (hzero : MvPolynomial.eval ![t, 1] f = 0) :
    f ∈ Ideal.span ({MvPolynomial.X (0 : Fin 2) - MvPolynomial.C t *
      MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) := by
  let I : Ideal (MvPolynomial (Fin 2) k) :=
    Ideal.span ({MvPolynomial.X (0 : Fin 2) - MvPolynomial.C t *
      MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k))
  have hmon : ∀ (d : Fin 2 →₀ ℕ) (r : k), d.degree = n →
      MvPolynomial.monomial d r -
          MvPolynomial.C (MvPolynomial.eval ![t, 1] (MvPolynomial.monomial d r)) *
            MvPolynomial.X (1 : Fin 2) ^ n ∈ I := by
    intro d r hd
    have hdeg : d 0 + d 1 = n := by
      rw [Finsupp.degree_eq_weight_one] at hd
      rw [Finsupp.weight_apply,
        Finsupp.sum_fintype _ _ (by intro i; simp), Fin.sum_univ_two] at hd
      simpa using hd
    have hpow : MvPolynomial.X (0 : Fin 2) - MvPolynomial.C t *
        MvPolynomial.X (1 : Fin 2) ∣
        MvPolynomial.X (0 : Fin 2) ^ (d 0) -
          (MvPolynomial.C t * MvPolynomial.X (1 : Fin 2)) ^ (d 0) := by
      simpa using (sub_dvd_pow_sub_pow (MvPolynomial.X (0 : Fin 2) (R := k))
        (MvPolynomial.C t * MvPolynomial.X (1 : Fin 2)) (d 0))
    have hpowI : MvPolynomial.X (0 : Fin 2) ^ (d 0) -
          (MvPolynomial.C t * MvPolynomial.X (1 : Fin 2)) ^ (d 0) ∈ I :=
      Ideal.mem_span_singleton.mpr hpow
    have hmul : MvPolynomial.C r * MvPolynomial.X (1 : Fin 2) ^ (d 1) *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0) -
            (MvPolynomial.C t * MvPolynomial.X (1 : Fin 2)) ^ (d 0)) ∈ I := by
      exact I.mul_mem_left _ hpowI
    have hEq : MvPolynomial.monomial d r -
          MvPolynomial.C (MvPolynomial.eval ![t, 1] (MvPolynomial.monomial d r)) *
            MvPolynomial.X (1 : Fin 2) ^ n =
        MvPolynomial.C r * MvPolynomial.X (1 : Fin 2) ^ (d 1) *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0) -
            (MvPolynomial.C t * MvPolynomial.X (1 : Fin 2)) ^ (d 0)) := by
      rw [MvPolynomial.eval_monomial]
      have hp : d.prod (fun i e => ![t, 1] i ^ e) =
          t ^ d 0 * (1 : k) ^ d 1 := by
        calc
          d.prod (fun i e => ![t, 1] i ^ e) =
              ∏ x ∈ Finset.univ, ![t, 1] x ^ d x := by
                apply Finsupp.prod_of_support_subset
                · exact Finset.subset_univ _
                · intro i _
                  simp
          _ = t ^ d 0 * (1 : k) ^ d 1 := by
                rw [Fin.prod_univ_two]
                rfl
      rw [hp]
      simp only [one_pow, mul_one]
      rw [MvPolynomial.monomial_eq]
      have hx : d.prod (fun i e => MvPolynomial.X (R := k) i ^ e) =
          MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1 := by
        calc
          d.prod (fun i e => MvPolynomial.X (R := k) i ^ e) =
              ∏ x ∈ Finset.univ, MvPolynomial.X (R := k) x ^ d x := by
                apply Finsupp.prod_of_support_subset
                · exact Finset.subset_univ _
                · intro i _
                  simp
          _ = _ := by rw [Fin.prod_univ_two]
      rw [hx]
      ring_nf
      rw [← hdeg, pow_add]
      simp only [map_pow, MvPolynomial.C_mul]
      ring
    rw [hEq]
    exact hmul
  have haux : ∀ (g : MvPolynomial (Fin 2) k), g.IsHomogeneous n →
      g - MvPolynomial.C (MvPolynomial.eval ![t, 1] g) *
        MvPolynomial.X (1 : Fin 2) ^ n ∈ I := by
    intro g hg
    induction hg using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp [I]
    | add p q hp hq ihp ihq =>
        have hh := I.add_mem ihp ihq
        simpa [map_add, sub_eq_add_neg, add_mul, add_assoc, add_left_comm, add_comm] using hh
    | monomial d r hd =>
        have hdeg : d.degree = n := by
          simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
        exact hmon d r hdeg
  have hmem := haux f hf
  have hlast : MvPolynomial.C (MvPolynomial.eval ![t, 1] f) *
      MvPolynomial.X (1 : Fin 2) ^ n ∈ I := by
    rw [hzero]
    simp
  have := I.add_mem hmem hlast
  simpa [I] using this

private lemma span_mem_case0 {k : Type u} [Field k] (t : k)
    {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous n)
    (hzero : MvPolynomial.eval ![1, t] f = 0) :
    f ∈ Ideal.span ({MvPolynomial.C t * MvPolynomial.X (0 : Fin 2) -
      MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) := by
  let I : Ideal (MvPolynomial (Fin 2) k) :=
    Ideal.span ({MvPolynomial.C t * MvPolynomial.X (0 : Fin 2) -
      MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k))
  have hmon : ∀ (d : Fin 2 →₀ ℕ) (r : k), d.degree = n →
      MvPolynomial.monomial d r -
          MvPolynomial.C (MvPolynomial.eval ![1, t] (MvPolynomial.monomial d r)) *
            MvPolynomial.X (0 : Fin 2) ^ n ∈ I := by
    intro d r hd
    have hdeg : d 0 + d 1 = n := by
      rw [Finsupp.degree_eq_weight_one] at hd
      rw [Finsupp.weight_apply,
        Finsupp.sum_fintype _ _ (by intro i; simp), Fin.sum_univ_two] at hd
      simpa using hd
    have hpow : MvPolynomial.C t * MvPolynomial.X (0 : Fin 2) -
        MvPolynomial.X (1 : Fin 2) ∣
        MvPolynomial.X (1 : Fin 2) ^ (d 1) -
          (MvPolynomial.C t * MvPolynomial.X (0 : Fin 2)) ^ (d 1) := by
      have h := sub_dvd_pow_sub_pow (MvPolynomial.X (1 : Fin 2) (R := k))
        (MvPolynomial.C t * MvPolynomial.X (0 : Fin 2)) (d 1)
      rw [show MvPolynomial.C t * MvPolynomial.X (0 : Fin 2) -
        MvPolynomial.X (1 : Fin 2) =
        -(MvPolynomial.X (1 : Fin 2) - MvPolynomial.C t * MvPolynomial.X (0 : Fin 2)) by
          simp [sub_eq_add_neg]]
      exact neg_dvd.mpr h
    have hpowI : MvPolynomial.X (1 : Fin 2) ^ (d 1) -
          (MvPolynomial.C t * MvPolynomial.X (0 : Fin 2)) ^ (d 1) ∈ I :=
      Ideal.mem_span_singleton.mpr hpow
    have hmul : MvPolynomial.C r * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
          (MvPolynomial.X (1 : Fin 2) ^ (d 1) -
            (MvPolynomial.C t * MvPolynomial.X (0 : Fin 2)) ^ (d 1)) ∈ I := by
      exact I.mul_mem_left _ hpowI
    have hEq : MvPolynomial.monomial d r -
          MvPolynomial.C (MvPolynomial.eval ![1, t] (MvPolynomial.monomial d r)) *
            MvPolynomial.X (0 : Fin 2) ^ n =
        MvPolynomial.C r * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
          (MvPolynomial.X (1 : Fin 2) ^ (d 1) -
            (MvPolynomial.C t * MvPolynomial.X (0 : Fin 2)) ^ (d 1)) := by
      rw [MvPolynomial.eval_monomial]
      have hp : d.prod (fun i e => ![1, t] i ^ e) =
          (1 : k) ^ d 0 * t ^ d 1 := by
        calc
          d.prod (fun i e => ![1, t] i ^ e) =
              ∏ x ∈ Finset.univ, ![1, t] x ^ d x := by
                apply Finsupp.prod_of_support_subset
                · exact Finset.subset_univ _
                · intro i _
                  simp
          _ = (1 : k) ^ d 0 * t ^ d 1 := by
                rw [Fin.prod_univ_two]
                rfl
      rw [hp]
      simp only [one_pow, one_mul]
      rw [MvPolynomial.monomial_eq]
      have hx : d.prod (fun i e => MvPolynomial.X (R := k) i ^ e) =
          MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1 := by
        calc
          d.prod (fun i e => MvPolynomial.X (R := k) i ^ e) =
              ∏ x ∈ Finset.univ, MvPolynomial.X (R := k) x ^ d x := by
                apply Finsupp.prod_of_support_subset
                · exact Finset.subset_univ _
                · intro i _
                  simp
          _ = _ := by rw [Fin.prod_univ_two]
      rw [hx]
      ring_nf
      rw [← hdeg, pow_add]
      simp only [map_pow, MvPolynomial.C_mul]
      ring
    rw [hEq]
    exact hmul
  have haux : ∀ (g : MvPolynomial (Fin 2) k), g.IsHomogeneous n →
      g - MvPolynomial.C (MvPolynomial.eval ![1, t] g) *
        MvPolynomial.X (0 : Fin 2) ^ n ∈ I := by
    intro g hg
    induction hg using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp [I]
    | add p q hp hq ihp ihq =>
        have hh := I.add_mem ihp ihq
        simpa [map_add, sub_eq_add_neg, add_mul, add_assoc, add_left_comm, add_comm] using hh
    | monomial d r hd =>
        have hdeg : d.degree = n := by
          simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
        exact hmon d r hdeg
  have hmem := haux f hf
  have hlast : MvPolynomial.C (MvPolynomial.eval ![1, t] f) *
      MvPolynomial.X (0 : Fin 2) ^ n ∈ I := by
    rw [hzero]
    simp
  have := I.add_mem hmem hlast
  simpa [I] using this

/-- A homogeneous basic open at a coordinate point is detected by evaluation. -/
theorem ProjectiveLine.ofCoords_mem_basicOpen_iff_eval {k : Type u} [Field k]
    (v : Fin 2 → k) (hv : v ≠ 0) (i : Fin 2) (hi : v i = 1)
    {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous n) :
    (ProjectiveLine.ofCoords v hv : ProjectiveLine k) ∈
        Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) f ↔
      MvPolynomial.eval v f ≠ 0 := by
  change f ∉ Ideal.span ({v 1 • MvPolynomial.X (0 : Fin 2) -
    v 0 • MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) ↔ _
  constructor
  · intro hnot he
    fin_cases i
    · have hvform : v = ![1, v 1] := by
        funext j
        fin_cases j
        · simpa using hi
        · rfl
      rw [hvform] at hnot he
      apply hnot
      simpa [Algebra.smul_def] using span_mem_case0 (v 1) hn hf he
    · have hvform : v = ![v 0, 1] := by
        funext j
        fin_cases j
        · simp
        · simpa using hi
      rw [hvform] at hnot he
      apply hnot
      simpa [Algebra.smul_def] using span_mem_case1 (v 0) hn hf he
  · intro hmem
    intro he
    have hker : Ideal.span
        ({v 1 • MvPolynomial.X (0 : Fin 2) - v 0 • MvPolynomial.X (1 : Fin 2)} :
          Set (MvPolynomial (Fin 2) k)) ≤
        RingHom.ker (MvPolynomial.eval v) := by
      rw [Ideal.span_le]
      intro z hz
      rcases hz with rfl
      simp [MvPolynomial.eval, sub_eq_add_neg]
      ring
    exact hmem (hker he)

theorem ProjectiveLine.exists_coords_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    (p : ProjectiveLine k) (hp : IsClosed ({p} : Set (ProjectiveLine k))) :
    ∃ (v : Fin 2 → k) (hv : v ≠ 0), p = ProjectiveLine.ofCoords v hv := by
  letI : AlgebraicGeometry.LocallyOfFiniteType
      (ProjectiveSpace.toSpecBase 1 k) := by
    letI : AlgebraicGeometry.IsProper (ProjectiveSpace.toSpecBase 1 k) :=
      ProjectiveSpace.isProper_toSpecBase 1 k
    infer_instance
  let e := AlgebraicGeometry.pointEquivClosedPoint (ProjectiveSpace.toSpecBase 1 k)
  let q : {g : Spec (CommRingCat.of k) ⟶ ProjectiveLine k //
      g ≫ ProjectiveSpace.toSpecBase 1 k = 𝟙 _} :=
    e.symm ⟨p, hp⟩
  have hq : q.1 (IsLocalRing.closedPoint k) = p := by
    have h := e.apply_symm_apply ⟨p, hp⟩
    exact congrArg Subtype.val h
  obtain ⟨i, hi⟩ :=
    AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.rationalPoint_exists_coordinateOpen ⟨q.1, q.2⟩
  let v := AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.normalizedCoordinates ⟨q.1, q.2⟩ i hi
  have hv : v ≠ 0 := by
    intro hv0
    have h := AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.normalizedCoordinates_nonzero
      ⟨q.1, q.2⟩ i hi
    exact h.elim
      (fun h0 => h0 (congrFun hv0 0))
      (fun h1 => h1 (congrFun hv0 1))
  have hvi : v i = 1 :=
    AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.normalizedCoordinates_self ⟨q.1, q.2⟩ i hi
  refine ⟨v, hv, ?_⟩
  apply AlgebraicGeometry.Proj.ProjectiveLineBasicOpenExt.point_eq_of_pos_homogeneous_basicOpen
  intro n hn f hf
  rw [← hq]
  exact (rationalPoint_mem_basicOpen_coords q.1 q.2 i hi hn hf).trans
    (ProjectiveLine.ofCoords_mem_basicOpen_iff_eval v hv i hvi hn hf).symm

end
