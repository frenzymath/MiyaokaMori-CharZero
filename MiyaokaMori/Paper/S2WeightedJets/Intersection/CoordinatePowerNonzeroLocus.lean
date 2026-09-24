import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitCoordPowMultiplicative
import MiyaokaMori.AlgebraicGeometry.Modules.SectionSupportComplNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitCoordBasicOpen
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraSufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedCoordinate
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The nonvanishing locus of a coordinate power

If `s` is a global section on the split weighted Proj given by the coordinate power formula, and its sheaf is a line
bundle, then the nonvanishing locus of `s` is the relative basic open set `splitCoordBasicOpen F kk p` of the
corresponding coordinate (proof of Proposition 2.4 of the paper: raising the coordinate to the `m/q`-th
power does not change its zero set).
Proof, in two steps:
1. A general lemma: the complement of the support of the zero scheme of a global section of a line bundle is its
   `nonvanishingLocus` (Stacks 01WX/01X0 and 01CY).
2. `splitCoordBasicOpen F kk p` is **by definition** the `nonvanishingLocus` of the coordinate power `x_p^{m₀/q}` for
   `m₀ := lcm(1..kk)`, so what remains is that the nonvanishing locus does not depend on `m`: `m₀ ∣ m` (all weights
   divide `m`), write `m = m₀·r`; the coordinate power sections are multiplicative in the exponent — there is an
   isomorphism `L_{m₀ r} ⊗ L_{m₀} ≅ L_{m₀(r+1)}` sending `x^{m₀r/q} ⊗ x^{m₀/q}` to `x^{m₀(r+1)/q}`
   (`splitTwistMul_add_exists_iso`); isomorphisms do not change nonvanishing loci (`NonvanishingLocusIsoInvariant`),
   and the nonvanishing locus of a tensor of line bundle sections is the intersection
   (`nonvanishingLocus_sectionTensor`), so induction on `r` gives `X_{x^{m₀ r/q}} = X_{x^{m₀/q}}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Sanity check: for `m = m₀ := lcm(1..kk)`, the nonvanishing locus of the coordinate power `x_p^{m₀/q}` is **by
definition** `splitCoordBasicOpen F kk p` (which is how `D₊(x_p)` is defined). Hence the content of this module is
that the nonvanishing locus does not depend on `m`. -/
theorem splitCoordPow_nonvanishingLocus_lcm {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (p : Fin (n + 1) × Fin kk) :
    letI := splitCoordBasicOpen.lineBundle_isLineBundle F kk p
    AlgebraicGeometry.Scheme.Modules.nonvanishingLocus (splitCoordBasicOpen.lineBundle F kk p)
      (splitTwistMul F kk p.1 ((p.2 : ℕ) + 1) ((Finset.Icc 1 kk).lcm id)
        (Finset.dvd_lcm (by simp only [Finset.mem_Icc]; omega))
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection
          (splitWeightedCoord F p.1 ((p.2 : ℕ) + 1) (by simp only [Finset.mem_Icc]; omega))
          ((Finset.Icc 1 kk).lcm id / ((p.2 : ℕ) + 1)))) = splitCoordBasicOpen F kk p :=
  rfl

/-- The sheaf `L_m := O(m) ⊗ π^*Q_i^{⊗ m/q}` containing the coordinate power section is a line bundle when `m > 0` is
divisible by all weights (the version of `splitCoordBasicOpen.lineBundle_isLineBundle` for general `m`, with the same
proof: `m` is sufficiently divisible (`splitWeightedAlgebra_sufficientlyDivisible_of_dvd`), so `O(m)` is invertible
(`relativeProj.isLineBundle_twist`); `Q_i` is a line bundle, and tensor powers, pullbacks and tensor products of line
bundles are line bundles). -/
theorem splitCoordPow_isLineBundle {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (i : Fin (n + 1)) (q m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) :
    ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q)))).IsLineBundle := by
  have htw : (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).IsLineBundle :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (splitWeightedAlgebraOf F kk) _
      (splitWeightedAlgebra_sufficientlyDivisible_of_dvd F kk _ hm hdiv)
  have hpow : (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q)).IsLineBundle :=
    SheafOfModules.IsLineBundle.tensorPow _ _
  have hpull : ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q))).IsLineBundle :=
    SheafOfModules.IsLineBundle.pullback _ _
  exact SheafOfModules.IsLineBundle.tensor _ _

/-- **The inductive step**: for `m = m₀·(r+1)` (`m₀ := lcm(1..kk)`) the nonvanishing locus of the coordinate power
`x_p^{m/q}` is `splitCoordBasicOpen F kk p`. Induction on `r`: `r = 0` is by definition
(`splitCoordPow_nonvanishingLocus_lcm`); for `r + 1`, `m = m₀(r+1) + m₀`, `splitTwistMul_add_exists_iso` gives an
isomorphism `Φ : L_{m₀(r+1)} ⊗ L_{m₀} ≅ L_m` sending `x^{m₀(r+1)/q} ⊗ x^{m₀/q}` to `x^{m/q}`, `nonvanishingLocus_iso`
removes `Φ`, `nonvanishingLocus_sectionTensor` splits the nonvanishing locus of the tensor into an intersection, and
the induction hypothesis together with the case `r = 0` and `D ⊓ D = D` concludes. -/
theorem splitCoordPow_nonvanishingLocus_lcm_mul {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (p : Fin (n + 1) × Fin kk) (r : ℕ) :
    ∀ (m : ℕ), m = (Finset.Icc 1 kk).lcm id * (r + 1) → ∀ (_hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m)
    (hL : ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1))))).IsLineBundle),
    (letI := hL
    AlgebraicGeometry.Scheme.Modules.nonvanishingLocus
      ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1)))))
      (splitTwistMul F kk p.1 ((p.2 : ℕ) + 1) m (hdiv _ (by simp only [Finset.mem_Icc]; omega))
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection
          (splitWeightedCoord F p.1 ((p.2 : ℕ) + 1) (by simp only [Finset.mem_Icc]; omega))
          (m / ((p.2 : ℕ) + 1))))) = splitCoordBasicOpen F kk p := by
  have hq : (p.2 : ℕ) + 1 ∈ Finset.Icc 1 kk := by simp only [Finset.mem_Icc]; omega
  have hm₀pos : 0 < ((Finset.Icc 1 kk).lcm id : ℕ) := by
    refine Nat.pos_of_ne_zero fun h => ?_
    obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h
    simp only [Finset.mem_Icc, id] at hx hx0
    omega
  have hm₀div : ∀ q ∈ Finset.Icc 1 kk, q ∣ ((Finset.Icc 1 kk).lcm id : ℕ) := fun q hq => Finset.dvd_lcm hq
  induction r with
  | zero =>
    intro m hr hm hdiv hL
    have hr' : m = (Finset.Icc 1 kk).lcm id := by rw [hr, Nat.zero_add, Nat.mul_one]
    subst hr'
    exact splitCoordPow_nonvanishingLocus_lcm F p
  | succ r ih =>
    intro m hr hm hdiv hL
    have hr' : m = (Finset.Icc 1 kk).lcm id * (r + 1) + (Finset.Icc 1 kk).lcm id := by
      rw [hr, Nat.mul_succ]
    subst hr'
    have hm1 : 0 < (Finset.Icc 1 kk).lcm id * (r + 1) := Nat.mul_pos hm₀pos (Nat.succ_pos r)
    have hdiv1 : ∀ q ∈ Finset.Icc 1 kk, q ∣ (Finset.Icc 1 kk).lcm id * (r + 1) :=
      fun q hq => Dvd.dvd.mul_right (hm₀div q hq) _
    have hL1 := splitCoordPow_isLineBundle F p.1 ((p.2 : ℕ) + 1) _ hm1 hdiv1
    have hL0 := splitCoordPow_isLineBundle F p.1 ((p.2 : ℕ) + 1) _ hm₀pos hm₀div
    have _hLinst := hL
    obtain ⟨Φ, hΦ⟩ := splitTwistMul_add_exists_iso F p.1 ((p.2 : ℕ) + 1) hq
      ((Finset.Icc 1 kk).lcm id * (r + 1)) ((Finset.Icc 1 kk).lcm id) hm1 hm₀pos hdiv1 hm₀div
    have h0 := splitCoordPow_nonvanishingLocus_lcm F p
    unfold splitCoordBasicOpen.lineBundle at h0
    rw [← hΦ]
    refine (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso Φ _).trans ?_
    refine (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_sectionTensor _ _ _ _).trans ?_
    rw [ih _ rfl hm1 hdiv1 hL1, h0, inf_idem]

/-- **The nonvanishing locus of a coordinate power does not depend on the exponent**: for every `m > 0` divisible by
all weights `1, …, kk`, the nonvanishing locus of
`x_p^{m/q} := splitTwistMul (x_p^{⊗ m/q}) ∈ Γ(Y^sp, O(m) ⊗ π^*Q_i^{⊗ m/q})` (`q = p.2 + 1`, `i = p.1`) is the relative
basic open set `D₊(x_p) = splitCoordBasicOpen F kk p` (which is by definition the case `m = lcm(1..kk)`, see
`splitCoordPow_nonvanishingLocus_lcm`).

Source: proof of Proposition 2.4 of the paper (raising the coordinate to the `m/q`-th power does not
change its zero set); Stacks 01MO/01MS.

Proof: `m₀ := lcm(1..kk)` divides `m` (`Finset.lcm_dvd`), so `m = m₀(r+1)` (as `m > 0`); then
`splitCoordPow_nonvanishingLocus_lcm_mul` by induction on `r`, using `splitTwistMul_add_exists_iso`
(`L_{m₀(r+1)} ⊗ L_{m₀} ≅ L_{m₀(r+2)}` sending `x^{m₀(r+1)/q} ⊗ x^{m₀/q}` to `x^{m₀(r+2)/q}`), `nonvanishingLocus_iso`
(isomorphisms do not change nonvanishing loci) and `nonvanishingLocus_sectionTensor` (the nonvanishing locus of a
tensor is the intersection). No identification of `S^sp` with a polynomial algebra is needed. -/
theorem splitCoordPow_nonvanishingLocus_eq_splitCoordBasicOpen {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) (p : Fin (n + 1) × Fin kk)
    (hL : ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1))))).IsLineBundle) :
    letI := hL
    AlgebraicGeometry.Scheme.Modules.nonvanishingLocus
      ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1)))))
      (splitTwistMul F kk p.1 ((p.2 : ℕ) + 1) m (hdiv _ (by simp only [Finset.mem_Icc]; omega))
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection
          (splitWeightedCoord F p.1 ((p.2 : ℕ) + 1) (by simp only [Finset.mem_Icc]; omega))
          (m / ((p.2 : ℕ) + 1)))) = splitCoordBasicOpen F kk p := by
  obtain ⟨r, hr⟩ : (Finset.Icc 1 kk).lcm id ∣ m := Finset.lcm_dvd (fun q hq => hdiv q hq)
  cases r with
  | zero =>
    rw [Nat.mul_zero] at hr
    omega
  | succ r =>
    exact splitCoordPow_nonvanishingLocus_lcm_mul F p r m hr hm hdiv hL

theorem coordPowSection_nonzeroLocus_formula {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) (p : Fin (n + 1) × Fin kk)
    (s : ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1))))).val.obj (Opposite.op ⊤))
    (hs : s = splitTwistMul F kk p.1 ((p.2 : ℕ) + 1) m
      (hdiv _ (by simp only [Finset.mem_Icc]; omega))
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection
        (splitWeightedCoord F p.1 ((p.2 : ℕ) + 1) (by simp only [Finset.mem_Icc]; omega))
        (m / ((p.2 : ℕ) + 1))))
    (hL : ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1))))).IsLineBundle) :
    letI := hL
    (SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection _ s).support)ᶜ =
      ((splitCoordBasicOpen F kk p : (splitWeightedProjectivization F kk).left.Opens) :
        Set (splitWeightedProjectivization F kk).left) := by
  subst hs
  rw [AlgebraicGeometry.Scheme.idealSheafOfSection_support_compl_eq_nonvanishingLocus,
    splitCoordPow_nonvanishingLocus_eq_splitCoordBasicOpen F m hm hdiv p hL]

end
