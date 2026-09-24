import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks035b_CharPAux
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.CharP.Reduced

/-! # Polynomial rings over a field are N-2

**Statement (Stacks, Algebra, §"Nagata rings", tag 032E ff.: a polynomial ring over a field is
N-2).** Let `k` be a field, `P = k[x_1, …, x_d]`,
`F = Frac P = k(x_1, …, x_d)` and `L/F` a finite field extension. Then the integral closure of `P`
in `L` is a finite `P`-module.

This is the only ingredient of the finiteness of the integral closure over a finite type algebra
over a field (`Algebra.finite_integralClosure_of_finiteType_over_field`, module `Stacks035b`) that
Mathlib does not already contain:

* in characteristic `0` (more generally whenever `L/F` is separable) it **is** Mathlib's
  `IsIntegralClosure.finite` (Stacks 032L: `P` is a Noetherian integrally closed domain, being a
  UFD), see `Field.polynomialRingsN2_of_charZero`;
* in characteristic `p > 0` the extension `L/F` may be inseparable and one needs E. Noether's
  argument with `q`-th roots; this is `Field.polynomialRingsN2_of_charP`, proved here in full by
  an *internal* version of that argument (Frobenius `z ↦ z^q` on `L` instead of adjoining `q`-th
  roots in an algebraic closure), see its docstring.

The property is packaged as the `Prop` `Field.PolynomialRingsN2 k` (all `d`, all `F`, all finite
`L/F`), so that the users can be stated once for an arbitrary field (`Field.polynomialRingsN2`).

Auxiliary elementary lemmas live in `Stacks035b_CharPAux.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

noncomputable section

/-- **N-2 for polynomial rings over `k`** (Stacks, Algebra, §Nagata rings): for every `d`, every
fraction field `F` of `P = k[x_1, …, x_d]` and every finite extension `L/F`, the integral closure of
`P` in `L` is a finite `P`-module. -/
def Field.PolynomialRingsN2 (k : Type u) [Field k] : Prop :=
  ∀ (d : ℕ) (F : Type u) [Field F] [Algebra (MvPolynomial (Fin d) k) F]
    [IsFractionRing (MvPolynomial (Fin d) k) F]
    (L : Type u) [Field L] [Algebra F L] [Algebra (MvPolynomial (Fin d) k) L]
    [IsScalarTower (MvPolynomial (Fin d) k) F L] [FiniteDimensional F L],
    Module.Finite (MvPolynomial (Fin d) k) ↥(integralClosure (MvPolynomial (Fin d) k) L)

/-- **Characteristic `0`**: `Field.PolynomialRingsN2 k` holds for `[CharZero k]`.

Proof: `P = k[x_1, …, x_d]` is a UFD (`MvPolynomial` over a field), hence integrally closed, and
Noetherian (Hilbert basis theorem). `F = Frac P` has characteristic `0`, so it is a perfect field and
the finite extension `L/F` is separable. Stacks 032L = Mathlib `IsIntegralClosure.finite P F L _`
gives that `integralClosure P L` is a finite `P`-module. -/
theorem Field.polynomialRingsN2_of_charZero (k : Type u) [Field k] [CharZero k] :
    Field.PolynomialRingsN2 k := by
  intro d F _ _ _ L _ _ _ _ _
  haveI : CharZero F :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Fin d) k) F)
  exact IsIntegralClosure.finite (MvPolynomial (Fin d) k) F L _

set_option synthInstance.maxHeartbeats 100000 in
/-- **Characteristic `p` (`k` not necessarily perfect)**: `Field.PolynomialRingsN2 k` for a field
`k` of characteristic `p > 0`.

Source: Stacks, Algebra, §Nagata rings (tag 032E ff.), lemma "`k[x_1, …, x_n]` is N-2 for every
field `k`" (E. Noether). The proof below is that argument, made *internal* to `L`: instead of
adjoining `q`-th roots in an algebraic closure we apply the Frobenius `z ↦ z^q` to everything.

Proof (matching the Lean). Write `P = k[x_1, …, x_d]`, `F = Frac P`, `L/F` finite.
1. Let `M = separableClosure F L`; `L/M` is purely inseparable and finite, so it has an exponent
   `e` (Mathlib `IsPurelyInseparable.exponent`): with `q = p^e`, `z^q ∈ M` for all `z ∈ L`.
   Let `φ : L → L`, `φ(z) = z^q` (`iterateFrobenius`), an injective ring homomorphism.
2. Choose an `F`-basis `b_i` of `L` consisting of elements integral over `P` (scale a basis by
   nonzero elements of `P`: `IsAlgebraic.exists_integral_multiple`). Put `β_i := b_i^q ∈ M`; each
   `β_i` is integral over `P` and separable over `F`. Let `m_i := minpoly P β_i ∈ P[X]`; since `P` is
   integrally closed, `minpoly F β_i = m_i.map (P → F)` (`minpoly.isIntegrallyClosed_eq_field_fractions'`),
   so `m_i.map (P → F)` is separable.
3. Let `S ⊆ k` be the finite set of all `k`-coefficients of all coefficients of all `m_i`,
   `k^q := (iterateFrobenius k p e).fieldRange` and `k₀ := k^q(S) ⊆ k`; `k₀/k^q` is finite (each
   `s ∈ S` is a root of `X^q - s^q`, `s^q ∈ k^q`). Put `P₀ := k₀[x_1, …, x_d]` with the inclusion
   `j : P₀ → P` (`MvPolynomial.map`), and `ρ : P → P₀`, `ρ = (MvPolynomial.map frob') ∘ (expand q)`
   where `frob' : k → k₀`, `c ↦ c^q`; then `j ∘ ρ = (z ↦ z^q)` on `P`, and `ρ` is a **finite** ring
   homomorphism (`MvPolynomial.expand_finite`, `MvPolynomial.map_finite`, and `frob'` is finite
   because `k₀/k^q` is finite and `k ≅ k^q`).
4. Let `F₀ = Frac P₀` (mapped into `L` through `j`) and `M₀ := F₀(β_1, …, β_n) ⊆ L`. Each `m_i`
   lifts to a monic `g_i ∈ P₀[X]` (`Polynomial.lifts_and_degree_eq_and_monic`, using
   `MvPolynomial.mem_range_map_of_coeff_mem_range`), `g_i(β_i) = 0`, and `g_i.map (P₀ → F₀)` is
   separable (its image in `L[X]` is `(minpoly F β_i).map (F → L)`), so `β_i` is integral and
   separable over `F₀`: `M₀/F₀` is finite separable, and `P₀` is a UFD, so by Stacks 032L = Mathlib
   `IsIntegralClosure.finite`, `C₀ := integralClosure P₀ M₀` is a finite `P₀`-module.
5. `L^q ⊆ M₀`: for `z = Σ c_i b_i` (`c_i ∈ F`), `z^q = Σ c_i^q β_i` and `c_i^q ∈ F^q ⊆ F₀`
   (`(n/d)^q = ρ(n)/ρ(d)` inside `L`). Hence `z ↦ z^q` defines an injective ring homomorphism
   `φ_C : integralClosure P L → C₀` (integrality via `IsIntegral.map_of_comp_eq`), and
   `φ_C ∘ (P → integralClosure P L) = (P₀ → C₀) ∘ ρ` is finite (`RingHom.Finite.comp`).
6. `P` is Noetherian, so `RingHom.Finite.of_comp_injective` gives that `P → integralClosure P L` is
   finite, i.e. `integralClosure P L` is a finite `P`-module. -/
theorem Field.polynomialRingsN2_of_charP (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] : Field.PolynomialRingsN2 k := by
  intro d F _ _ _ L _ _ _ _ _
  classical
  set P := MvPolynomial (Fin d) k with hP
  haveI : CharP F p := charP_of_injective_algebraMap (IsFractionRing.injective P F) p
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  have hPL : Function.Injective (algebraMap P L) := by
    rw [IsScalarTower.algebraMap_eq P F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective P F)
  -- the separable closure `M` of `F` in `L` and the exponent `e` of `L / M`
  let M : IntermediateField F L := separableClosure F L
  haveI : CharP M p := ⟨fun n => by
    rw [← map_eq_zero_iff (algebraMap M L) (algebraMap M L).injective, map_natCast]
    exact CharP.cast_eq_zero_iff L p n⟩
  haveI : FiniteDimensional M L := FiniteDimensional.right F M L
  haveI : IsPurelyInseparable M L := separableClosure.isPurelyInseparable F L
  set e := IsPurelyInseparable.exponent M L with he
  set q := p ^ e with hq
  have hq0 : 0 < q := pow_pos (Fact.out : p.Prime).pos e
  let φL : L →+* L := iterateFrobenius L p e
  have hφL : ∀ z : L, φL z = z ^ q := fun z => iterateFrobenius_def p e z
  have hpowM : ∀ z : L, z ^ q ∈ M := fun z => by
    rw [← IsPurelyInseparable.algebraMap_iterateFrobenius M p (le_refl e) z]
    exact SetLike.coe_mem _
  -- a basis of `L / F` consisting of elements integral over `P`
  let b₀ := Module.finBasis F L
  have hbalg : ∀ i, IsAlgebraic P (b₀ i) := fun i =>
    (IsFractionRing.isAlgebraic_iff P F L).mpr (Algebra.IsAlgebraic.isAlgebraic (b₀ i))
  choose y hy0 hyint using fun i => (hbalg i).exists_integral_multiple
  have hy0' : ∀ i, algebraMap P F (y i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective P F)).mpr (hy0 i)
  let b : Module.Basis (Fin (Module.finrank F L)) F L := b₀.unitsSMul fun i => Units.mk0 _ (hy0' i)
  have hbint : ∀ i, IsIntegral P (b i) := fun i => by
    have : b i = y i • b₀ i := by
      rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, algebraMap_smul]
    rw [this]; exact hyint i
  let β : Fin (Module.finrank F L) → L := fun i => b i ^ q
  have hβint : ∀ i, IsIntegral P (β i) := fun i => (hbint i).pow q
  have hβsep : ∀ i, IsSeparable F (β i) := fun i => mem_separableClosure_iff.mp (hpowM (b i))
  -- minimal polynomials over `P` and the finite set `S` of their `k`-coefficients
  let m : Fin (Module.finrank F L) → Polynomial P := fun i => minpoly P (β i)
  have hm : ∀ i, minpoly F (β i) = (m i).map (algebraMap P F) := fun i =>
    minpoly.isIntegrallyClosed_eq_field_fractions' F (hβint i)
  let S : Finset k := Finset.univ.biUnion fun i => (Finset.range ((m i).natDegree + 1)).biUnion
    fun jj => ((m i).coeff jj).support.image fun v => MvPolynomial.coeff v ((m i).coeff jj)
  have hS : ∀ i jj v, MvPolynomial.coeff v ((m i).coeff jj) ≠ 0 →
      MvPolynomial.coeff v ((m i).coeff jj) ∈ S := fun i jj v hv => by
    have hjj : jj ≤ (m i).natDegree := by
      by_contra h
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp h), MvPolynomial.coeff_zero] at hv
      exact hv rfl
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_image]
    exact ⟨i, jj, Nat.lt_succ_of_le hjj, v, MvPolynomial.mem_support_iff.mpr hv, rfl⟩
  -- the subfields `k^q ⊆ k₀ = k^q(S) ⊆ k`
  let kq : Subfield k := (iterateFrobenius k p e).fieldRange
  let k₀ : IntermediateField kq k := IntermediateField.adjoin kq (S : Set k)
  haveI : FiniteDimensional kq k₀ := by
    refine IntermediateField.finiteDimensional_adjoin fun x _ => ?_
    refine ⟨Polynomial.X ^ q - Polynomial.C ⟨x ^ q, ⟨x, iterateFrobenius_def p e x⟩⟩,
      Polynomial.monic_X_pow_sub_C _ hq0.ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    exact sub_self _
  let e' : k →+* kq := (iterateFrobenius k p e).rangeRestrictField
  have he'surj : Function.Surjective e' := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, Subtype.ext (RingHom.coe_rangeRestrictField _ _)⟩
  let frob' : k →+* k₀ := (algebraMap kq k₀).comp e'
  have hfrob'fin : frob'.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      (RingHom.Finite.of_surjective _ he'surj)
  -- `P₀ = k₀[x]` and the maps `j : P₀ → P`, `ρ : P → P₀`
  let P₀ := MvPolynomial (Fin d) k₀
  haveI : IsDomain P₀ := inferInstance
  haveI : IsNoetherianRing P₀ := inferInstance
  haveI : UniqueFactorizationMonoid P₀ := inferInstance
  haveI : IsIntegrallyClosed P₀ := UniqueFactorizationMonoid.instIsIntegrallyClosed
  let j : P₀ →+* P := MvPolynomial.map (algebraMap k₀ k)
  have hj : Function.Injective j := MvPolynomial.map_injective _ (algebraMap k₀ k).injective
  let ρ : P →+* P₀ :=
    (MvPolynomial.map frob').comp ((MvPolynomial.expand q : P →ₐ[k] P) : P →+* P)
  have hρfin : ρ.Finite :=
    RingHom.Finite.comp (MvPolynomial.map_finite frob' hfrob'fin d)
      (MvPolynomial.expand_finite k d q hq0)
  have hjρ : j.comp ρ = iterateFrobenius P p e := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change j (MvPolynomial.map frob' (MvPolynomial.expand q (MvPolynomial.C c)))
        = (MvPolynomial.C c) ^ q
      rw [MvPolynomial.expand_C, MvPolynomial.map_C,
        show j = MvPolynomial.map (algebraMap k₀ k) from rfl, MvPolynomial.map_C,
        ← MvPolynomial.C_pow]
      congr 1
    · intro i
      change j (MvPolynomial.map frob' (MvPolynomial.expand q (MvPolynomial.X i)))
        = (MvPolynomial.X i) ^ q
      rw [MvPolynomial.expand_X, map_pow, MvPolynomial.map_X,
        show j = MvPolynomial.map (algebraMap k₀ k) from rfl, map_pow, MvPolynomial.map_X]
  -- algebra structures on `L` over `P₀` and `F₀ = Frac P₀`
  letI : Algebra P₀ P := j.toAlgebra
  letI : Algebra P₀ L := ((algebraMap P L).comp j).toAlgebra
  haveI : IsScalarTower P₀ P L := .of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul P₀ L :=
    (faithfulSMul_iff_algebraMap_injective P₀ L).mpr (hPL.comp hj)
  letI := FractionRing.liftAlgebra P₀ L
  haveI := FractionRing.isScalarTower_liftAlgebra P₀ L
  let F₀ := FractionRing P₀
  let M₀ : IntermediateField F₀ L := IntermediateField.adjoin F₀ (Set.range β)
  letI : Algebra P₀ M₀ := IntermediateField.algebra' M₀
  haveI : IsScalarTower P₀ F₀ M₀ := IntermediateField.isScalarTower (S := M₀)
  -- lifts of the minimal polynomials to `P₀[X]`
  have hlift : ∀ i, ∃ g : Polynomial P₀, g.map j = m i ∧ g.Monic := fun i => by
    have hlifts : m i ∈ Polynomial.lifts j := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro jj
      refine RingHom.mem_range.mp
        (MvPolynomial.mem_range_map_of_coeff_mem_range _ _ fun v => ?_)
      by_cases hv : MvPolynomial.coeff v ((m i).coeff jj) = 0
      · exact ⟨0, by rw [map_zero, hv]⟩
      · exact ⟨⟨_, IntermediateField.subset_adjoin kq (S : Set k) (hS i jj v hv)⟩, rfl⟩
    obtain ⟨g, hg, -, hmon⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic hlifts (minpoly.monic (hβint i))
    exact ⟨g, hg, hmon⟩
  choose g hgj hgmon using hlift
  have hgβ : ∀ i, Polynomial.aeval (β i) (g i) = 0 := fun i => by
    have h1 : Polynomial.aeval (β i) (m i) = 0 := minpoly.aeval P (β i)
    rw [← hgj i] at h1
    rwa [show (g i).map j = (g i).map (algebraMap P₀ P) from rfl,
      Polynomial.aeval_map_algebraMap] at h1
  have hgL : ∀ i, (g i).map (algebraMap P₀ L) = (minpoly F (β i)).map (algebraMap F L) := fun i => by
    rw [hm, Polynomial.map_map, ← IsScalarTower.algebraMap_eq P F L,
      show algebraMap P₀ L = (algebraMap P L).comp j from rfl, ← Polynomial.map_map, hgj]
  have hgsep : ∀ i, ((g i).map (algebraMap P₀ F₀)).Separable := fun i => by
    rw [← Polynomial.separable_map (algebraMap F₀ L), Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq P₀ F₀ L, hgL]
    exact Polynomial.Separable.map (hβsep i)
  have hβint₀ : ∀ i, IsIntegral F₀ (β i) := fun i =>
    ⟨(g i).map (algebraMap P₀ F₀), (hgmon i).map _, by
      rw [← Polynomial.aeval_def, Polynomial.aeval_map_algebraMap]; exact hgβ i⟩
  have hβsep₀ : ∀ i, IsSeparable F₀ (β i) := fun i =>
    (hgsep i).of_dvd (minpoly.dvd F₀ (β i) (by rw [Polynomial.aeval_map_algebraMap]; exact hgβ i))
  haveI : Algebra.IsSeparable F₀ M₀ :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable F₀ L).mpr
      (by rintro _ ⟨i, rfl⟩; exact hβsep₀ i)
  haveI : FiniteDimensional F₀ M₀ :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact hβint₀ i)
  -- the integral closure of `P₀` in `M₀` is finite (separable case)
  letI : Algebra P₀ ↥(integralClosure P₀ M₀) := (integralClosure P₀ M₀).algebra
  have hC₀ := IsIntegralClosure.finite P₀ F₀ M₀ (integralClosure P₀ M₀)
  -- Frobenius identities
  have hcompL : (algebraMap P₀ L).comp ρ = φL.comp (algebraMap P L) := by
    rw [show algebraMap P₀ L = (algebraMap P L).comp j from rfl, RingHom.comp_assoc, hjρ]
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, φL, iterateFrobenius_def, map_pow]
  have hcompL' : ∀ a : P, algebraMap P₀ L (ρ a) = algebraMap P L a ^ q := fun a => by
    have := congrArg (fun f : P →+* L => f a) hcompL
    simpa [hφL] using this
  -- `F^q ⊆ F₀` inside `L`, hence `L^q ⊆ M₀`
  have hFq : ∀ c : F, algebraMap F L c ^ q ∈ (algebraMap F₀ L).range := fun c => by
    obtain ⟨nn, dd, hdd, rfl⟩ := IsFractionRing.div_surjective (A := P) c
    refine ⟨algebraMap P₀ F₀ (ρ nn) / algebraMap P₀ F₀ (ρ dd), ?_⟩
    rw [map_div₀, map_div₀, div_pow, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, hcompL', hcompL', ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hφM₀ : ∀ z : L, z ^ q ∈ M₀ := fun z => by
    rw [← b.sum_repr z, ← hφL, map_sum]
    refine IntermediateField.sum_mem _ fun i _ => ?_
    rw [hφL, Algebra.smul_def, mul_pow]
    obtain ⟨w, hw⟩ := hFq (b.repr z i)
    rw [← hw]
    exact M₀.mul_mem (M₀.algebraMap_mem w) (IntermediateField.subset_adjoin F₀ _ ⟨i, rfl⟩)
  -- the ring homomorphism `integralClosure P L → integralClosure P₀ M₀`, `z ↦ z^q`
  have hint : ∀ z : ↥(integralClosure P L), IsIntegral P₀ (z.1 ^ q) := fun z => by
    have := IsIntegral.map_of_comp_eq ρ φL hcompL (z.2 : IsIntegral P z.1)
    rwa [hφL] at this
  let φC : ↥(integralClosure P L) →+* ↥(integralClosure P₀ M₀) :=
    { toFun := fun z => ⟨⟨z.1 ^ q, hφM₀ z.1⟩,
        (IntermediateField.coe_isIntegral_iff (R := P₀)).mp (hint z)⟩
      map_one' := Subtype.ext (Subtype.ext (one_pow q))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (mul_pow _ _ q))
      map_zero' := Subtype.ext (Subtype.ext (zero_pow hq0.ne'))
      map_add' := fun a b => Subtype.ext (Subtype.ext (by
        show ((a : L) + (b : L)) ^ q = (a : L) ^ q + (b : L) ^ q
        exact add_pow_expChar_pow _ _ p e)) }
  have hφC : Function.Injective φC := fun a b h => by
    apply Subtype.ext
    have h1 : a.1 ^ q = b.1 ^ q :=
      congrArg (fun w => ((w : ↥(integralClosure P₀ M₀)) : ↥M₀).1) h
    exact iterateFrobenius_inj L p e h1
  have hcomp : φC.comp (algebraMap P ↥(integralClosure P L))
      = (algebraMap P₀ ↥(integralClosure P₀ M₀)).comp ρ := by
    refine RingHom.ext fun a => Subtype.ext (Subtype.ext ?_)
    change (algebraMap P L a) ^ q = algebraMap P₀ L (ρ a)
    rw [hcompL']
  refine RingHom.finite_algebraMap.mp (RingHom.Finite.of_comp_injective (R := P)
    (A := ↥(integralClosure P L)) (B := ↥(integralClosure P₀ M₀)) (algebraMap P _) φC hφC ?_)
  rw [hcomp]
  exact RingHom.Finite.comp (RingHom.finite_algebraMap.mpr hC₀) hρfin


/-- **N-2 for polynomial rings over an arbitrary field** (Stacks, Algebra, §Nagata rings), by the
characteristic split: characteristic `0` is `Field.polynomialRingsN2_of_charZero` (Mathlib's
`IsIntegralClosure.finite`), characteristic `p` is `Field.polynomialRingsN2_of_charP`. -/
theorem Field.polynomialRingsN2 (k : Type u) [Field k] : Field.PolynomialRingsN2 k := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact Field.polynomialRingsN2_of_charZero k
  · exact Field.polynomialRingsN2_of_charP k p

end
