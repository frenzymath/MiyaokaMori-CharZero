import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.NormalizationFiniteNagata
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks035b_CharPAux
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.MvPolynomial.Expand

/-! # N-2 for finite type domains over a perfect field of characteristic `p`

**N-2 (perfect field, characteristic `p`)**: `k` a perfect field of characteristic `p > 0`, `A` a
finite type `k`-algebra which is a domain, `K = Frac A`, `L/K` a finite extension; then the integral
closure of `A` in `L` is a finite `A`-module. Taking `L = K` gives N-1 (finiteness of the
normalization).

This is the instance, for a perfect field of positive characteristic, of the half "every quotient
domain is N-2" of Stacks 0335 (finite type algebras over a field are Nagata rings); the
characteristic-`0` N-1 is `Ring.module_finite_integralClosure_of_finiteType` (module
`NormalizationFiniteNagata`), and this file supplies the positive-characteristic branch, used in
`Ring.module_finite_integralClosure_of_finiteType_of_perfectField` (finite normalization of a curve
over a perfect field) and in step 4 of `Algebra.finite_integralClosure_of_finiteType_over_field`.

References: Stacks 0335, 0333 (polynomial rings over a perfect field are N-2), 032L (the integral
closure in a finite separable extension is finite = Mathlib `IsIntegralClosure.finite`), 00OW
(Noether normalization = Mathlib `exists_finite_inj_algHom_of_fg`).

**Route**: the argument of Stacks 0333, but instead of taking `q`-th roots in an algebraic closure,
the Frobenius sends the candidate elements of `L` into the separable closure:

* `P = k[x_1..x_d]`, `F = Frac P`, `L/F` finite. Let `S = separableClosure F L` (the separable closure
  of `F` in `L`); `L/S` is purely inseparable and finite, so there is `q = p^e` with
  `∀ y ∈ L, y^q ∈ S` (`IsPurelyInseparable.exists_pow_mem_of_finiteDimensional`).
* Stacks 032L (Mathlib `IsIntegralClosure.finite P F S`): `C := integralClosure P S` is a finite
  `P`-module.
* `k` perfect ⇒ the `q`-th Frobenius `φ : P → P` is a finite ring map
  (`MvPolynomial.iterateFrobenius_finite_of_perfectField`: `φ = map(Frob_k^e) ∘ expand q`, `expand q`
  is finite (`MvPolynomial.expand_finite`), `map(Frob_k^e)` is bijective).
* `ψ : integralClosure P L → C, y ↦ y^q` is an injective ring map, and
  `ψ ∘ (P → integralClosure P L) = (P → C) ∘ φ` is finite; `P` is Noetherian, so
  `P → integralClosure P L` is finite (`RingHom.Finite.of_comp_injective`).
* General finite type domain `A`: Noether normalization `P → A` is finite injective, and
  `integralClosure A L = integralClosure P L`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

open scoped nonZeroDivisors

universe u v w u' v'

noncomputable section

/-! ### A uniform exponent for finite purely inseparable extensions -/

/-- **Uniform exponent**: if `E/F` is purely inseparable and finite with `F` of characteristic `p`,
then there is `n` with `∀ x ∈ E, x^(p^n) ∈ F`.

Proof: `[E:F] = p^n` (`IsPurelyInseparable.finrank_eq_pow`); for `x`, `minpoly F x = X^(p^m) - C y`
(`IsPurelyInseparable.minpoly_eq_X_pow_sub_C`), whose degree `p^m` divides `[E:F] = p^n`
(`minpoly.degree_dvd`), so `m ≤ n` and `x^(p^n) = (x^(p^m))^(p^(n-m)) = y^(p^(n-m)) ∈ F`.
Reference: standard, cf. Stacks 09HD/09HE. -/
theorem IsPurelyInseparable.exists_pow_mem_of_finiteDimensional (F : Type u) (E : Type v) [Field F]
    [Field E] [Algebra F E] (p : ℕ) [Fact p.Prime] [CharP F p] [IsPurelyInseparable F E]
    [FiniteDimensional F E] :
    ∃ n : ℕ, ∀ x : E, x ^ p ^ n ∈ (algebraMap F E).range := by
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow F E p
  refine ⟨n, fun x => ?_⟩
  obtain ⟨m, y, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
  have hdvd : (minpoly F x).natDegree ∣ Module.finrank F E :=
    minpoly.degree_dvd (IsIntegral.of_finite F x)
  rw [hmin, Polynomial.natDegree_X_pow_sub_C, hn] at hdvd
  have hmn : m ≤ n := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hdvd
  have hx : x ^ p ^ m = algebraMap F E y := by
    have h := minpoly.aeval F x
    rw [hmin, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h
    exact h
  refine ⟨y ^ p ^ (n - m), ?_⟩
  rw [map_pow, ← hx, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hmn]

/-! ### The Frobenius of a polynomial ring over a perfect field is finite -/

/-- The `p^e`-th Frobenius on `k[x_1..x_d]` equals `map (Frob_k^e) ∘ expand (p^e)`: both are ring maps
agreeing on `C r` (`(C r)^q = C (r^q)`) and on `X i` (`(X i)^q`). -/
theorem MvPolynomial.iterateFrobenius_eq_map_comp_expand (k : Type u) [CommRing k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (d e : ℕ) :
    iterateFrobenius (MvPolynomial (Fin d) k) p e =
      (MvPolynomial.map (iterateFrobenius k p e)).comp
        ((MvPolynomial.expand (p ^ e) : MvPolynomial (Fin d) k →ₐ[k] MvPolynomial (Fin d) k) :
          MvPolynomial (Fin d) k →+* MvPolynomial (Fin d) k) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [iterateFrobenius_def, MvPolynomial.map_C]
  · simp [iterateFrobenius_def, MvPolynomial.expand_X, MvPolynomial.map_X]

/-- **`k` perfect ⇒ the Frobenius of `k[x_1..x_d]` is finite** (the step "`P^{1/q}` is a finite
`P`-module" in the proof of Stacks 0333): `Frob^e = map (Frob_k^e) ∘ expand (p^e)`, `expand` is finite
(`MvPolynomial.expand_finite`, generated by the monomials with exponents `< q`), and `map (Frob_k^e)` is
surjective (`k` perfect), hence finite. -/
theorem MvPolynomial.iterateFrobenius_finite_of_perfectField (k : Type u) [Field k] [PerfectField k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (d e : ℕ) :
    (iterateFrobenius (MvPolynomial (Fin d) k) p e).Finite := by
  rw [MvPolynomial.iterateFrobenius_eq_map_comp_expand]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ ?_)
    (MvPolynomial.expand_finite k d (p ^ e) (expChar_pow_pos k p e))
  exact MvPolynomial.map_surjective _ (bijective_iterateFrobenius k p e).2

/-! ### N-2 for polynomial rings over a perfect field (Stacks 0333) -/

/-- **N-2 for `k[x_1..x_d]`, `k` a perfect field of characteristic `p`** (Stacks 0333): `F = Frac P`,
`L/F` finite; then `integralClosure P L` is a finite `P`-module.

Proof: let `S := separableClosure F L`; `L/S` is purely inseparable and finite, so choose `q = p^e`
with `∀ y ∈ L, y^q ∈ S`. `C := integralClosure P S` is a finite `P`-module by 032L
(`IsIntegralClosure.finite`; `S/F` finite separable, `P` Noetherian and integrally closed).
`ψ : integralClosure P L → C, y ↦ y^q` is an injective ring map (Frobenius is injective) with
`ψ ∘ algebraMap P _ = algebraMap P C ∘ Frob_P^e`; the right-hand side is finite (`Frob_P^e` is finite
since `k` is perfect) and `P` is Noetherian, so `algebraMap P (integralClosure P L)` is finite
(`RingHom.Finite.of_comp_injective`). -/
theorem MvPolynomial.module_finite_integralClosure_of_perfectField (k : Type u) [Field k]
    [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ)
    (F : Type v) [Field F] [Algebra (MvPolynomial (Fin d) k) F]
    [IsFractionRing (MvPolynomial (Fin d) k) F]
    (L : Type w) [Field L] [Algebra F L] [Algebra (MvPolynomial (Fin d) k) L]
    [IsScalarTower (MvPolynomial (Fin d) k) F L] [FiniteDimensional F L] :
    Module.Finite (MvPolynomial (Fin d) k) ↥(integralClosure (MvPolynomial (Fin d) k) L) := by
  classical
  haveI : CharP F p :=
    charP_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Fin d) k) F) p
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  haveI : CharP (separableClosure F L) p :=
    charP_of_injective_algebraMap (algebraMap F (separableClosure F L)).injective p
  obtain ⟨e, he⟩ :=
    IsPurelyInseparable.exists_pow_mem_of_finiteDimensional (separableClosure F L) L p
  haveI : IsScalarTower (MvPolynomial (Fin d) k) (separableClosure F L) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hC : Module.Finite (MvPolynomial (Fin d) k)
      ↥(integralClosure (MvPolynomial (Fin d) k) (separableClosure F L)) :=
    IsIntegralClosure.finite (MvPolynomial (Fin d) k) F (separableClosure F L) _
  have hφ : (iterateFrobenius (MvPolynomial (Fin d) k) p e).Finite :=
    MvPolynomial.iterateFrobenius_finite_of_perfectField k p d e
  have hcomp : ((algebraMap (MvPolynomial (Fin d) k)
      ↥(integralClosure (MvPolynomial (Fin d) k) (separableClosure F L))).comp
        (iterateFrobenius (MvPolynomial (Fin d) k) p e)).Finite :=
    (RingHom.finite_algebraMap.mpr hC).comp hφ
  have hmem : ∀ y : L, y ^ p ^ e ∈ separableClosure F L := fun y => by
    obtain ⟨z, hz⟩ := he y
    rw [← hz]
    exact z.2
  have hint : ∀ y : ↥(integralClosure (MvPolynomial (Fin d) k) L),
      IsIntegral (MvPolynomial (Fin d) k)
        (⟨y.1 ^ p ^ e, hmem y.1⟩ : separableClosure F L) := fun y =>
    (isIntegral_algebraMap_iff (R := MvPolynomial (Fin d) k) (A := separableClosure F L) (B := L)
      (x := ⟨y.1 ^ p ^ e, hmem y.1⟩) (algebraMap (separableClosure F L) L).injective).mp
      ((show IsIntegral (MvPolynomial (Fin d) k) y.1 from y.2).pow (p ^ e))
  let ψ : ↥(integralClosure (MvPolynomial (Fin d) k) L) →+*
      ↥(integralClosure (MvPolynomial (Fin d) k) (separableClosure F L)) :=
    { toFun := fun y => ⟨⟨y.1 ^ p ^ e, hmem y.1⟩, hint y⟩
      map_one' := Subtype.ext (Subtype.ext (one_pow _))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (mul_pow _ _ _))
      map_zero' := Subtype.ext (Subtype.ext (zero_pow (expChar_pow_pos L p e).ne'))
      map_add' := fun a b => Subtype.ext (Subtype.ext (add_pow_char_pow _ _ p e)) }
  have hψ : Function.Injective ψ := fun a b h => by
    apply Subtype.ext
    have h' : a.1 ^ p ^ e = b.1 ^ p ^ e :=
      congrArg (fun z : ↥(integralClosure (MvPolynomial (Fin d) k) (separableClosure F L)) =>
        (z.1 : L)) h
    exact iterateFrobenius_inj L p e h'
  have heq : ψ.comp (algebraMap (MvPolynomial (Fin d) k)
      ↥(integralClosure (MvPolynomial (Fin d) k) L)) =
      (algebraMap (MvPolynomial (Fin d) k)
        ↥(integralClosure (MvPolynomial (Fin d) k) (separableClosure F L))).comp
        (iterateFrobenius (MvPolynomial (Fin d) k) p e) := by
    refine RingHom.ext fun x => Subtype.ext (Subtype.ext ?_)
    change (algebraMap (MvPolynomial (Fin d) k) L x) ^ p ^ e
      = algebraMap (MvPolynomial (Fin d) k) L (iterateFrobenius (MvPolynomial (Fin d) k) p e x)
    rw [iterateFrobenius_def, map_pow]
  have hN : (algebraMap (MvPolynomial (Fin d) k)
      ↥(integralClosure (MvPolynomial (Fin d) k) L)).Finite :=
    RingHom.Finite.of_comp_injective _ ψ hψ (heq ▸ hcomp)
  exact RingHom.finite_algebraMap.mp hN

/-! ### N-2 for finite type domains (Stacks 0335, perfect field of characteristic `p`) -/

/-- **N-2 in characteristic `p`**: `k` a perfect field of characteristic `p > 0`, `A` a finite type
`k`-algebra which is a domain, `K = Frac A`, `L/K` finite; then the integral closure of `A` in `L` is a
finite `A`-module.

Proof (Stacks 0335 + 0333, step by step as in the Lean proof):
1. Noether normalization (Mathlib `exists_finite_inj_algHom_of_fg`): there are `d` and an injective
   `k`-algebra map `P := k[x_1,…,x_d] → A` with `A` a finite `P`-module. Let `F := Frac P`; `K/F` is
   finite (`Module.Finite.of_isLocalization`, as in step 2 of
   `Ring.module_finite_integralClosure_of_finiteType`), hence `L/F` is finite (`Module.Finite.trans`).
2. `MvPolynomial.module_finite_integralClosure_of_perfectField` (Stacks 0333): `integralClosure P L`
   is a finite `P`-module.
3. `A` is integral over `P`, so `integralClosure A L = integralClosure P L` (as subsets of `L`:
   `isIntegral_trans` and `IsIntegral.tower_top`); hence `integralClosure A L` is a finite `P`-module
   and therefore a finite `A`-module (`Module.Finite.of_restrictScalars_finite`). -/
theorem Ring.module_finite_integralClosure_of_finiteType_of_charP (k : Type u) [Field k]
    [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    Module.Finite A ↥(integralClosure A L) := by
  obtain ⟨s, g, hinj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hgfin' : (g.toRingHom).Finite := hgfin
  have hinj' : Function.Injective (g.toRingHom) := hinj
  algebraize [g.toRingHom]
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj'
  letI : Algebra (MvPolynomial (Fin s) k) K :=
    ((algebraMap A K).comp (algebraMap (MvPolynomial (Fin s) k) A)).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) A K := .of_algebraMap_eq fun _ => rfl
  letI : Algebra (MvPolynomial (Fin s) k) L :=
    ((algebraMap A L).comp (algebraMap (MvPolynomial (Fin s) k) A)).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) A L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (MvPolynomial (Fin s) k) K L :=
    .of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply A K L (algebraMap _ A x)
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) K := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq _ A K]
    exact (FaithfulSMul.algebraMap_injective A K).comp hinj'
  letI := FractionRing.liftAlgebra (MvPolynomial (Fin s) k) K
  haveI := FractionRing.isScalarTower_liftAlgebra (MvPolynomial (Fin s) k) K
  haveI : Module.Finite (FractionRing (MvPolynomial (Fin s) k)) K :=
    Module.Finite.of_isLocalization (MvPolynomial (Fin s) k) A (MvPolynomial (Fin s) k)⁰
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing (MvPolynomial (Fin s) k)) K)).toAlgebra
  haveI : IsScalarTower (FractionRing (MvPolynomial (Fin s) k)) K L :=
    .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k) K L x,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k)
          (FractionRing (MvPolynomial (Fin s) k)) K x]
      rfl
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L := Module.Finite.trans K L
  have hPC : Module.Finite (MvPolynomial (Fin s) k)
      ↥(integralClosure (MvPolynomial (Fin s) k) L) :=
    MvPolynomial.module_finite_integralClosure_of_perfectField k p s
      (FractionRing (MvPolynomial (Fin s) k)) L
  have hmod : Module.Finite (MvPolynomial (Fin s) k) ↥(integralClosure A L) := by
    refine Module.Finite.of_surjective
      ({ toFun := fun x =>
            (⟨x.1, (show IsIntegral (MvPolynomial (Fin s) k) x.1 from x.2).tower_top⟩ :
              ↥(integralClosure A L))
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } :
        ↥(integralClosure (MvPolynomial (Fin s) k) L) →ₗ[MvPolynomial (Fin s) k]
          ↥(integralClosure A L)) ?_
    rintro ⟨x, hx⟩
    exact ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) A _

/-- **N-1 over a perfect field**: `k` a perfect field, `A` a finite type `k`-algebra which is a domain,
`K = Frac A`; then the integral closure of `A` in `K` (the normalization `Ã`) is a finite `A`-module.
By characteristic: in characteristic `0` use `Ring.module_finite_integralClosure_of_finiteType`
(module `NormalizationFiniteNagata`), in characteristic `p` use
`Ring.module_finite_integralClosure_of_finiteType_of_charP` with `L = K`. Reference: Stacks 0335. -/
theorem Ring.module_finite_integralClosure_of_finiteType_of_perfectField (k : Type u) [Field k]
    [PerfectField k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A ↥(integralClosure A K) := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact Ring.module_finite_integralClosure_of_finiteType k A K
  · exact Ring.module_finite_integralClosure_of_finiteType_of_charP k p A K K

end
