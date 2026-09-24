import MiyaokaMori.Prelude
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Perfect

/-! # Finiteness of the normalization of a finite type domain (characteristic zero)

The normalization of a domain (essentially) of finite type over a field is finite, and this passes
along localization. These statements provide, in the geometric application (`X` locally of finite
type over a field `k`, `A = O_{X,z}`), the hypotheses `hB : Module.Finite A (integralClosure A (FractionRing A))`
of Stacks 0EAX and `hfin` (finiteness of the normalization at every height-one prime).

**Route**: the general case needs the theory of Nagata rings (Stacks 032E–0335, not in Mathlib); since
the base field of the main theorems is an algebraically closed field of characteristic zero, we take
the **characteristic-zero version**: with `[CharZero k]`, Noether normalization + Mathlib's
`IsIntegralClosure.finite` give the conclusion directly. This is not an approximation but the instance
in characteristic zero of the genuine route Stacks 032L (the integral closure in a finite separable
extension is finite); the inseparable part (Stacks 0333) is treated in
`FiniteTypeDomainIntegralClosureFiniteCharP`.

References:
* Stacks 00OW (Noether normalization) = Mathlib `exists_finite_inj_algHom_of_fg`;
* Stacks 032L (`A` Noetherian integrally closed, `L/Frac A` finite separable ⇒ the integral closure is
  finite) = Mathlib `IsIntegralClosure.finite`;
* Stacks 0307 (integral closure commutes with localization) = Mathlib `IsLocalization.integralClosure`;
* Stacks 0335 / 032U / 032F / 0334 (Nagata rings) — cited only as the source of the general case;
  this file does not use them;
* Stacks 01T6 (stalk maps of a locally finite type morphism are essentially of finite type) = Mathlib
  `AlgebraicGeometry.LocallyOfFiniteType.stalkMap`.

Note on Mathlib: there is no `IsNagataRing` / Japanese / N-1 / N-2. `IsIntegralClosure.finite` is
applied to the polynomial ring `k[x_1..x_d]` given by Noether normalization (a UFD, hence integrally
closed, and Noetherian), not to `A` itself; and `IsLocalization.integralClosure` is exactly Stacks 0307.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped nonZeroDivisors

universe u

noncomputable section

/-! ### Auxiliary: fraction fields descend along localization -/

/-- If `S = M⁻¹R` (`M ≤ R⁰`) and `T` is a fraction field of `S`, then `T` is also a fraction field of
`R`.

Mathlib has only the converse `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization` (from
`IsFractionRing R T` deduce `IsFractionRing S T`); this is the missing other half, used in
`Ring.module_finite_integralClosure_of_essFiniteType` to replace "the fraction field of `A`" by "the
fraction field of the finite type subalgebra `R₀` of `A`". -/
theorem IsFractionRing.of_isLocalization_of_le_nonZeroDivisors
    {R : Type u} {S : Type u} {T : Type u} [CommRing R] [IsDomain R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) [IsLocalization M S] [IsFractionRing S T] :
    IsFractionRing R T := by
  have hRS : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  have hST : Function.Injective (algebraMap S T) := IsFractionRing.injective S T
  have hRT : Function.Injective (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R S T]; exact hST.comp hRS
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  refine (isLocalization_iff (nonZeroDivisors R) T).mpr
    ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩
  · rw [IsScalarTower.algebraMap_apply R S T]
    refine IsLocalization.map_units T (⟨algebraMap R S (y : R), ?_⟩ : nonZeroDivisors S)
    exact mem_nonZeroDivisors_of_ne_zero
      (by simp [map_eq_zero_iff _ hRS, nonZeroDivisors.coe_ne_zero y])
  · have hsurj : ∀ w : T, ∃ x : S × (nonZeroDivisors S),
        w * algebraMap S T (x.2 : S) = algebraMap S T x.1 := IsLocalization.surj _
    obtain ⟨⟨a, s⟩, e⟩ := hsurj z
    obtain ⟨⟨x₁, m₁⟩, e₁⟩ := IsLocalization.surj M a
    obtain ⟨⟨x₂, m₂⟩, e₂⟩ := IsLocalization.surj M (s : S)
    have hs0 : (s : S) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    have hm₂0 : algebraMap R S (m₂ : R) ≠ 0 := by
      have : (m₂ : R) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨(m₂ : R), hM m₂.2⟩
      simpa [map_eq_zero_iff _ hRS] using this
    have hx₂0 : x₂ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at e₂
      exact (mul_ne_zero hs0 hm₂0) e₂
    refine ⟨⟨x₁ * (m₂ : R), ⟨x₂ * (m₁ : R),
      mul_mem (mem_nonZeroDivisors_of_ne_zero hx₂0) (hM m₁.2)⟩⟩, ?_⟩
    have key : z * algebraMap S T (algebraMap R S (x₂ * (m₁ : R)))
        = algebraMap S T (algebraMap R S (x₁ * (m₂ : R))) := by
      have h2 : algebraMap R S (x₂ * (m₁ : R))
          = (s : S) * algebraMap R S (m₂ : R) * algebraMap R S (m₁ : R) := by
        rw [map_mul, ← e₂]
      have h1 : algebraMap R S (x₁ * (m₂ : R))
          = a * algebraMap R S (m₁ : R) * algebraMap R S (m₂ : R) := by
        rw [map_mul, ← e₁]
      rw [h1, h2, map_mul, map_mul, map_mul, map_mul]
      rw [show z * (algebraMap S T (s : S) * algebraMap S T (algebraMap R S (m₂ : R))
            * algebraMap S T (algebraMap R S (m₁ : R)))
          = (z * algebraMap S T (s : S)) * (algebraMap S T (algebraMap R S (m₂ : R))
            * algebraMap S T (algebraMap R S (m₁ : R))) by ring]
      rw [e]; ring
    simpa [IsScalarTower.algebraMap_apply R S T] using key
  · exact ⟨1, by simpa using hRT h⟩

/-! ### (N0) The finite type case: Noether normalization + `IsIntegralClosure.finite` -/

/-- **(N0)**: `k` a field of characteristic zero, `A` a finite type `k`-algebra which is a domain,
`K = Frac A`; then the integral closure of `A` in `K` (the normalization `Ã`) is a finite `A`-module.

Reference: Stacks 00OW (Noether normalization) + Stacks 032L (the integral closure in a finite
separable extension is finite).

Proof (step by step as in the Lean proof):
1. Noether normalization (Mathlib `exists_finite_inj_algHom_of_fg`) gives `s : ℕ` and an injective
   `k`-algebra map `g : P := k[x_1,…,x_s] →ₐ[k] A` with `A` a finite `P`-module.
2. Regard `K` as a `P`-algebra (via `A`); `P → K` is injective. `A` is integral, hence algebraic, over
   `P`, so Mathlib's instance `IsLocalization (Algebra.algebraMapSubmonoid A P⁰) K` applies, and
   `Module.Finite.of_isLocalization` gives `FiniteDimensional (Frac P) K`.
3. `k` of characteristic zero ⇒ `P` of characteristic zero ⇒ `Frac P` of characteristic zero ⇒ `Frac P`
   perfect ⇒ `K / Frac P` separable (`PerfectField.ofCharZero` +
   `Algebra.IsAlgebraic.isSeparable_of_perfectField`).
4. `P` is a UFD (`MvPolynomial` over a field), hence integrally closed, and Noetherian (Hilbert basis
   theorem); so `IsIntegralClosure.finite P (Frac P) K _` gives `Module.Finite P (integralClosure P K)`.
5. As subsets of `K`, `integralClosure P K = integralClosure A K` (`A/P` integral; `isIntegral_trans`
   and `IsIntegral.tower_top`), so `integralClosure A K` is a finite `P`-module and hence a finite
   `A`-module (`Module.Finite.of_restrictScalars_finite`). -/
theorem Ring.module_finite_integralClosure_of_finiteType (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A ↥(integralClosure A K) := by
  obtain ⟨s, g, hinj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hgfin' : (g.toRingHom).Finite := hgfin
  have hinj' : Function.Injective (g.toRingHom) := hinj
  algebraize [g.toRingHom]
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj'
  letI : Algebra (MvPolynomial (Fin s) k) K :=
    ((algebraMap A K).comp (algebraMap (MvPolynomial (Fin s) k) A)).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) A K := .of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) K := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq _ A K]
    exact (FaithfulSMul.algebraMap_injective A K).comp hinj'
  letI := FractionRing.liftAlgebra (MvPolynomial (Fin s) k) K
  haveI := FractionRing.isScalarTower_liftAlgebra (MvPolynomial (Fin s) k) K
  haveI : Module.Finite (FractionRing (MvPolynomial (Fin s) k)) K :=
    Module.Finite.of_isLocalization (MvPolynomial (Fin s) k) A (MvPolynomial (Fin s) k)⁰
  have hPC : Module.Finite (MvPolynomial (Fin s) k)
      ↥(integralClosure (MvPolynomial (Fin s) k) K) :=
    IsIntegralClosure.finite (MvPolynomial (Fin s) k)
      (FractionRing (MvPolynomial (Fin s) k)) K _
  have hmod : Module.Finite (MvPolynomial (Fin s) k) ↥(integralClosure A K) := by
    refine Module.Finite.of_surjective
      ({ toFun := fun x =>
            (⟨x.1, (show IsIntegral (MvPolynomial (Fin s) k) x.1 from x.2).tower_top⟩ :
              ↥(integralClosure A K))
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } :
        ↥(integralClosure (MvPolynomial (Fin s) k) K) →ₗ[MvPolynomial (Fin s) k]
          ↥(integralClosure A K)) ?_
    rintro ⟨x, hx⟩
    exact ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) A _

/-! ### Integral closure along localization (Stacks 0307) -/

/-- **(N0')**: a consequence of "integral closure commutes with localization" (Stacks 0307 = Mathlib
`IsLocalization.integralClosure`): `R` a domain, `A = M⁻¹R` (`M ≤ R⁰`, and `K` a field above both), if
the integral closure of `R` in `K` is finite over `R`, then the integral closure of `A` in `K` is finite
over `A`. -/
theorem Ring.module_finite_integralClosure_isLocalization
    {R : Type u} [CommRing R] [IsDomain R] {A : Type u} [CommRing A] [Algebra R A]
    {K : Type u} [Field K] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    (hinj : Function.Injective (algebraMap R K))
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) [IsLocalization M A]
    (h : Module.Finite R ↥(integralClosure R K)) :
    Module.Finite A ↥(integralClosure A K) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid K M) K := by
    refine IsLocalization.of_le_isUnit ?_
    rintro _ ⟨m, hm, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    simpa [map_eq_zero_iff _ hinj] using nonZeroDivisors.coe_ne_zero ⟨m, hM hm⟩
  letI : Algebra ↥(integralClosure R K) ↥(integralClosure A K) :=
    RingHom.toAlgebra
      { toFun := fun x => (⟨x.1, (show IsIntegral R x.1 from x.2).tower_top⟩ :
          ↥(integralClosure A K))
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
  haveI : IsScalarTower ↥(integralClosure R K) ↥(integralClosure A K) K :=
    .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R ↥(integralClosure R K) ↥(integralClosure A K) :=
    .of_algebraMap_eq fun _ => rfl
  haveI := IsLocalization.integralClosure (R := R) (S := K) (Rf := A) (Sf := K) M
  exact Module.Finite.of_isLocalization R ↥(integralClosure R K) M

/-! ### (N1) The essentially finite type case -/

/-- **(N1)**: `k` a field of **characteristic zero**, `A` a domain essentially of finite type over `k`
(`Algebra.EssFiniteType`, i.e. a localization of some finite type `k`-algebra), `K = Frac A`; then the
integral closure of `A` in `K` (the normalization `Ã`) is a finite `A`-module.

Reference: Stacks 00OW + 032L + 0307 (characteristic-zero version; the general case is the Nagata
theory of Stacks 0335(1)(5) + 032U + 032F/0334, not needed here).

Proof: let `R₀ := Algebra.EssFiniteType.subalgebra k A` (a finite type `k`-subalgebra of `A`, hence a
domain) and `M := Algebra.EssFiniteType.submonoid k A`, so that `A = M⁻¹R₀`. Elements of `M` are
invertible in `A`, hence nonzero in `R₀`, i.e. `M ≤ R₀⁰`; by
`IsFractionRing.of_isLocalization_of_le_nonZeroDivisors`, `K` is also a fraction field of `R₀`.
Apply (N0) to `R₀` to get `Module.Finite R₀ (integralClosure R₀ K)`, then (N0') (Stacks 0307) to
localize along `M`.

The hypothesis `[CharZero k]` costs nothing for the applications: the base fields of the main
theorems are algebraically closed of characteristic zero. -/
theorem Ring.module_finite_integralClosure_of_essFiniteType (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.EssFiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A ↥(integralClosure A K) := by
  haveI : IsLocalization (Algebra.EssFiniteType.submonoid k A) A :=
    Algebra.EssFiniteType.isLocalization k A
  have hR₀A : Function.Injective
      (algebraMap ↥(Algebra.EssFiniteType.subalgebra k A) A) := fun _ _ h => Subtype.ext h
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hinj : Function.Injective (algebraMap ↥(Algebra.EssFiniteType.subalgebra k A) K) := by
    rw [IsScalarTower.algebraMap_eq ↥(Algebra.EssFiniteType.subalgebra k A) A K]
    exact hAK.comp hR₀A
  have hM : Algebra.EssFiniteType.submonoid k A
      ≤ nonZeroDivisors ↥(Algebra.EssFiniteType.subalgebra k A) := by
    intro x hx
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rintro rfl
    have hu : IsUnit (algebraMap ↥(Algebra.EssFiniteType.subalgebra k A) A 0) := hx
    rw [map_zero] at hu
    exact (not_isUnit_zero (M₀ := A)) hu
  haveI : IsFractionRing ↥(Algebra.EssFiniteType.subalgebra k A) K :=
    IsFractionRing.of_isLocalization_of_le_nonZeroDivisors (S := A)
      (Algebra.EssFiniteType.submonoid k A) hM
  have h0 : Module.Finite ↥(Algebra.EssFiniteType.subalgebra k A)
      ↥(integralClosure ↥(Algebra.EssFiniteType.subalgebra k A) K) :=
    Ring.module_finite_integralClosure_of_finiteType k _ K
  exact Ring.module_finite_integralClosure_isLocalization hinj
    (Algebra.EssFiniteType.submonoid k A) hM h0

/-! ### (N2) Localization at a prime -/

/-- **(N2)**: a consequence of "integral closure commutes with localization" (Stacks 0307): if `A` is a
Noetherian domain whose normalization `Ã` is finite over `A`, then for every prime `q` the
normalization of `A_q` is finite over `A_q`. This is the hypothesis `hfin` in the signatures of
`Ring.tameOrd` / `Ring.tameSymbol`, derived from the hypothesis `hB` of 0EAX. -/
theorem Ring.module_finite_integralClosure_localization {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hB : Module.Finite A ↥(integralClosure A (FractionRing A)))
    (q : PrimeSpectrum A) :
    Module.Finite (Localization.AtPrime q.asIdeal)
      ↥(integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :=
  Ring.module_finite_integralClosure_isLocalization
    (IsFractionRing.injective A (FractionRing A))
    q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors hB

/-! ### (N3) Geometric form: stalks of a scheme locally of finite type -/

/-- **(N3)**: `X` locally of finite type over a field `k` of **characteristic zero**, `x ∈ X` with
`O_{X,x}` a domain; then the normalization of `O_{X,x}` is finite over `O_{X,x}`. This is the form
used in `AlgebraicGeometry.keyFormula_cycle_identity`: there `A := O_{X,z}`, this statement gives the
finiteness hypothesis of 0EAX, and `Ring.module_finite_integralClosure_localization` gives its
version at every prime.

Reference: Stacks 01T6 (the stalk maps of a locally finite type morphism are essentially of finite
type) + (N1). The geometric form is Stacks 035S.

Proof (step by step as in the Lean proof):
1. `AlgebraicGeometry.LocallyOfFiniteType.stalkMap π x : (π.stalkMap x).hom.EssFiniteType` says that
   the stalk map `O_{Spec k, π x} → O_{X,x}` of `π` at `x` is essentially of finite type. As an
   instance: after `letI := (π.stalkMap x).hom.toAlgebra`,
   `rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]`.
2. Source side: `k → O_{Spec k, π x}` is the localization of `k` at the prime `π x`. Mathlib provides
   this directly in the shape of stalks of `Spec R`:
   `AlgebraicGeometry.StructureSheaf.stalkAlgebra R p : Algebra R ((Spec R).presheaf.stalk p)` and
   `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R p : IsLocalization.AtPrime _ p.asIdeal`
   (used the same way in `ringKrullDim_stalk_eq_coheight`); with `R := k`, `p := π.base x` both
   terms typecheck (`↥(Spec (CommRingCat.of k))` and `PrimeSpectrum k` are definitionally equal at
   default transparency; only the instance `(π.base x).asIdeal.IsPrime` has to be supplied by hand
   from the structure field `(π.base x).isPrime`, since instance search at reducible transparency
   does not see through the type of the point). Then
   `Algebra.EssFiniteType.of_isLocalization _ (π.base x).asIdeal.primeCompl` gives
   `Algebra.EssFiniteType k (O_{Spec k, π x})`.
3. Composition: define `Algebra k O_{X,x}` as the `toAlgebra` of the composite
   `(π.stalkMap x).hom.comp (algebraMap k _)`, balance with
   `IsScalarTower.of_algebraMap_eq fun _ => rfl`, and `Algebra.EssFiniteType.comp` gives
   `Algebra.EssFiniteType k ↥(X.presheaf.stalk x)`.
4. Apply (N1) `Ring.module_finite_integralClosure_of_essFiniteType k _ (FractionRing _)`.

Remark: Mathlib's `stalkAlgebra` / `IsLocalization.to_stalk` are usable as explicit terms (not via
instance search) on stalks of `Spec R`; one only has to supply the `IsPrime` instance. -/
theorem AlgebraicGeometry.Scheme.module_finite_integralClosure_stalk {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [CharZero k] (π : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType π] (x : X) [IsDomain ↥(X.presheaf.stalk x)] :
    Module.Finite ↥(X.presheaf.stalk x)
      ↥(integralClosure ↥(X.presheaf.stalk x) (FractionRing ↥(X.presheaf.stalk x))) := by
  -- Step 2: `k → O_{Spec k, π x}` is the localization at the prime `π x` (Mathlib's
  -- `StructureSheaf.stalkAlgebra` / `IsLocalization.to_stalk`, stated on `Spec R` as in
  -- `Mathlib/AlgebraicGeometry/Properties.lean`, `ringKrullDim_stalk_eq_coheight`).
  letI : Algebra k ↥((AlgebraicGeometry.Spec (CommRingCat.of k)).presheaf.stalk (π.base x)) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra k (π.base x)
  -- the point `π x : ↥(Spec k)` is a prime of `k`, but instance search does not see it as such
  haveI : (π.base x).asIdeal.IsPrime := (π.base x).isPrime
  haveI : IsLocalization.AtPrime
      ↥((AlgebraicGeometry.Spec (CommRingCat.of k)).presheaf.stalk (π.base x)) (π.base x).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk k (π.base x)
  haveI : Algebra.EssFiniteType k
      ↥((AlgebraicGeometry.Spec (CommRingCat.of k)).presheaf.stalk (π.base x)) :=
    Algebra.EssFiniteType.of_isLocalization _ (π.base x).asIdeal.primeCompl
  -- Step 1: the stalk map is essentially of finite type (Stacks 01T6).
  letI : Algebra ↥((AlgebraicGeometry.Spec (CommRingCat.of k)).presheaf.stalk (π.base x))
      ↥(X.presheaf.stalk x) := (π.stalkMap x).hom.toAlgebra
  haveI : Algebra.EssFiniteType
      ↥((AlgebraicGeometry.Spec (CommRingCat.of k)).presheaf.stalk (π.base x))
      ↥(X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact AlgebraicGeometry.LocallyOfFiniteType.stalkMap π x
  -- Step 3: compose.
  letI : Algebra k ↥(X.presheaf.stalk x) :=
    ((π.stalkMap x).hom.comp (algebraMap k
      ↥((AlgebraicGeometry.Spec (CommRingCat.of k)).presheaf.stalk (π.base x)))).toAlgebra
  haveI : IsScalarTower k ↥((AlgebraicGeometry.Spec (CommRingCat.of k)).presheaf.stalk (π.base x))
      ↥(X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType k ↥(X.presheaf.stalk x) :=
    Algebra.EssFiniteType.comp k
      ↥((AlgebraicGeometry.Spec (CommRingCat.of k)).presheaf.stalk (π.base x)) ↥(X.presheaf.stalk x)
  -- Step 4: (N1).
  exact Ring.module_finite_integralClosure_of_essFiniteType k _ (FractionRing _)

end
