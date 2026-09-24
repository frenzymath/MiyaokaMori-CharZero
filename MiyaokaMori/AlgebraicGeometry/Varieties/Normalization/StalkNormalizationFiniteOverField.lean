import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.PolynomialRingN2
import MiyaokaMori.RingTheory.Dimension.NormalizationFiniteNagata

/-! # Finiteness of the normalization of the stalks of a scheme locally of finite type over a field

Input for the key formula (Stacks 0AYC): the tame symbol `Ring.tameSymbol` of this library needs
`Module.Finite O_{X,w} (integralClosure O_{X,w} K(X))` (finite normalization; used for 0EAN), and Stacks 0EAX
needs the same for `O_{X,z}` and its localizations.

Source: Stacks 0AYC proof, first sentence of the second paragraph ("`B_i` is a Nagata ring ... its
normalization is finite"); Stacks, Algebra, "Nagata and Japanese rings": a field is Nagata, an algebra of
finite type over a Nagata ring is Nagata (Proposition 10.162.16, tag 0335), a localization of a Nagata ring is
Nagata (Lemma 10.162.7, tag 032U), and a Nagata domain is N-1 (its integral closure in its fraction field
is finite).

Proof sketch: the only non-Mathlib input is "polynomial rings over a field are N-2", packaged as
`Field.PolynomialRingsN2 K` and provided for every field by `Field.polynomialRingsN2` (in
characteristic `p` by `Field.polynomialRingsN2_of_charP`, in characteristic `0` by Mathlib's
`IsIntegralClosure.finite`). Everything else is Noether normalization, Stacks 0307
(`Ring.module_finite_integralClosure_isLocalization`) and affine-open bookkeeping.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

/-- **N-1 for finite type domains over an arbitrary field, given N-2 for polynomial rings**
(Stacks 0335, the case `p = 0` of "finite type over a Nagata ring is Nagata"; the classical statement
"a finitely generated domain over a field has finite normalization", E. Noether).

Statement: `k` a field with `Field.PolynomialRingsN2 k` (for every field: `Field.polynomialRingsN2`),
`A` a domain of finite type over `k`, `K = Frac A`. Then `integralClosure A K` is a finite `A`-module.

Proof (matching the Lean; it is the proof of `Ring.module_finite_integralClosure_of_finiteType_of_charP`
in `FiniteTypeDomainIntegralClosureFiniteCharP` with `L = K` and the perfect-field
input replaced by `hk`):
1. Noether normalization (Mathlib `exists_finite_inj_algHom_of_fg`): `s : ℕ` and an injective `k`-algebra
   map `P := k[x_1, …, x_s] → A` with `A` a finite `P`-module.
2. `K` is a `P`-algebra through `A`, `P → K` is injective; `A` is integral over `P`, so
   `K = Frac A` is a localization of `A` at `P⁰` (Mathlib instance in `RingTheory/Algebraic/Integral.lean`)
   and `Module.Finite.of_isLocalization` gives `FiniteDimensional (Frac P) K`.
3. `hk s (Frac P) K`: `integralClosure P K` is a finite `P`-module.
4. As subsets of `K`, `integralClosure P K = integralClosure A K` (`A/P` integral: `isIntegral_trans`,
   `IsIntegral.tower_top`), so `integralClosure A K` is a finite `P`-module (image of a surjective
   `P`-linear map), hence a finite `A`-module (`Module.Finite.of_restrictScalars_finite`).

Edge cases: `s = 0` (`A` a finite field extension of `k`, `K = A`, integral closure `A`); `A = k`. -/
theorem Ring.module_finite_integralClosure_of_finiteType_of_polynomialRingsN2 (k : Type u) [Field k]
    (hk : Field.PolynomialRingsN2 k)
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
    hk s (FractionRing (MvPolynomial (Fin s) k)) K
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

/-- **Finite normalization of the stalks (Stacks 0335 + 032U), stated in `K(X)`.**

Statement: `X` integral, locally of finite type over a field `K` (any characteristic), `x : X`. Then the
integral closure of `O_{X,x}` in `K(X)` is a finite `O_{X,x}`-module.

Natural-language proof (Stacks, Algebra, §"Nagata and Japanese rings"; matching the Lean):
1. Choose an affine open `U = Spec A ∋ x` (the chart of `X.affineCover` through `x`); `A = Γ(X, U)` is a
   finite type `K`-algebra (`Scheme.Hom.finiteType_appLE` for `π` on `⊤ ≥ U`, composed with
   `K ≅ Γ(Spec K, ⊤)`), a domain (`X` integral) with fraction field `K(X)`
   (`functionField_isFractionRing_of_isAffineOpen`), and `O_{X,x} = A_p` for the prime `p` of `x`
   (`IsAffineOpen.isLocalization_stalk`); `A → O_{X,x} → K(X)` is a scalar tower
   (`functionField_isScalarTower`).
2. `A` is N-1 (tag 0335, `p = 0`): the integral closure `Ã` of `A` in `K(X)` is finite over `A`. This is
   `Ring.module_finite_integralClosure_of_finiteType_of_polynomialRingsN2` (above) applied with
   `Field.polynomialRingsN2 K` (N-2 for polynomial rings over an arbitrary field; in characteristic
   `p` this is `Field.polynomialRingsN2_of_charP`, E. Noether's `q`-th root argument, tag 032L–0333).
3. Localization (Stacks 0307 = Mathlib `IsLocalization.integralClosure`, packaged as
   `Ring.module_finite_integralClosure_isLocalization`): `integralClosure A_p K(X) = (Ã)_p`, and a
   localization of a finite module is finite. Hence `Module.Finite O_{X,x} (integralClosure O_{X,x} K(X))`.

Compare `AlgebraicGeometry.Scheme.module_finite_integralClosure_stalk`, the same statement **with
`[CharZero K]`** and with `FractionRing O_{X,x}` in place of `K(X)`; it is not used here.

Edge cases: `x` the generic point: `O_{X,x} = K(X)` is a field, its integral closure is itself, finite.
`X = Spec K`: trivial. -/
theorem AlgebraicGeometry.keyFormula_module_finite_integralClosure_stalk {X : Scheme.{u}} [IsIntegral X]
    (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType π] (x : X) :
    Module.Finite (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) X.functionField) := by
  -- Step 1: an affine open through `x`.
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  let xU : U := ⟨x, X.affineCover.covers x⟩
  haveI : Nonempty U := ⟨xU⟩
  -- `A = Γ(X, U)` is a finite type `K`-algebra.
  let φ : K →+* Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ π.appLE ⊤ U le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (π.appLE ⊤ U le_top).hom.FiniteType :=
      π.finiteType_appLE (isAffineOpen_top _) hU _
    have h2 : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  letI : Algebra K Γ(X, U) := φ.toAlgebra
  haveI : Algebra.FiniteType K Γ(X, U) := hφ
  -- `K(X) = Frac A`.
  haveI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  -- Step 2: `Ã` is finite over `A`.
  have hA : Module.Finite Γ(X, U) ↥(integralClosure Γ(X, U) X.functionField) :=
    Ring.module_finite_integralClosure_of_finiteType_of_polynomialRingsN2 K
      (Field.polynomialRingsN2 K) Γ(X, U) X.functionField
  -- Step 3: `O_{X,x} = A_p` and Stacks 0307.
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf xU
  haveI := hU.isLocalization_stalk xU
  haveI := functionField_isScalarTower X U xU
  exact Ring.module_finite_integralClosure_isLocalization
    (IsFractionRing.injective Γ(X, U) X.functionField)
    (hU.primeIdealOf xU).asIdeal.primeCompl (hU.primeIdealOf xU).asIdeal.primeCompl_le_nonZeroDivisors hA

end
