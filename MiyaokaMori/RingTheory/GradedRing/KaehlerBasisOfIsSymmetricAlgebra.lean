import MiyaokaMori.Prelude
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Kähler differentials of the symmetric algebra of a free module

Kähler differentials of a symmetric algebra of a free module: if `f : M →ₗ[R] A` makes `A` the
symmetric algebra of `M` (`IsSymmetricAlgebra f`, Mathlib) and `b` is an `R`-basis of `M`, then
`Ω[A⁄R]` is a free `A`-module with basis `d(f(b i))`. This is Eisenbud, *Commutative Algebra*,
Prop. 16.1 (`Ω_{R[x_1,…,x_n]/R}` is free on `dx_i`), Mathlib `KaehlerDifferential.mvPolynomialBasis`,
transported along `A ≃ₐ[R] MvPolynomial I R` (`IsSymmetricAlgebra.equiv`, `SymmetricAlgebra.equivMvPolynomial`).

Proof: the coordinate derivation of `R[X_I]` is transported to a derivation `A → A^{(I)}`
(`coordDerivation`), whose lift `Ω[A⁄R] → A^{(I)}` (`toCoords`) is inverse to `e_i ↦ D (f (b i))`
(`ofCoords`); the basis is `Module.Basis.ofRepr` of this equivalence.

Used for the affine-local computation of the cotangent sheaf of the total space of a vector bundle
(`Ω_{A(U)/Γ(U)}` free on `d ℓ_i`, `A(U) = Sym_{Γ(U)} Γ(U, V^∨)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace KaehlerDifferential

variable {R M A : Type*} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]
  {f : M →ₗ[R] A} (hf : IsSymmetricAlgebra f) {I : Type*} (b : Module.Basis I R M)

/-- `A ≃ₐ[R] R[X_I]`, `f (b i) ↦ X i`. -/
def symEquivMvPolynomial : A ≃ₐ[R] MvPolynomial I R :=
  hf.equiv.symm.trans (SymmetricAlgebra.equivMvPolynomial b)

theorem symEquivMvPolynomial_apply_f (i : I) :
    symEquivMvPolynomial hf b (f (b i)) = MvPolynomial.X i := by
  simp [symEquivMvPolynomial]

theorem symEquivMvPolynomial_symm_X (i : I) :
    (symEquivMvPolynomial hf b).symm (MvPolynomial.X i) = f (b i) := by
  rw [AlgEquiv.symm_apply_eq, symEquivMvPolynomial_apply_f]

/-- transport of the coordinate derivation of `R[X_I]` to `A`, as an `R`-linear map -/
def coordDerivationLinear : A →ₗ[R] (I →₀ A) :=
  (Finsupp.mapRange.linearMap (symEquivMvPolynomial hf b).symm.toLinearMap) ∘ₗ
    (MvPolynomial.mkDerivation R (fun i : I => Finsupp.single i (1 : MvPolynomial I R))).toLinearMap ∘ₗ
    (symEquivMvPolynomial hf b).toLinearMap

theorem coordDerivationLinear_apply (a : A) :
    coordDerivationLinear hf b a = Finsupp.mapRange (symEquivMvPolynomial hf b).symm (map_zero _)
      (MvPolynomial.mkDerivation R (fun i : I => Finsupp.single i (1 : MvPolynomial I R))
        (symEquivMvPolynomial hf b a)) := rfl

theorem mapRange_symm_smul' (q : MvPolynomial I R) (v : I →₀ MvPolynomial I R) :
    Finsupp.mapRange (symEquivMvPolynomial hf b).symm (map_zero _) (q • v) =
      (symEquivMvPolynomial hf b).symm q • Finsupp.mapRange (symEquivMvPolynomial hf b).symm (map_zero _) v := by
  ext i
  simp [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]

theorem mapRange_symm_smul (a : A) (v : I →₀ MvPolynomial I R) :
    Finsupp.mapRange (symEquivMvPolynomial hf b).symm (map_zero _) (symEquivMvPolynomial hf b a • v) =
      a • Finsupp.mapRange (symEquivMvPolynomial hf b).symm (map_zero _) v := by
  rw [mapRange_symm_smul', AlgEquiv.symm_apply_apply]

/-- the coordinate derivation `A → A^{(I)}` -/
def coordDerivation : Derivation R A (I →₀ A) where
  toLinearMap := coordDerivationLinear hf b
  map_one_eq_zero' := by
    simp [coordDerivationLinear_apply]
  leibniz' := fun x y => by
    simp only [coordDerivationLinear_apply, map_mul, Derivation.leibniz]
    rw [Finsupp.mapRange_add (map_add _), mapRange_symm_smul, mapRange_symm_smul]

theorem coordDerivation_apply (a : A) :
    coordDerivation hf b a = Finsupp.mapRange (symEquivMvPolynomial hf b).symm (map_zero _)
      (MvPolynomial.mkDerivation R (fun i : I => Finsupp.single i (1 : MvPolynomial I R))
        (symEquivMvPolynomial hf b a)) := rfl

theorem coordDerivation_f (i : I) :
    coordDerivation hf b (f (b i)) = Finsupp.single i 1 := by
  rw [coordDerivation_apply, symEquivMvPolynomial_apply_f, MvPolynomial.mkDerivation_X,
    Finsupp.mapRange_single, map_one]

/-- `Ω[A⁄R] → A^{(I)}` -/
def toCoords : KaehlerDifferential R A →ₗ[A] (I →₀ A) :=
  (coordDerivation hf b).liftKaehlerDifferential

/-- `A^{(I)} → Ω[A⁄R]`, `e_i ↦ D (f (b i))` -/
def ofCoords : (I →₀ A) →ₗ[A] KaehlerDifferential R A :=
  Finsupp.linearCombination A (fun i => KaehlerDifferential.D R A (f (b i)))

theorem toCoords_ofCoords : toCoords hf b ∘ₗ ofCoords (f := f) b = LinearMap.id := by
  refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply, ofCoords,
    Finsupp.linearCombination_single, one_smul, toCoords, Derivation.liftKaehlerDifferential_comp_D,
    coordDerivation_f]

theorem ofCoords_mapRange (q : MvPolynomial I R) :
    ofCoords (f := f) b (Finsupp.mapRange (symEquivMvPolynomial hf b).symm (map_zero _)
      (MvPolynomial.mkDerivation R (fun i : I => Finsupp.single i (1 : MvPolynomial I R)) q)) =
      KaehlerDifferential.D R A ((symEquivMvPolynomial hf b).symm q) := by
  induction q using MvPolynomial.induction_on with
  | C r =>
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, Finsupp.mapRange_zero, map_zero,
      AlgEquiv.commutes, Derivation.map_algebraMap]
  | add p q hp hq =>
    rw [map_add, Finsupp.mapRange_add (map_add _), map_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    rw [Derivation.leibniz, MvPolynomial.mkDerivation_X, Finsupp.mapRange_add (map_add _), map_add,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mapRange_single, mapRange_symm_smul',
      map_smul, hp, symEquivMvPolynomial_symm_X, map_mul, Derivation.leibniz,
      symEquivMvPolynomial_symm_X]
    simp only [ofCoords, Finsupp.linearCombination_single]

theorem ofCoords_toCoords : ofCoords (f := f) b ∘ₗ toCoords hf b = LinearMap.id := by
  apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation R A)
  rintro _ ⟨a, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.id_apply, toCoords,
    Derivation.liftKaehlerDifferential_comp_D, coordDerivation_apply]
  rw [ofCoords_mapRange, AlgEquiv.symm_apply_apply]

end KaehlerDifferential

/-- If `A` is the symmetric algebra of the
free `R`-module `M` with basis `b` (through `f : M →ₗ[R] A`), then `Ω[A⁄R]` has the `A`-basis
`i ↦ D (f (b i))`.

Source: Eisenbud, Commutative Algebra, Prop. 16.1; Mathlib `KaehlerDifferential.mvPolynomialBasis`
(`Ω[R[X_i]/R]` is free on `D (X i)`, `mvPolynomialBasis_repr_D_X`).

Natural-language proof (the Lean proof follows the "Alternative" below; the first route is kept for reference). Let `P := MvPolynomial I R` and
`e : A ≃ₐ[R] P := hf.equiv.symm.trans (SymmetricAlgebra.equivMvPolynomial b)`; then
`e (f (b i)) = X i` (`IsSymmetricAlgebra.equiv_symm_apply`, `equivMvPolynomial_ι_apply`).
1. Make `P` an `A`-algebra through `e` (`e.toAlgHom.toRingHom.toAlgebra`; `IsScalarTower R A P` holds
   because `e` commutes with `algebraMap R`). Mathlib's `KaehlerDifferential.map R R A P : Ω[A⁄R] →ₗ[A] Ω[P⁄R]`
   satisfies `map (D a) = D (e a)` (`KaehlerDifferential.map_D`). Symmetrically, making `A` a
   `P`-algebra through `e.symm`, `map R R P A : Ω[P⁄R] →ₗ[P] Ω[A⁄R]` with `map (D q) = D (e.symm q)`.
   The two composites are the identity: both sides are linear and agree on the generators `D a`
   (resp. `D q`), which span (`KaehlerDifferential.span_range_derivation`); so `Ω[A⁄R] ≃ Ω[P⁄R]`
   additively, and `A`-linearly when `Ω[P⁄R]` is regarded as an `A`-module through `e`
   (`map R R A P` is `A`-linear by construction).
2. `Ω[P⁄R]` has the `P`-basis `D (X i)` (`mvPolynomialBasis R I`; `mvPolynomialBasis R I i = D (X i)`
   from `mvPolynomialBasis_repr_D_X` and `Basis.repr_self`). Change the coefficient ring along the ring
   isomorphism `e : A ≃+* P` (`Module.Basis.mapCoeffs` with the compatibility `e a • x = a • x`, which
   holds by definition of the `A`-module structure on `Ω[P⁄R]`) to get an `A`-basis of `Ω[P⁄R]` with the
   same vectors `D (X i)`.
3. Transport along the `A`-linear equivalence of step 1 (`Module.Basis.map`): the basis vector `i` is
   `map R R P A (D (X i)) = D (e.symm (X i)) = D (f (b i))`.

Alternative (avoiding step 1's inverse): define the `A`-linear map `Ω[A⁄R] → (I →₀ A)` by lifting the
derivation `a ↦ mapRange e.symm (mkDerivation R (single · 1) (e a))` and the inverse
`Finsupp.linearCombination A (fun i => D (f (b i)))`; check both composites on generators as in
`KaehlerDifferential.mvPolynomialEquiv`.

Edge cases: `I` empty — `A ≅ R`, `Ω[A⁄R] = 0`, the empty family is a basis; `R` the zero ring —
everything is trivial, any family is a basis of the zero module. -/
theorem KaehlerDifferential.exists_basis_of_isSymmetricAlgebra {R M A : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A] {f : M →ₗ[R] A}
    (hf : IsSymmetricAlgebra f) {I : Type*} (b : Module.Basis I R M) :
    ∃ c : Module.Basis I A (KaehlerDifferential R A),
      ∀ i, c i = KaehlerDifferential.D R A (f (b i)) := by
  refine ⟨Module.Basis.ofRepr (LinearEquiv.ofLinearMap (KaehlerDifferential.toCoords hf b)
    (KaehlerDifferential.ofCoords (f := f) b) (KaehlerDifferential.toCoords_ofCoords hf b)
    (KaehlerDifferential.ofCoords_toCoords hf b)), fun i => ?_⟩
  simp [KaehlerDifferential.ofCoords, Finsupp.linearCombination_single]



end
