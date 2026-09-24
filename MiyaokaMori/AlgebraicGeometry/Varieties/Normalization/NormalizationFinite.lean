import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismFiniteType
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.CurveFieldNormalizationFinite
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Perfect

/-! # Finiteness of the normalization in a finite extension of the function field

For an integral `k`-scheme of finite type (`char k = 0`), the normalization morphism in a finite
extension `K` of its function field is finite.

Proof sketch:
1. The morphism `fromNormalization (Spec.map (algebraMap K(Y) K) ≫ Y.fromSpecStalk (genericPoint Y))`
   is by definition `AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Y K`.
2. Finiteness is affine-local on `Y` (`IsFinite`: affine morphism whose section maps over affine
   opens are finite). `curveFieldNormalizationSectionsFieldIso` /
   `curveFieldNormalizationMap_app_sectionsFieldIso` identify the section map over a nonempty affine
   open `U` with `Γ(Y,U) → integralClosure Γ(Y,U) K`; over the empty open the section ring is
   trivial. So it suffices that the integral closure of `Γ(Y,U)` in `K` is a finite `Γ(Y,U)`-module
   for every nonempty affine open `U` (`normalizationFinite_isFinite_of_forall_module_finite` below).
3. `Γ(Y,U)` is a finitely generated `k`-algebra (`Scheme.Hom.finiteType_appLE`, `ΓSpecIso`) and a
   domain (`Y` integral), `K(Y) = Frac Γ(Y,U)` (`functionField_isFractionRing_of_isAffineOpen`), and
   `K / K(Y)` is finite.
4. The algebraic statement `Ring.module_finite_integralClosure_of_finiteType_of_finite_extension`
   below: for a finitely generated domain `A` over a field of characteristic zero and a finite
   extension `L` of `Frac A`, the integral closure of `A` in `L` is a finite `A`-module.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 00OW and 032L, finite extension version**: let `k` be a field of characteristic zero,
`A` a finitely generated `k`-algebra which is a domain, `K = Frac A` and `L / K` a finite
extension. Then the integral closure of `A` in `L` is a finite `A`-module.

This generalizes `Ring.module_finite_integralClosure_of_finiteType` (the case `L = K`). Proof:
1. Noether normalization (`exists_finite_inj_algHom_of_fg`) gives an injection
   `g : P := k[x_1,…,x_s] →ₐ[k] A` with `A` a finite `P`-module.
2. View `K`, `L` as `P`-algebras through `A`. `A/P` integral makes `K` a localization of
   `A ⊗ Frac P`, so `Module.Finite.of_isLocalization` gives `FiniteDimensional (Frac P) K`; with
   `[Module.Finite K L]` this gives `FiniteDimensional (Frac P) L` (`Frac P → L` is
   `Frac P → K → L`, and the towers `P → Frac P → L` and `P → A → L` are compatible).
3. `k` of characteristic zero makes `Frac P` perfect, so `L / Frac P` is separable; `P` is a UFD,
   hence integrally closed and Noetherian; `IsIntegralClosure.finite P (Frac P) L _` gives
   `Module.Finite P (integralClosure P L)`.
4. `integralClosure P L = integralClosure A L` (`A/P` integral), so the latter is a finite
   `P`-module and hence a finite `A`-module. -/
theorem Ring.module_finite_integralClosure_of_finiteType_of_finite_extension
    (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] :
    Module.Finite A ↥(integralClosure A L) := by
  obtain ⟨s, g, hinj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hgfin' : (g.toRingHom).Finite := hgfin
  have hinj' : Function.Injective (g.toRingHom) := hinj
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj'
  let : Algebra (MvPolynomial (Fin s) k) K :=
    ((algebraMap A K).comp (algebraMap (MvPolynomial (Fin s) k) A)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin s) k) A K := .of_algebraMap_eq fun _ => rfl
  let : Algebra (MvPolynomial (Fin s) k) L :=
    ((algebraMap A L).comp (algebraMap (MvPolynomial (Fin s) k) A)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin s) k) A L := .of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul (MvPolynomial (Fin s) k) K := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq _ A K]
    exact (FaithfulSMul.algebraMap_injective A K).comp hinj'
  let := FractionRing.liftAlgebra (MvPolynomial (Fin s) k) K
  have := FractionRing.isScalarTower_liftAlgebra (MvPolynomial (Fin s) k) K
  have : Module.Finite (FractionRing (MvPolynomial (Fin s) k)) K :=
    Module.Finite.of_isLocalization (MvPolynomial (Fin s) k) A (nonZeroDivisors (MvPolynomial (Fin s) k))
  let : Algebra (FractionRing (MvPolynomial (Fin s) k)) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing (MvPolynomial (Fin s) k)) K)).toAlgebra
  have : IsScalarTower (FractionRing (MvPolynomial (Fin s) k)) K L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L := by
    refine .of_algebraMap_eq fun x => ?_
    change algebraMap A L (algebraMap (MvPolynomial (Fin s) k) A x) =
      algebraMap K L (algebraMap (FractionRing (MvPolynomial (Fin s) k)) K
        (algebraMap (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) x))
    rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k)
        (FractionRing (MvPolynomial (Fin s) k)) K,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k) A K,
      ← IsScalarTower.algebraMap_apply A K L]
  have : Module.Finite (FractionRing (MvPolynomial (Fin s) k)) L := Module.Finite.trans K L
  have hPC : Module.Finite (MvPolynomial (Fin s) k)
      ↥(integralClosure (MvPolynomial (Fin s) k) L) :=
    IsIntegralClosure.finite (MvPolynomial (Fin s) k)
      (FractionRing (MvPolynomial (Fin s) k)) L _
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

/-- On a nonempty affine open `U`, if the integral closure of `Γ(Y,U)` in `L` is a finite
`Γ(Y,U)`-module, then the section map of the normalization projection over `U` is a finite ring
map (`curveFieldNormalizationMap_finite_app` with module-finiteness of the integral closure in
place of "`Γ(Y,U)` integrally closed and `L` separable"). -/
private theorem normalizationFinite_finite_app_of_module_finite
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (U : X.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U]
    (hfin : letI := AlgebraicGeometry.Scheme.Covers.curveExtensionSectionAlgebra X L U
      Module.Finite Γ(X, U) ↥(integralClosure Γ(X, U) L)) :
    ((AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X L).app U).hom.Finite := by
  let _ := AlgebraicGeometry.Scheme.Covers.curveExtensionSectionAlgebra X L U
  let e := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationSectionsFieldIso X L U hU
  have he : (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X L).app U =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) ≫ e.inv := by
    rw [← AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap_app_sectionsFieldIso X L U hU]
    simp only [Category.assoc, e, Iso.hom_inv_id, Category.comp_id]
  rw [he, CommRingCat.hom_comp]
  exact e.commRingCatIsoToRingEquiv.symm.finite.comp
    (RingHom.finite_algebraMap.mpr hfin)

/-- If on every nonempty affine open `U` the integral closure of `Γ(X,U)` in `L` is a finite
`Γ(X,U)`-module, then the normalization projection `curveFieldNormalizationMap X L` is a finite
morphism (on the empty open the section ring is trivial). -/
private theorem normalizationFinite_isFinite_of_forall_module_finite
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (hfin : ∀ (U : X.affineOpens) [Nonempty U.1],
      let := AlgebraicGeometry.Scheme.Covers.curveExtensionSectionAlgebra X L U.1
      Module.Finite Γ(X, U.1) ↥(integralClosure Γ(X, U.1) L)) :
    AlgebraicGeometry.IsFinite (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X L) := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · exact normalizationFinite_finite_app_of_module_finite X L U hU (hfin ⟨U, hU⟩)
  · have hUbot : U = ⊥ := (Opens.not_nonempty_iff_eq_bot U).mp
      fun h ↦ hne (Opens.nonempty_coeSort.mpr h)
    subst U
    have : Subsingleton Γ(AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X L,
        AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X L ⁻¹ᵁ (⊥ : X.Opens)) :=
      inferInstanceAs (Subsingleton Γ(AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X L,
        (⊥ : (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X L).Opens)))
    apply RingHom.Finite.of_surjective
    intro a
    exact ⟨0, Subsingleton.elim _ _⟩

/-- The normalization of an integral `k`-scheme of finite type (`char k = 0`) in a finite extension
of its function field is a finite morphism. -/
theorem finite_normalization_of_curve {k : Type u} [Field k] [CharZero k]
    {Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral Y]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (K : Type u) [Field K] [Algebra Y.functionField K] [Module.Finite Y.functionField K] :
    AlgebraicGeometry.IsFinite (AlgebraicGeometry.Scheme.Hom.fromNormalization
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Y.functionField K)) ≫
        Y.fromSpecStalk (genericPoint Y))) := by
  change AlgebraicGeometry.IsFinite (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Y K)
  apply normalizationFinite_isFinite_of_forall_module_finite
  intro U _
  let φ : k →+* Γ(Y, U.1) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ U.1 le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : ((Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ U.1 le_top).hom.FiniteType :=
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).finiteType_appLE
        (AlgebraicGeometry.isAffineOpen_top _) U.2 _
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let _ : Algebra k Γ(Y, U.1) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(Y, U.1) := hφ
  have : IsFractionRing Γ(Y, U.1) Y.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen Y U.1 U.2
  let := AlgebraicGeometry.Scheme.Covers.curveExtensionSectionAlgebra Y K U.1
  have : IsScalarTower Γ(Y, U.1) Y.functionField K := IsScalarTower.of_algebraMap_eq' rfl
  exact Ring.module_finite_integralClosure_of_finiteType_of_finite_extension k Γ(Y, U.1)
    Y.functionField K

end
