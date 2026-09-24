import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberPolynomialExtensionDegreeAffineLinePolynomial

/-! # Coordinate changes on `A¹_k` preserve the degree

Algebraic glue for the polynomiality of the fiber sections of `Tot(L)` (the homogenization in the
fiber coordinate in the proof of the polynomial realization theorem of the paper).

* `Polynomial.degree_ringEquiv_apply`: a ring automorphism `σ` of `k[X]` (`k` a field) preserves the
  degree. Proof: constants go to constants (units of `k[X]` are the nonzero constants,
  `Polynomial.isUnit_iff`), so `σ (C c) = C (φ c)` for a ring endomorphism `φ` of `k`, and
  `σ f = (f.map φ).comp (σ X)` (`Polynomial.ringHom_ext`); hence
  `natDegree (σ f) = natDegree f · natDegree (σ X)` (`Polynomial.natDegree_comp`,
  `Polynomial.natDegree_map_eq_of_injective`). Applying this to `σ⁻¹` and to `X = σ (σ⁻¹ X)` gives
  `natDegree (σ X) · natDegree (σ⁻¹ X) = 1`, so `natDegree (σ X) = 1`.
  No `k`-linearity of `σ` is needed.
* `affineLinePolynomialRingHom k : k[X] →+* Γ(A¹_k, ⊤)` is `affineLinePolynomial k` as a ring
  homomorphism (`rfl`), and it is bijective (`MvPolynomial.uniqueAlgEquiv` and the two isomorphisms
  `AffineSpace.SpecIso`, `ΓSpecIso` it is built from).
* `fiberCoordinate α : k[X] →+* Γ(F, ⊤)` for an isomorphism `α : F ≅ A¹_k` is
  `f ↦ α.hom.appTop (affineLinePolynomial k f)`; it is bijective, and for two isomorphisms `α₀`, `α`
  the ring automorphism `fiberCoordinateChange α₀ α := (fiberCoordinate α)⁻¹ ∘ fiberCoordinate α₀`
  of `k[X]` satisfies `fiberCoordinate α (fiberCoordinateChange α₀ α f) = fiberCoordinate α₀ f`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Polynomial

variable {k : Type*} [Field k]

/-- A ring automorphism of `k[X]` sends constants to constants (units are the nonzero constants). -/
theorem ringEquiv_C_eq_C_coeff_zero (σ : k[X] ≃+* k[X]) (c : k) :
    σ (C c) = C ((σ (C c)).coeff 0) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hu : IsUnit (σ (C c)) := (isUnit_C.mpr hc.isUnit).map σ
    obtain ⟨r, -, hr⟩ := isUnit_iff.mp hu
    rw [← hr, coeff_C_zero]

/-- The ring endomorphism of `k` induced by a ring automorphism of `k[X]` on the constants. -/
def ringEquivConst (σ : k[X] ≃+* k[X]) : k →+* k where
  toFun c := (σ (C c)).coeff 0
  map_one' := by simp
  map_mul' a b := by
    show (σ (C (a * b))).coeff 0 = (σ (C a)).coeff 0 * (σ (C b)).coeff 0
    rw [C_mul, map_mul, mul_coeff_zero]
  map_zero' := by simp
  map_add' a b := by
    show (σ (C (a + b))).coeff 0 = (σ (C a)).coeff 0 + (σ (C b)).coeff 0
    rw [C_add, map_add, coeff_add]

theorem ringEquiv_C (σ : k[X] ≃+* k[X]) (c : k) : σ (C c) = C (ringEquivConst σ c) :=
  ringEquiv_C_eq_C_coeff_zero σ c

/-- A ring automorphism of `k[X]` is "twist the coefficients by `ringEquivConst σ`, then substitute
`σ X`". -/
theorem ringEquiv_apply_eq_map_comp (σ : k[X] ≃+* k[X]) (f : k[X]) :
    σ f = (f.map (ringEquivConst σ)).comp (σ X) := by
  have h : (σ : k[X] →+* k[X]) = (compRingHom (σ X)).comp (mapRingHom (ringEquivConst σ)) := by
    apply ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, coe_mapRingHom, map_C, coe_compRingHom, C_comp]
      exact ringEquiv_C σ a
    · simp only [RingHom.comp_apply, coe_mapRingHom, map_X, coe_compRingHom, X_comp]
      rfl
  exact congrArg (fun g : k[X] →+* k[X] => g f) h

theorem natDegree_ringEquiv_apply_eq_mul (σ : k[X] ≃+* k[X]) (f : k[X]) :
    (σ f).natDegree = f.natDegree * (σ X).natDegree := by
  rw [ringEquiv_apply_eq_map_comp σ f, natDegree_comp,
    natDegree_map_eq_of_injective (ringEquivConst σ).injective]

/-- The image of `X` under a ring automorphism of `k[X]` has degree `1`. -/
theorem natDegree_ringEquiv_X (σ : k[X] ≃+* k[X]) : (σ X).natDegree = 1 := by
  have h : (σ (σ.symm X)).natDegree = (σ.symm X).natDegree * (σ X).natDegree :=
    natDegree_ringEquiv_apply_eq_mul σ (σ.symm X)
  rw [RingEquiv.apply_symm_apply, natDegree_X, natDegree_ringEquiv_apply_eq_mul σ.symm X,
    natDegree_X, one_mul] at h
  exact Nat.eq_one_of_mul_eq_one_left h.symm

theorem natDegree_ringEquiv_apply (σ : k[X] ≃+* k[X]) (f : k[X]) :
    (σ f).natDegree = f.natDegree := by
  rw [natDegree_ringEquiv_apply_eq_mul, natDegree_ringEquiv_X, mul_one]

/-- **A ring automorphism of `k[X]` preserves the degree.** -/
theorem degree_ringEquiv_apply (σ : k[X] ≃+* k[X]) (f : k[X]) : (σ f).degree = f.degree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hσf : σ f ≠ 0 := fun h => hf (σ.injective (h.trans (map_zero σ).symm))
    rw [degree_eq_natDegree hσf, degree_eq_natDegree hf, natDegree_ringEquiv_apply]

end Polynomial

/-- `affineLinePolynomial k` as a ring homomorphism `k[X] →+* Γ(A¹_k, ⊤)`. -/
def affineLinePolynomialRingHom (k : Type u) [Field k] :
    Polynomial k →+*
      Γ(AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)), ⊤) :=
  ((AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.appTop.hom.comp
    ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv.hom.comp
      (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k)).toRingHom))

theorem affineLinePolynomialRingHom_apply (k : Type u) [Field k] (f : Polynomial k) :
    affineLinePolynomialRingHom k f = affineLinePolynomial k f := rfl

/-- `k[X] → k[X_{ULift (Fin 1)}]`, `X ↦ X ⟨0⟩`, is bijective (`MvPolynomial.uniqueAlgEquiv`). -/
theorem aeval_X_ulift_fin_one_bijective (k : Type u) [Field k] :
    Function.Bijective
      (Polynomial.aeval (R := k) (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k)) := by
  have h : (Polynomial.aeval (R := k) (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k)) =
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).symm.toAlgHom := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    change _ = (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).symm Polynomial.X
    rw [eq_comm, AlgEquiv.symm_apply_eq]
    simp [MvPolynomial.X]
  rw [h]
  exact (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).symm.bijective

theorem affineLinePolynomialRingHom_bijective (k : Type u) [Field k] :
    Function.Bijective (affineLinePolynomialRingHom k) := by
  have h1 : Function.Bijective
      ((AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.app ⊤).hom :=
    ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Bijective (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv.hom :=
    ConcreteCategory.bijective_of_isIso _
  exact h1.comp (h2.comp (aeval_X_ulift_fin_one_bijective k))

/-- The coordinate ring homomorphism `k[X] →+* Γ(F, ⊤)` attached to an isomorphism `α : F ≅ A¹_k`:
`f ↦ α.hom.appTop (affineLinePolynomial k f)`. -/
def fiberCoordinate {k : Type u} [Field k] {F : AlgebraicGeometry.Scheme.{u}}
    (α : F ≅ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))) :
    Polynomial k →+* Γ(F, ⊤) :=
  α.hom.appTop.hom.comp (affineLinePolynomialRingHom k)

theorem fiberCoordinate_apply {k : Type u} [Field k] {F : AlgebraicGeometry.Scheme.{u}}
    (α : F ≅ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (f : Polynomial k) :
    fiberCoordinate α f = α.hom.appTop.hom (affineLinePolynomial k f) := rfl

theorem fiberCoordinate_bijective {k : Type u} [Field k] {F : AlgebraicGeometry.Scheme.{u}}
    (α : F ≅ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))) :
    Function.Bijective (fiberCoordinate α) := by
  have h1 : Function.Bijective (α.hom.app ⊤).hom := ConcreteCategory.bijective_of_isIso _
  exact h1.comp (affineLinePolynomialRingHom_bijective k)

/-- `fiberCoordinate α` as a ring isomorphism. -/
def fiberCoordinateEquiv {k : Type u} [Field k] {F : AlgebraicGeometry.Scheme.{u}}
    (α : F ≅ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))) :
    Polynomial k ≃+* Γ(F, ⊤) :=
  RingEquiv.ofBijective (fiberCoordinate α) (fiberCoordinate_bijective α)

/-- The ring automorphism of `k[X]` comparing two coordinates `α₀`, `α` on `F`:
`(fiberCoordinate α)⁻¹ ∘ fiberCoordinate α₀`. -/
def fiberCoordinateChange {k : Type u} [Field k] {F : AlgebraicGeometry.Scheme.{u}}
    (α₀ α : F ≅ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))) :
    Polynomial k ≃+* Polynomial k :=
  (fiberCoordinateEquiv α₀).trans (fiberCoordinateEquiv α).symm

theorem fiberCoordinate_fiberCoordinateChange {k : Type u} [Field k] {F : AlgebraicGeometry.Scheme.{u}}
    (α₀ α : F ≅ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (f : Polynomial k) :
    α.hom.appTop.hom (affineLinePolynomial k (fiberCoordinateChange α₀ α f)) =
      α₀.hom.appTop.hom (affineLinePolynomial k f) := by
  change fiberCoordinateEquiv α (fiberCoordinateChange α₀ α f) = fiberCoordinateEquiv α₀ f
  simp only [fiberCoordinateChange, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]

theorem degree_fiberCoordinateChange {k : Type u} [Field k] {F : AlgebraicGeometry.Scheme.{u}}
    (α₀ α : F ≅ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (f : Polynomial k) :
    (fiberCoordinateChange α₀ α f).degree = f.degree :=
  Polynomial.degree_ringEquiv_apply _ f

end
