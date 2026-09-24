import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenterAffineLeaf

/-! # Sections of the Rees algebra sheaf on an affine open, with a ring model

Sections of the Rees algebra sheaf `I.reesAlgebra = ⊕ₙ Iⁿ` on an affine
open `U` form the Rees algebra `⊕ₙ Jⁿ Xⁿ ⊆ A[X]` of `J`, where `A` is any ring identified with
`Γ(X, U)` by a ring isomorphism `ψ` and `J` corresponds to `I(U)` under `ψ`. The identification is a
graded ring isomorphism, `(sₙ)ₙ ↦ ∑ₙ ψ(sₙ) Xⁿ`, and it turns the structure map
`Γ(X, U) → ⊕ₙ Γ(U, Iⁿ)` into `algebraMap A (reesAlgebra J) ∘ ψ`.

Source: Stacks 01OG (definition of the blowup: on `Spec A` the sheaf `⊕ Iⁿ` is the Rees algebra
`⊕ Jⁿ`), used in Stacks 0804 / 0AGQ. The extra ring isomorphism `ψ` lets the result be applied
directly with `ψ = ΓSpecIso A : Γ(Spec A, ⊤) ≃+* A` (`blowup_spec_iso_proj_reesGrading_over`) without a
separate transport of Rees algebras along `A ≅ Γ(Spec A, ⊤)`; with `ψ = RingEquiv.refl` it is
`exists_reesAlgebra_sectionsRing_equiv`.

Ingredients: `IdealSheafData.map_ideal` (Mathlib: `I(V) = I(U)·O(V)` for affine
`V ≤ U`), `coe_reesAlgebra_sectionsGMul` and `monoidalUnitIso_hom_app`
(the graded multiplication and unit of `I.reesAlgebra` on sections are the multiplication and unit of
`Γ(X, U)`), `DirectSum.toSemiring`, `MiyaokaMori.RingTheory.ReesAlgebra.grading` (`Ideal.reesGrading`).

Implementation note: the underlying section of `a ∈ Γ(U, Iⁿ)` is wrapped in the `def` `secVal`
(a function into `Γ(X, U)`); the raw `a.1` lives in `(SheafOfModules.unit _).val.obj (op U)`, which is
only definitionally (not reducibly) `Γ(X, U)`, and `rw` refuses to work on goals mixing the two spellings.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace Polynomial
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)

/-- On an affine open `U`, a section `s ∈ Γ(X, U)` lies in `Γ(U, Iᵐ)` (i.e. `s|_V ∈ I(V)^m` for
every affine `V ≤ U`) iff `s ∈ I(U)^m`: take `V = U` for one direction; for the other,
`I(V) = I(U)·O(V)` (`map_ideal`) and `Ideal.map_pow`. -/
theorem mem_powSubmodule_affine_iff (U : X.affineOpens) (m : ℕ) (s : Γ(X, (U : X.Opens))) :
    s ∈ (I.powSubmodule m).obj (op (U : X.Opens)) ↔ s ∈ (I.ideal U) ^ m := by
  constructor
  · intro h
    have h' := h U le_rfl
    have hid : (X.presheaf.map (homOfLE (le_refl (U : X.Opens))).op).hom s = s := by
      have e : (homOfLE (le_refl (U : X.Opens))).op = 𝟙 (op (U : X.Opens)) := rfl
      rw [e, X.presheaf.map_id]
      rfl
    rwa [hid] at h'
  · intro h V hV
    have h2 : ((I.ideal U) ^ m).map (X.presheaf.map (homOfLE hV).op).hom = (I.ideal V) ^ m := by
      rw [Ideal.map_pow]
      exact congrArg (· ^ m) (I.map_ideal hV)
    have h1 := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE hV).op).hom h
    rw [h2] at h1
    exact h1

/-! ### The underlying section of an element of `Γ(U, Iᵐ)` -/

/-- The underlying section in `Γ(X, U)` of `a ∈ Γ(U, Iᵐ)` (`a.1`, retyped). -/
def secVal (U : X.Opens) (m : ℕ) (a : I.reesAlgebra.sectionsPiece U m) : Γ(X, U) := a.1

theorem secVal_injective (U : X.Opens) (m : ℕ) : Function.Injective (I.secVal U m) :=
  fun _ _ h => Subtype.ext h

theorem secVal_zero (U : X.Opens) (m : ℕ) : I.secVal U m 0 = 0 := rfl

theorem secVal_add (U : X.Opens) (m : ℕ) (a b : I.reesAlgebra.sectionsPiece U m) :
    I.secVal U m (a + b) = I.secVal U m a + I.secVal U m b := rfl

theorem secVal_mem (U : X.Opens) (m : ℕ) (a : I.reesAlgebra.sectionsPiece U m) :
    I.secVal U m a ∈ (I.powSubmodule m).obj (op U) := a.2

/-- `secVal` as an additive homomorphism. -/
def secValAddHom (U : X.Opens) (m : ℕ) : I.reesAlgebra.sectionsPiece U m →+ Γ(X, U) where
  toFun := I.secVal U m
  map_zero' := I.secVal_zero U m
  map_add' := I.secVal_add U m

/-- The unit `S.one = powOne` of the Rees algebra is the identity on sections
(`monoidalUnitIso_hom_app`). -/
theorem secVal_one_app (U : X.Opens) (r : Γ(X, U)) :
    I.secVal U 0 (I.reesAlgebra.one.app U r) = r :=
  monoidalUnitIso_hom_app U r

/-- The graded multiplication of the Rees algebra is the ring multiplication
(`coe_reesAlgebra_sectionsGMul`). -/
theorem secVal_sectionsGMul (U : X.Opens) {m n : ℕ} (a : I.reesAlgebra.sectionsPiece U m)
    (b : I.reesAlgebra.sectionsPiece U n) :
    I.secVal U (m + n) (I.reesAlgebra.sectionsGMul U a b) = I.secVal U m a * I.secVal U n b :=
  I.coe_reesAlgebra_sectionsGMul U m n a b

/-- The `m`-th component of an element of the sections ring, as an additive homomorphism. -/
def componentAddHom (U : X.Opens) (m : ℕ) :
    I.reesAlgebra.sectionsRing U →+ I.reesAlgebra.sectionsPiece U m where
  toFun := I.reesAlgebra.component U m
  map_zero' := DirectSum.zero_apply (β := I.reesAlgebra.sectionsPiece U) m
  map_add' x y := DirectSum.add_apply (β := I.reesAlgebra.sectionsPiece U) x y m

section RingEquiv

variable (U : X.affineOpens) {A : Type u} [CommRing A] (ψ : Γ(X, (U : X.Opens)) ≃+* A)
  (J : Ideal A)

/-- `x ∈ I(U)^m ↔ ψ x ∈ J^m` when `I(U)` corresponds to `J` under `ψ`. -/
theorem mem_pow_iff_of_equiv (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) (m : ℕ)
    (x : Γ(X, (U : X.Opens))) :
    x ∈ (I.ideal U) ^ m ↔ ψ x ∈ J ^ m := by
  have hI : I.ideal U = J.map ψ.symm := by
    rw [Ideal.map_symm]
    ext y
    exact hJ y
  rw [hI, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [ψ.apply_symm_apply]
  · intro h
    exact ⟨ψ x, h, ψ.symm_apply_apply x⟩

/-- The element of `Γ(U, Iᵐ)` with underlying section `ψ.symm c`, for `c ∈ J^m`. -/
def reesPieceOfCoeff (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) (m : ℕ) (c : A) (hc : c ∈ J ^ m) :
    I.reesAlgebra.sectionsPiece U m :=
  ⟨ψ.symm c, (I.mem_powSubmodule_affine_iff U m (ψ.symm c)).mpr
    ((I.mem_pow_iff_of_equiv U ψ J hJ m (ψ.symm c)).mpr (by rwa [ψ.apply_symm_apply]))⟩

theorem secVal_reesPieceOfCoeff (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) (m : ℕ) (c : A)
    (hc : c ∈ J ^ m) :
    I.secVal U m (I.reesPieceOfCoeff U ψ J hJ m c hc) = ψ.symm c := rfl

/-- Degree `m` piece: `s ↦ ψ(s) Xᵐ ∈ reesAlgebra J`. -/
def reesPieceToReesAlgebra (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) (m : ℕ) :
    I.reesAlgebra.sectionsPiece U m →+ _root_.reesAlgebra J where
  toFun a := ⟨monomial m (ψ (I.secVal U m a)),
    reesAlgebra.monomial_mem.mpr ((I.mem_pow_iff_of_equiv U ψ J hJ m _).mp
      ((I.mem_powSubmodule_affine_iff U m _).mp (I.secVal_mem U m a)))⟩
  map_zero' := Subtype.ext (by
    show (monomial m (ψ (I.secVal U m 0)) : A[X]) = 0
    rw [I.secVal_zero, map_zero, monomial_zero_right])
  map_add' a b := Subtype.ext (by
    show (monomial m (ψ (I.secVal U m (a + b))) : A[X]) =
      monomial m (ψ (I.secVal U m a)) + monomial m (ψ (I.secVal U m b))
    rw [I.secVal_add, map_add, map_add])

theorem coe_reesPieceToReesAlgebra (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) (m : ℕ)
    (a : I.reesAlgebra.sectionsPiece U m) :
    ((I.reesPieceToReesAlgebra U ψ J hJ m a : _root_.reesAlgebra J) : A[X]) =
      monomial m (ψ (I.secVal U m a)) := rfl

theorem reesPieceToReesAlgebra_one (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) :
    I.reesPieceToReesAlgebra U ψ J hJ _
      (GradedMonoid.GOne.one : I.reesAlgebra.sectionsPiece U 0) = 1 := by
  apply Subtype.ext
  rw [I.coe_reesPieceToReesAlgebra]
  change (monomial 0 (ψ (I.secVal U 0 (I.reesAlgebra.one.app (U : X.Opens)
    (1 : Γ(X, (U : X.Opens)))))) : A[X]) = 1
  rw [I.secVal_one_app, map_one, monomial_zero_one]

theorem reesPieceToReesAlgebra_mul (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) {i j : ℕ}
    (a : I.reesAlgebra.sectionsPiece U i) (b : I.reesAlgebra.sectionsPiece U j) :
    I.reesPieceToReesAlgebra U ψ J hJ _ (GradedMonoid.GMul.mul a b) =
      I.reesPieceToReesAlgebra U ψ J hJ _ a * I.reesPieceToReesAlgebra U ψ J hJ _ b := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, I.coe_reesPieceToReesAlgebra, I.coe_reesPieceToReesAlgebra,
    I.coe_reesPieceToReesAlgebra]
  change (monomial (i + j) (ψ (I.secVal U (i + j) (I.reesAlgebra.sectionsGMul U a b))) : A[X]) = _
  rw [I.secVal_sectionsGMul, map_mul, monomial_mul_monomial]

/-- The ring homomorphism `⊕ₙ Γ(U, Iⁿ) → reesAlgebra J`, `(sₙ)ₙ ↦ ∑ₙ ψ(sₙ) Xⁿ`. -/
def reesSectionsToReesAlgebra (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) :
    I.reesAlgebra.sectionsRing U →+* _root_.reesAlgebra J :=
  DirectSum.toSemiring (fun m => I.reesPieceToReesAlgebra U ψ J hJ m)
    (I.reesPieceToReesAlgebra_one U ψ J hJ) (fun a b => I.reesPieceToReesAlgebra_mul U ψ J hJ a b)

theorem reesSectionsToReesAlgebra_ofPiece (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) (m : ℕ)
    (a : I.reesAlgebra.sectionsPiece U m) :
    I.reesSectionsToReesAlgebra U ψ J hJ (I.reesAlgebra.ofPiece U m a) =
      I.reesPieceToReesAlgebra U ψ J hJ m a :=
  DirectSum.toSemiring_of _ _ _ m a

/-- The `m`-th coefficient of the image is `ψ` of the `m`-th component. -/
theorem coeff_reesSectionsToReesAlgebra (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J)
    (x : I.reesAlgebra.sectionsRing U) (m : ℕ) :
    ((I.reesSectionsToReesAlgebra U ψ J hJ x : _root_.reesAlgebra J) : A[X]).coeff m =
      ψ (I.secVal U m (I.reesAlgebra.component U m x)) := by
  have key : ((Polynomial.lcoeff A m).toAddMonoidHom.comp
      ((AddSubmonoidClass.subtype (_root_.reesAlgebra J)).comp
        (I.reesSectionsToReesAlgebra U ψ J hJ).toAddMonoidHom)) =
      ψ.toAddMonoidHom.comp ((I.secValAddHom U m).comp (I.componentAddHom U m)) := by
    refine DirectSum.addHom_ext fun i a => ?_
    change ((I.reesSectionsToReesAlgebra U ψ J hJ (I.reesAlgebra.ofPiece U i a) :
        _root_.reesAlgebra J) : A[X]).coeff m =
      ψ (I.secVal U m (I.reesAlgebra.component U m (I.reesAlgebra.ofPiece U i a)))
    rw [I.reesSectionsToReesAlgebra_ofPiece, I.coe_reesPieceToReesAlgebra, coeff_monomial]
    by_cases h : i = m
    · subst h
      rw [if_pos rfl, I.reesAlgebra.component_ofPiece]
    · rw [if_neg h]
      have h0 : I.reesAlgebra.component U m (I.reesAlgebra.ofPiece U i a) = 0 :=
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)
      rw [h0, I.secVal_zero, map_zero]
  exact DFunLike.congr_fun key x

theorem reesSectionsToReesAlgebra_injective (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) :
    Function.Injective (I.reesSectionsToReesAlgebra U ψ J hJ) := by
  intro x y hxy
  refine DFinsupp.ext fun m => ?_
  apply I.secVal_injective U m
  apply ψ.injective
  have h : ((I.reesSectionsToReesAlgebra U ψ J hJ x : _root_.reesAlgebra J) : A[X]).coeff m =
      ((I.reesSectionsToReesAlgebra U ψ J hJ y : _root_.reesAlgebra J) : A[X]).coeff m := by
    rw [hxy]
  rw [I.coeff_reesSectionsToReesAlgebra, I.coeff_reesSectionsToReesAlgebra] at h
  exact h

theorem reesSectionsToReesAlgebra_surjective (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) :
    Function.Surjective (I.reesSectionsToReesAlgebra U ψ J hJ) := by
  intro p
  refine ⟨∑ m ∈ (p : A[X]).support, I.reesAlgebra.ofPiece U m
    (I.reesPieceOfCoeff U ψ J hJ m ((p : A[X]).coeff m) (p.2 m)), ?_⟩
  apply Subtype.ext
  rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) (as_sum_support (p : A[X])).symm
  rw [I.reesSectionsToReesAlgebra_ofPiece, I.coe_reesPieceToReesAlgebra,
    I.secVal_reesPieceOfCoeff, ψ.apply_symm_apply]

/-- The ring isomorphism `⊕ₙ Γ(U, Iⁿ) ≃+* reesAlgebra J`. -/
def reesSectionsRingEquiv (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) :
    I.reesAlgebra.sectionsRing U ≃+* _root_.reesAlgebra J :=
  RingEquiv.ofBijective (I.reesSectionsToReesAlgebra U ψ J hJ)
    ⟨I.reesSectionsToReesAlgebra_injective U ψ J hJ,
      I.reesSectionsToReesAlgebra_surjective U ψ J hJ⟩

theorem reesSectionsRingEquiv_apply (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J)
    (x : I.reesAlgebra.sectionsRing U) :
    I.reesSectionsRingEquiv U ψ J hJ x = I.reesSectionsToReesAlgebra U ψ J hJ x := rfl

/-- The isomorphism is graded: `x` lies in the `m`-th piece iff its image is a monomial of
degree `m`. -/
theorem mem_sectionsGrading_iff_reesSectionsRingEquiv (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J)
    (m : ℕ) (x : I.reesAlgebra.sectionsRing U) :
    x ∈ I.reesAlgebra.sectionsGrading (U : X.Opens) m ↔
      I.reesSectionsRingEquiv U ψ J hJ x ∈ Ideal.reesGrading J m := by
  rw [I.reesSectionsRingEquiv_apply]
  constructor
  · rintro ⟨a, rfl⟩
    rw [show DirectSum.of (I.reesAlgebra.sectionsPiece (U : X.Opens)) m a =
      I.reesAlgebra.ofPiece U m a from rfl, I.reesSectionsToReesAlgebra_ofPiece]
    exact (MiyaokaMori.RingTheory.ReesAlgebra.mem_grading_iff J m _).mpr
      ⟨_, (I.coe_reesPieceToReesAlgebra U ψ J hJ m a).symm⟩
  · intro h
    refine ⟨I.reesAlgebra.component U m x, ?_⟩
    refine DFinsupp.ext fun i => ?_
    by_cases hi : m = i
    · subst hi
      exact DirectSum.of_eq_same m _
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi)]
      have h0 := MiyaokaMori.RingTheory.ReesAlgebra.coeff_eq_zero_of_mem J h hi
      rw [I.coeff_reesSectionsToReesAlgebra] at h0
      exact (I.secVal_injective U i
        ((ψ.map_eq_zero_iff.mp h0).trans (I.secVal_zero U i).symm)).symm

/-- Compatibility with the structure maps: `sectionsUnitHom U r ↦ algebraMap A _ (ψ r)`. -/
theorem reesSectionsRingEquiv_sectionsUnitHom (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J)
    (r : Γ(X, (U : X.Opens))) :
    I.reesSectionsRingEquiv U ψ J hJ (I.reesAlgebra.sectionsUnitHom (U : X.Opens) r) =
      algebraMap A (_root_.reesAlgebra J) (ψ r) := by
  have h2 : I.reesSectionsToReesAlgebra U ψ J hJ (I.reesAlgebra.sectionsUnitHom (U : X.Opens) r) =
      I.reesPieceToReesAlgebra U ψ J hJ 0 (I.reesAlgebra.one.app (U : X.Opens) r) :=
    I.reesSectionsToReesAlgebra_ofPiece U ψ J hJ 0 (I.reesAlgebra.one.app (U : X.Opens) r)
  refine h2.trans (Subtype.ext ?_)
  refine (I.coe_reesPieceToReesAlgebra U ψ J hJ 0 _).trans ?_
  refine (congrArg (fun t => (monomial 0 (ψ t) : A[X])) (I.secVal_one_app (U : X.Opens) r)).trans ?_
  exact (monomial_zero_left (a := ψ r)).trans (C_eq_algebraMap (ψ r))

end RingEquiv

/-- **Sections of the Rees algebra sheaf on an affine open are the Rees algebra** (Stacks 01OG),
existential form with an arbitrary ring model `ψ : Γ(X, U) ≃+* A` of the sections and an ideal `J`
of `A` corresponding to `I(U)`: graded ring isomorphism compatible with the structure maps. With
`ψ = RingEquiv.refl _`, `J = I.ideal U` this is `exists_reesAlgebra_sectionsRing_equiv`. -/
theorem exists_reesAlgebra_sectionsRing_equiv_of_ringEquiv (U : X.affineOpens) {A : Type u}
    [CommRing A] (ψ : Γ(X, (U : X.Opens)) ≃+* A) (J : Ideal A)
    (hJ : ∀ x, x ∈ I.ideal U ↔ ψ x ∈ J) :
    ∃ e : I.reesAlgebra.sectionsRing (U : X.Opens) ≃+* _root_.reesAlgebra J,
      (∀ (m : ℕ) (x : I.reesAlgebra.sectionsRing (U : X.Opens)),
        x ∈ I.reesAlgebra.sectionsGrading (U : X.Opens) m ↔ e x ∈ Ideal.reesGrading J m) ∧
      ∀ r : Γ(X, (U : X.Opens)),
        e (I.reesAlgebra.sectionsUnitHom (U : X.Opens) r) =
          algebraMap A (_root_.reesAlgebra J) (ψ r) :=
  ⟨I.reesSectionsRingEquiv U ψ J hJ, I.mem_sectionsGrading_iff_reesSectionsRingEquiv U ψ J hJ,
    I.reesSectionsRingEquiv_sectionsUnitHom U ψ J hJ⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end
