import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.FreeTensorFreeIso
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # The weighted polynomial graded algebra on a scheme

The local model: the weighted polynomial graded quasi-coherent algebra of weight vector `w` on a
scheme `X`, whose `j`-th piece is the free sheaf on the monomials of weight `j` (the graded jet
algebras of the paper have local bases of this form).

The monoid laws `one_mul` / `mul_assoc` / `mul_comm` are proved by reduction to the generators: a
morphism out of a tensor product of free sheaves is determined by the generators `ιFree`
(`free_hom_ext` / `tensor_hom_ext` / `tensor_tensor_hom_ext` / `unit_tensor_hom_ext`), the
multiplication on generators is `λ ≫ ιFree (e + e′)` (`ιM_tensor_ιM_mulHom`), index equalities are
transported by `ιM_comp_eqToHom`, and the remaining coherence on `𝟙_ ⊗ 𝟙_` is handled by `triangle`,
`unitors_equal` and `braiding_leftUnitor`.

On an affine open `U` the sections ring of this algebra is `≃+* MvPolynomial σ Γ(X,U)` with the
grading corresponding to the weighted homogeneous components (`sectionsRingEquiv`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The index set `{e : σ →₀ ℕ // weight w e = j}` of monomials of weight `j`. -/

abbrev weightedMonomials {σ : Type u} (w : σ → ℕ) (j : ℕ) : Type u :=
  {e : σ →₀ ℕ // Finsupp.weight w e = j}

open scoped CategoryTheory.MonoidalCategory

/-- The `j`-th piece: the free sheaf of modules on the monomials of weight `j`. -/

noncomputable abbrev AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part (X : AlgebraicGeometry.Scheme.{u}) {σ : Type u} (w : σ → ℕ) (j : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (weightedMonomials w j)

/-- The multiplication: addition of exponents of monomials. -/

noncomputable def AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom (X : AlgebraicGeometry.Scheme.{u}) {σ : Type u} (w : σ → ℕ) (i j : ℕ) :
    AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w i ⊗ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w j ⟶ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w (i + j) :=
  (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X)
      (weightedMonomials w i) (weightedMonomials w j)).hom ≫
    SheafOfModules.freeMap (R := X.ringCatSheaf)
      (fun p : weightedMonomials w i × weightedMonomials w j =>
        (⟨p.1.1 + p.2.1, by simp [map_add, p.1.2, p.2.2]⟩ : weightedMonomials w (i + j)))

noncomputable def AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.oneHom (X : AlgebraicGeometry.Scheme.{u}) {σ : Type u} (w : σ → ℕ) : 𝟙_ X.Modules ⟶ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w 0 :=
  SheafOfModules.ιFree (R := X.ringCatSheaf) (I := weightedMonomials w 0) ⟨0, map_zero _⟩

namespace AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra

variable (X : AlgebraicGeometry.Scheme.{u}) {σ : Type u} (w : σ → ℕ)

/-- The generator `ιFree i`, packaged as a morphism `𝟙_ ⟶ free I` in `X.Modules`.
(A `def`, not an `abbrev`, so that `rw` only matches the `X.Modules` spelling; the connection to
Mathlib's lemmas always goes through `exact`.) -/
noncomputable def ιM {I : Type u} (i : I) :
    𝟙_ X.Modules ⟶ AlgebraicGeometry.Scheme.Modules.free (X := X) I :=
  SheafOfModules.ιFree (R := X.ringCatSheaf) i

/-- The unit is the generator of the zero monomial. -/
theorem oneHom_eq : oneHom X w = ιM X (⟨0, map_zero _⟩ : weightedMonomials w 0) := rfl

/-- A morphism out of a free sheaf is determined by the generators: `free I = ∐ O_X`, by
`Sigma.hom_ext`. -/
theorem free_hom_ext {I : Type u} {M : X.Modules}
    {f g : AlgebraicGeometry.Scheme.Modules.free (X := X) I ⟶ M}
    (h : ∀ i, ιM X i ≫ f = ιM X i ≫ g) : f = g :=
  CategoryTheory.Limits.Sigma.hom_ext (C := SheafOfModules.{u} X.ringCatSheaf) f g h

/-- `ιFree (i, j) ≫ freeTensorFreeIso.inv = λ⁻¹ ≫ (ιFree i ⊗ ιFree j)` (`Sigma.ι_desc`). -/
theorem ιM_freeTensorFreeIso_inv {I J : Type u} (i : I) (j : J) :
    ιM X (i, j) ≫ (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X) I J).inv =
      (λ_ (𝟙_ X.Modules)).inv ≫ (ιM X i ⊗ₘ ιM X j) := by
  rw [AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso_inv]
  exact CategoryTheory.Limits.Sigma.ι_desc (C := SheafOfModules.{u} X.ringCatSheaf)
    (f := fun _ : I × J => SheafOfModules.unit X.ringCatSheaf) _ (i, j)

/-- `(ιFree i ⊗ ιFree j) ≫ freeTensorFreeIso.hom = λ ≫ ιFree (i, j)` (the `ιM` spelling of
`ιFree_tensor_ιFree_freeTensorFreeIso`). -/
theorem ιM_tensor_ιM_freeTensorFreeIso_hom {I J : Type u} (i : I) (j : J) :
    (ιM X i ⊗ₘ ιM X j) ≫ (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X) I J).hom =
      (λ_ (𝟙_ X.Modules)).hom ≫ ιM X (i, j) :=
  AlgebraicGeometry.Scheme.Modules.ιFree_tensor_ιFree_freeTensorFreeIso (X := X) i j

/-- A morphism out of the tensor product of two free sheaves is determined by the generators
`ιFree i ⊗ ιFree j`. -/
theorem tensor_hom_ext {I J : Type u} {M : X.Modules}
    {f g : AlgebraicGeometry.Scheme.Modules.free (X := X) I ⊗ AlgebraicGeometry.Scheme.Modules.free (X := X) J ⟶ M}
    (h : ∀ i j, (ιM X i ⊗ₘ ιM X j) ≫ f = (ιM X i ⊗ₘ ιM X j) ≫ g) : f = g := by
  refine (CategoryTheory.Iso.cancel_iso_inv_left
    (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X) I J) _ _).mp ?_
  apply free_hom_ext
  rintro ⟨i, j⟩
  rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc,
    ιM_freeTensorFreeIso_inv, CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, h]

/-- A morphism out of `(free I ⊗ free J) ⊗ free K` is determined by the generators
`(ιFree i ⊗ ιFree j) ⊗ ιFree k`. -/
theorem tensor_tensor_hom_ext {I J K : Type u} {M : X.Modules}
    {f g : (AlgebraicGeometry.Scheme.Modules.free (X := X) I ⊗ AlgebraicGeometry.Scheme.Modules.free (X := X) J) ⊗
      AlgebraicGeometry.Scheme.Modules.free (X := X) K ⟶ M}
    (h : ∀ i j k, ((ιM X i ⊗ₘ ιM X j) ⊗ₘ ιM X k) ≫ f = ((ιM X i ⊗ₘ ιM X j) ⊗ₘ ιM X k) ≫ g) : f = g := by
  refine (CategoryTheory.Iso.cancel_iso_inv_left
    (CategoryTheory.MonoidalCategory.whiskerRightIso
      (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X) I J)
      (AlgebraicGeometry.Scheme.Modules.free (X := X) K)) _ _).mp ?_
  apply tensor_hom_ext
  rintro ⟨i, j⟩ k
  dsimp only [CategoryTheory.MonoidalCategory.whiskerRightIso]
  rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc,
    ← CategoryTheory.MonoidalCategory.tensorHom_id
      (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X) I J).inv
      (AlgebraicGeometry.Scheme.Modules.free (X := X) K),
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, CategoryTheory.Category.comp_id,
    ιM_freeTensorFreeIso_inv, ← CategoryTheory.Category.id_comp (ιM X k),
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
    CategoryTheory.MonoidalCategory.tensorHom_id,
    CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, h]

/-- A morphism out of `unit ⊗ free J` is determined by the generators `𝟙_ ◁ ιFree j`. -/
theorem unit_tensor_hom_ext {J : Type u} {M : X.Modules}
    {f g : 𝟙_ X.Modules ⊗ AlgebraicGeometry.Scheme.Modules.free (X := X) J ⟶ M}
    (h : ∀ j, (𝟙_ X.Modules ◁ ιM X j) ≫ f = (𝟙_ X.Modules ◁ ιM X j) ≫ g) : f = g := by
  refine (CategoryTheory.Iso.cancel_iso_inv_left
    (λ_ (AlgebraicGeometry.Scheme.Modules.free (X := X) J)) _ _).mp ?_
  apply free_hom_ext
  intro j
  rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc,
    CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality,
    CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, h]

/-- The multiplication on generators: `(ιFree e ⊗ ιFree e′) ≫ mulHom = λ ≫ ιFree (e + e′)`. -/
theorem ιM_tensor_ιM_mulHom (i j : ℕ) (e : weightedMonomials w i) (e' : weightedMonomials w j) :
    (ιM X e ⊗ₘ ιM X e') ≫ mulHom X w i j =
      (λ_ (𝟙_ X.Modules)).hom ≫ ιM X
        (⟨e.1 + e'.1, by simp [map_add, e.2, e'.2]⟩ : weightedMonomials w (i + j)) := by
  unfold mulHom
  refine ((CategoryTheory.Category.assoc _ _ _).symm.trans ?_)
  rw [ιM_tensor_ιM_freeTensorFreeIso_hom]
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  exact congrArg (fun t => (λ_ (𝟙_ X.Modules)).hom ≫ t)
    (SheafOfModules.ιFree_freeMap (R := X.ringCatSheaf) _ (e, e'))

/-- Transport along an index equality: `ιFree e ≫ eqToHom (part h) = ιFree ⟨e, _⟩`. -/
theorem ιM_comp_eqToHom {i i' : ℕ} (h : i = i') (e : weightedMonomials w i) :
    ιM X e ≫ eqToHom (congrArg (part X w) h) =
      ιM X (⟨e.1, e.2.trans h⟩ : weightedMonomials w i') := by
  subst h
  simp

/-- `ιM` depends only on the value of the monomial (`Subtype.ext`). -/
theorem ιM_congr {j : ℕ} {e e' : weightedMonomials w j} (h : e.1 = e'.1) :
    ιM X e = ιM X e' := by
  rw [Subtype.ext h]

end AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra

/- The three monoid laws of `weightedPolynomialQCAlgebra`, as separate theorems. Each is reduced to
the generators `ιM = ιFree` (`unit_tensor_hom_ext` / `tensor_hom_ext` / `tensor_tensor_hom_ext`),
both sides are computed with `ιM_tensor_ιM_mulHom`, index equalities are transported by
`ιM_comp_eqToHom`, and the remaining unitor/associator/braiding identities on `𝟙_ ⊗ 𝟙_` follow from
the coherence of the monoidal category (`triangle`, `unitors_equal`, `braiding_leftUnitor`). -/

open AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra in
/-- Left unit law: reduces to `0 + e = e`. -/
theorem AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.one_mul (X : AlgebraicGeometry.Scheme.{u}) {σ : Type u} (w : σ → ℕ) (j : ℕ) :
    (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.oneHom X w ▷ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w j) ≫ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom X w 0 j =
      (λ_ (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w j)).hom ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w) (Nat.zero_add j).symm) := by
  apply unit_tensor_hom_ext
  intro e
  rw [oneHom_eq]
  slice_lhs 1 2 => rw [← CategoryTheory.MonoidalCategory.tensorHom_def']
  slice_lhs 1 2 => rw [ιM_tensor_ιM_mulHom]
  slice_rhs 1 2 => rw [CategoryTheory.MonoidalCategory.leftUnitor_naturality]
  slice_rhs 2 3 => rw [ιM_comp_eqToHom X w (Nat.zero_add j).symm]
  congr 1
  exact ιM_congr X w (zero_add _)

open AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra in
/-- Associativity: reduces to `(e + e′) + e″ = e + (e′ + e″)`. -/
theorem AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mul_assoc (X : AlgebraicGeometry.Scheme.{u}) {σ : Type u} (w : σ → ℕ) (i j l : ℕ) :
    (α_ (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w i) (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w j) (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w l)).hom ≫
        (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w i ◁ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom X w j l) ≫ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom X w i (j + l) =
      (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom X w i j ▷ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w l) ≫ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom X w (i + j) l ≫
        eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w) (Nat.add_assoc i j l)) := by
  apply tensor_tensor_hom_ext
  intro e e' e''
  -- left side: `α ≫ (𝟙 ◁ λ) ≫ λ ≫ ιFree (e + (e′ + e″))`
  slice_lhs 1 2 => rw [CategoryTheory.MonoidalCategory.associator_naturality]
  slice_lhs 2 3 => rw [← CategoryTheory.MonoidalCategory.id_tensorHom,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, CategoryTheory.Category.comp_id,
    ιM_tensor_ιM_mulHom, ← CategoryTheory.Category.id_comp (ιM X e),
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
    CategoryTheory.MonoidalCategory.id_tensorHom]
  slice_lhs 3 4 => rw [ιM_tensor_ιM_mulHom]
  -- right side: `(λ ▷ 𝟙) ≫ λ ≫ ιFree ((e + e′) + e″)`
  slice_rhs 1 2 => rw [← CategoryTheory.MonoidalCategory.tensorHom_id,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, CategoryTheory.Category.comp_id,
    ιM_tensor_ιM_mulHom, ← CategoryTheory.Category.id_comp (ιM X e''),
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
    CategoryTheory.MonoidalCategory.tensorHom_id]
  slice_rhs 2 3 => rw [ιM_tensor_ιM_mulHom]
  slice_rhs 3 4 => rw [ιM_comp_eqToHom X w (Nat.add_assoc i j l)]
  -- coherence: `α ≫ (𝟙 ◁ λ) = ρ ▷ 𝟙 = λ ▷ 𝟙`
  slice_lhs 1 2 => rw [CategoryTheory.MonoidalCategory.triangle, ← CategoryTheory.MonoidalCategory.unitors_equal]
  simp only [CategoryTheory.Category.assoc]
  congr 1
  congr 1
  refine ιM_congr X w ?_
  exact (add_assoc _ _ _).symm

open AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra in
/-- Commutativity: reduces to `e + e′ = e′ + e`. -/
theorem AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mul_comm (X : AlgebraicGeometry.Scheme.{u}) {σ : Type u} (w : σ → ℕ) (i j : ℕ) :
    (β_ (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w i) (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w j)).hom ≫ AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom X w j i =
      AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom X w i j ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w) (Nat.add_comm i j)) := by
  apply tensor_hom_ext
  intro e e'
  slice_lhs 1 2 => rw [CategoryTheory.BraidedCategory.braiding_naturality]
  slice_lhs 2 3 => rw [ιM_tensor_ιM_mulHom]
  slice_lhs 1 2 => rw [CategoryTheory.braiding_leftUnitor,
    ← CategoryTheory.MonoidalCategory.unitors_equal]
  slice_rhs 1 2 => rw [ιM_tensor_ιM_mulHom]
  slice_rhs 2 3 => rw [ιM_comp_eqToHom X w (Nat.add_comm i j)]
  congr 1
  exact ιM_congr X w (add_comm _ _)

noncomputable def AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
    (X : AlgebraicGeometry.Scheme.{u}) {σ : Type u} [Finite σ] (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) : X.GradedQCAlgebra where
  part j := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part X w j
  quasicoherent _ := inferInstance
  mul i j := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom X w i j
  one := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.oneHom X w
  one_mul := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.one_mul X w
  mul_assoc := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mul_assoc X w
  mul_comm := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mul_comm X w

end
