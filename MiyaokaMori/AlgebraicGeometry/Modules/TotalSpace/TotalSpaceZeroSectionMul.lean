import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSectionData

/-! # The augmentation of the symmetric algebra is multiplicative

Statement: `symAugmentation` preserves multiplication on sections over any open.
Proof:
1. Decompose `total.mul` and `tensorSections` along the two graded indices;
2. the components of nonzero total degree vanish because the positive-degree components of the augmentation are zero;
3. the degree-zero component follows from the compatibility of `symPowMul` with the tensor multiplication of the unit
   object.

Route (the three steps above, carried out at the **level of morphisms** and then evaluated on sections):
* `coprod_tensor_hom_ext`: a morphism out of `(∐ P) ⊗ (∐ P)` is determined by the components `ι_m ⊗ₘ ι_n` (the
  tensor–Hom adjunction `tensorObjHomEquiv` and its naturality on the left, twice, + `Sigma.hom_ext`, exchanging the
  sides with the braiding in between);
* `totalMul_component`: `(ι_m ⊗ₘ ι_n) ≫ totalMul S = S.mul m n ≫ ι_{m+n}` (the component formula of `GradedAlgebraTotal`);
* `symPowπ_tensor_symPowDesc₂_zsm` / `symPowπ_tensor_cancel_zsm`: compatibility of `symPowDesc₂` with the quotient map
  `π_m ⊗ₘ π_n`, and the cancellation law;
* `symAugmentationZero_mul`: the degree-zero component `S.mul 0 0 ≫ ε₀ = (ε₀ ⊗ₘ ε₀) ≫ λ_`, proved separately in the two
  branches of `symGradedAlgebra` (the quasi-coherent branch uses `monoidalPowCat W 0 0 = ρ_` and `unitors_equal`; the
  trivial branch is `λ_` by definition);
* `zero_tensorHom` / `tensorHom_zero`: `0 ⊗ₘ f = 0` in `X.Modules` (there is no `MonoidalPreadditive X.Modules` instance,
  so this is computed on pure tensor sections through `tensorObj_hom_ext`);
* `symAugmentation_mul_hom`: `total.mul ≫ ε = (ε ⊗ₘ ε) ≫ λ_`; finally on sections use `tensorHom_tensorSections` and
  `leftUnitor_app_tensorSections` (`r ⊗ s ↦ r • s = r * s`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory
noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `GradedQCAlgebra.totalCurry` and `tensorObjHomEquiv` have the same definition body. -/
theorem totalCurry_eq (F G H : X.Modules) :
    GradedQCAlgebra.totalCurry F G H = tensorObjHomEquiv F G H := rfl

/-- The inverse of currying is natural in the first variable: `(a ▷ G) ≫ uncurry ψ = uncurry (a ≫ ψ)`. -/
theorem tensorObjHomEquiv_symm_naturality_left {F' F : X.Modules} (G H : X.Modules) (a : F' ⟶ F)
    (ψ : F ⟶ internalHom G H) :
    (a ▷ G) ≫ (tensorObjHomEquiv F G H).symm ψ = (tensorObjHomEquiv F' G H).symm (a ≫ ψ) := by
  apply (tensorObjHomEquiv F' G H).injective
  rw [Equiv.apply_symm_apply, ← tensorObjHomEquiv_naturality_left, Equiv.apply_symm_apply]

/-- A morphism out of `(∐ P) ⊗ (∐ P)` is determined by the components `ι_m ⊗ₘ ι_n` (`⊗` preserves coproducts in
each variable, through the tensor–Hom adjunction). -/
theorem coprod_tensor_hom_ext {P : ℕ → X.Modules} {H : X.Modules}
    {f g : (∐ P) ⊗ (∐ P) ⟶ H}
    (h : ∀ m n, (Sigma.ι P m ⊗ₘ Sigma.ι P n) ≫ f = (Sigma.ι P m ⊗ₘ Sigma.ι P n) ≫ g) : f = g := by
  apply (tensorObjHomEquiv _ _ _).injective
  apply Sigma.hom_ext
  intro m
  rw [tensorObjHomEquiv_naturality_left, tensorObjHomEquiv_naturality_left]
  congr 1
  have e0 : ∀ k : (∐ P) ⊗ (∐ P) ⟶ H,
      (β_ (∐ P) (P m)).hom ≫ (Sigma.ι P m ▷ (∐ P)) ≫ k =
        ((∐ P) ◁ Sigma.ι P m) ≫ (β_ (∐ P) (∐ P)).hom ≫ k := by
    intro k
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_right, Category.assoc]
  rw [← cancel_epi (β_ (∐ P) (P m)).hom, e0, e0]
  apply (tensorObjHomEquiv _ _ _).injective
  apply Sigma.hom_ext
  intro n
  rw [tensorObjHomEquiv_naturality_left, tensorObjHomEquiv_naturality_left]
  congr 1
  have e1 : ∀ k : (∐ P) ⊗ (∐ P) ⟶ H,
      (Sigma.ι P n ▷ P m) ≫ ((∐ P) ◁ Sigma.ι P m) ≫ (β_ (∐ P) (∐ P)).hom ≫ k =
        (β_ (P n) (P m)).hom ≫ (Sigma.ι P m ⊗ₘ Sigma.ι P n) ≫ k := by
    intro k
    rw [← Category.assoc, ← MonoidalCategory.tensorHom_def, ← Category.assoc,
      BraidedCategory.braiding_naturality, Category.assoc]
  rw [e1, e1, h]

/-- The component formula for `totalMul`: `(ι_m ⊗ₘ ι_n) ≫ totalMul S = S.mul m n ≫ ι_{m+n}`. -/
theorem totalMul_component (S : X.GradedQCAlgebra) (m n : ℕ) :
    (Sigma.ι S.part m ⊗ₘ Sigma.ι S.part n) ≫ GradedQCAlgebra.totalMul S =
      S.mul m n ≫ Sigma.ι S.part (m + n) := by
  have h1 : (Sigma.ι S.part m ▷ (∐ S.part)) ≫ GradedQCAlgebra.totalMul S =
      GradedQCAlgebra.totalMulRow S m := by
    unfold GradedQCAlgebra.totalMul
    simp only [totalCurry_eq]
    rw [tensorObjHomEquiv_symm_naturality_left, Sigma.ι_desc, Equiv.symm_apply_apply]
  rw [MonoidalCategory.tensorHom_def', Category.assoc, h1]
  unfold GradedQCAlgebra.totalMulRow
  simp only [totalCurry_eq]
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc,
    tensorObjHomEquiv_symm_naturality_left, Sigma.ι_desc, Equiv.symm_apply_apply,
    ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- The degree-zero component of the augmentation. -/
theorem ι_zero_comp_symAugmentation (W : X.Modules) :
    Sigma.ι (symGradedAlgebra W).part 0 ≫ symAugmentation W = symAugmentationZero W :=
  Sigma.ι_desc _ _

/-- The positive-degree components of the augmentation vanish. -/
theorem ι_comp_symAugmentation_of_ne_zero (W : X.Modules) (k : ℕ) (hk : k ≠ 0) :
    Sigma.ι (symGradedAlgebra W).part k ≫ symAugmentation W = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact Sigma.ι_desc _ _

/-- Computation rule for the two-variable descent: `(π_m ⊗ₘ π_n) ≫ symPowDesc₂ f = f`. -/
theorem symPowπ_tensor_symPowDesc₂_zsm (V : X.Modules) (m n : ℕ) {T : X.Modules}
    (f : monoidalPow V m ⊗ monoidalPow V n ⟶ T)
    (hf₁ : ∀ i : Fin m, (monoidalPowTransp V m i ▷ monoidalPow V n) ≫ f = f)
    (hf₂ : ∀ j : Fin n, (monoidalPow V m ◁ monoidalPowTransp V n j) ≫ f = f) :
    (symPowπ V m ⊗ₘ symPowπ V n) ≫ symPowDesc₂ V m n f hf₁ hf₂ = f := by
  unfold symPowDesc₂
  dsimp only
  rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc,
    MonoidalCategory.tensorHom_def', Category.assoc, symPowπ_whiskerRight_descCurry,
    BraidedCategory.braiding_naturality_right_assoc, symPowπ_whiskerRight_descCurry,
    ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- `π_m ⊗ₘ π_n` is an epimorphism. -/
theorem symPowπ_tensor_cancel_zsm (V : X.Modules) (m n : ℕ) {T : X.Modules}
    (x y : symPow V m ⊗ symPow V n ⟶ T)
    (h : (symPowπ V m ⊗ₘ symPowπ V n) ≫ x = (symPowπ V m ⊗ₘ symPowπ V n) ≫ y) : x = y := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, Category.assoc] at h
  have h' := symPowπ_whiskerRight_cancel V m _ _ _ h
  rw [← cancel_epi (β_ (symPow V n) (symPow V m)).hom]
  apply symPowπ_whiskerRight_cancel V n
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc, h',
    ← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc]

/-- An `Eq.mpr`-type cast written as composition with `eqToHom`. -/
theorem eqMpr_hom_eq_eqToHom_comp {C : Type v} [Category.{w} C] {A A' B : C} (h : A = A')
    (f : A' ⟶ B) :
    (congrArg (fun Z : C => Z ⟶ B) h).mpr f = eqToHom h ≫ f := by
  subst h
  simp

/-- Transporting a graded algebra along an equality, the multiplication is compatible with `eqToHom`. -/
theorem GradedQCAlgebra.mul_eqToHom {S S' : X.GradedQCAlgebra} (hS : S = S') (m n : ℕ) :
    S.mul m n ≫ eqToHom (congrArg (fun T : X.GradedQCAlgebra => T.part (m + n)) hS) =
      (eqToHom (congrArg (fun T : X.GradedQCAlgebra => T.part m) hS) ⊗ₘ
        eqToHom (congrArg (fun T : X.GradedQCAlgebra => T.part n) hS)) ≫ S'.mul m n := by
  subst hS
  simp

/-- The degree-zero computation in the quasi-coherent branch: every `ε₀ : Sym⁰ W ⟶ 𝟙_` with `π₀ ≫ ε₀ = 𝟙` satisfies
    `symPowMul W 0 0 ≫ ε₀ = (ε₀ ⊗ₘ ε₀) ≫ λ_` (using that `π₀ ⊗ₘ π₀` is an epimorphism, `monoidalPowCat W 0 0 = ρ_` and
    `unitors_equal`). -/
theorem symPowMul_zero_zero_comp (W : X.Modules) (ε₀ : symPow W 0 ⟶ 𝟙_ X.Modules)
    (hπ : symPowπ W 0 ≫ ε₀ = 𝟙 (𝟙_ X.Modules)) :
    symPowMul W 0 0 ≫ ε₀ = (ε₀ ⊗ₘ ε₀) ≫ (λ_ (𝟙_ X.Modules)).hom := by
  apply symPowπ_tensor_cancel_zsm W 0 0
  have hL : (symPowπ W 0 ⊗ₘ symPowπ W 0) ≫ symPowMul W 0 0 =
      (monoidalPowCat W 0 0).hom ≫ symPowπ W 0 :=
    symPowπ_tensor_symPowDesc₂_zsm W 0 0 _ _ _
  have h1 : (monoidalPowCat W 0 0).hom ≫ 𝟙 (𝟙_ X.Modules) = (λ_ (𝟙_ X.Modules)).hom :=
    (Category.comp_id _).trans MonoidalCategory.unitors_equal.symm
  have h2 : (symPowπ W 0 ⊗ₘ symPowπ W 0) ≫ (ε₀ ⊗ₘ ε₀) ≫ (λ_ (𝟙_ X.Modules)).hom =
      (λ_ (𝟙_ X.Modules)).hom := by
    have h3 : (𝟙 (𝟙_ X.Modules) ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (λ_ (𝟙_ X.Modules)).hom =
        (λ_ (𝟙_ X.Modules)).hom := by
      rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hπ]
    exact h3
  rw [← Category.assoc, hL, Category.assoc, hπ, h2]
  exact h1

/-- Multiplicativity on the degree-zero component: `S.mul 0 0 ≫ ε₀ = (ε₀ ⊗ₘ ε₀) ≫ λ_`, in the two branches of
    `symGradedAlgebra`. The definition body of `symAugmentationZero` is a `Decidable.casesOn` on
    `Classical.propDecidable`, each branch carrying an `Eq.mpr` cast; we first replace the instance by
    `isTrue`/`isFalse` with `Subsingleton.elim` to reduce the `casesOn`, then rewrite the casts as `eqToHom` by proof
    irrelevance, and finally move the multiplication to the concrete branch along `dif_pos`/`dif_neg` with
    `GradedQCAlgebra.mul_eqToHom`. -/
theorem symAugmentationZero_mul (W : X.Modules) :
    (symGradedAlgebra W).mul 0 0 ≫ symAugmentationZero W =
      (symAugmentationZero W ⊗ₘ symAugmentationZero W) ≫ (λ_ (𝟙_ X.Modules)).hom := by
  unfold symAugmentationZero
  by_cases hW : W.IsQuasicoherent
  · have e : (Classical.propDecidable W.IsQuasicoherent) = isTrue hW := Subsingleton.elim _ _
    simp only [e]
    have hS : symGradedAlgebra W = symGradedAlgebraOfQC W hW := dif_pos hW
    have hA : (symGradedAlgebra W).part 0 = symPow W 0 := congrArg (fun S => S.part 0) hS
    change (symGradedAlgebra W).mul 0 0 ≫
        (congrArg (fun Z : X.Modules => Z ⟶ 𝟙_ X.Modules) hA).mpr
          (symPowDesc W 0 (𝟙 _) (fun i => i.elim0)) =
      ((congrArg (fun Z : X.Modules => Z ⟶ 𝟙_ X.Modules) hA).mpr
          (symPowDesc W 0 (𝟙 _) (fun i => i.elim0)) ⊗ₘ
        (congrArg (fun Z : X.Modules => Z ⟶ 𝟙_ X.Modules) hA).mpr
          (symPowDesc W 0 (𝟙 _) (fun i => i.elim0))) ≫ (λ_ (𝟙_ X.Modules)).hom
    rw [eqMpr_hom_eq_eqToHom_comp]
    have key : (symGradedAlgebra W).mul 0 0 ≫ eqToHom hA =
        (eqToHom hA ⊗ₘ eqToHom hA) ≫ symPowMul W 0 0 :=
      GradedQCAlgebra.mul_eqToHom hS 0 0
    rw [← Category.assoc, key, Category.assoc, ← MonoidalCategory.tensorHom_comp_tensorHom,
      Category.assoc]
    exact congrArg (fun k => (eqToHom hA ⊗ₘ eqToHom hA) ≫ k)
      (symPowMul_zero_zero_comp W (symPowDesc W 0 (𝟙 _) (fun i => i.elim0))
        (symPowπ_desc W 0 _ _))
  · have e : (Classical.propDecidable W.IsQuasicoherent) = isFalse hW := Subsingleton.elim _ _
    simp only [e]
    have hS : symGradedAlgebra W = GradedQCAlgebra.trivial X := dif_neg hW
    have hA : (symGradedAlgebra W).part 0 = 𝟙_ X.Modules := congrArg (fun S => S.part 0) hS
    change (symGradedAlgebra W).mul 0 0 ≫
        (congrArg (fun Z : X.Modules => Z ⟶ 𝟙_ X.Modules) hA).mpr (𝟙 (𝟙_ X.Modules)) =
      ((congrArg (fun Z : X.Modules => Z ⟶ 𝟙_ X.Modules) hA).mpr (𝟙 (𝟙_ X.Modules)) ⊗ₘ
        (congrArg (fun Z : X.Modules => Z ⟶ 𝟙_ X.Modules) hA).mpr (𝟙 (𝟙_ X.Modules))) ≫
        (λ_ (𝟙_ X.Modules)).hom
    rw [eqMpr_hom_eq_eqToHom_comp]
    have key : (symGradedAlgebra W).mul 0 0 ≫ eqToHom hA =
        (eqToHom hA ⊗ₘ eqToHom hA) ≫ (λ_ (𝟙_ X.Modules)).hom :=
      GradedQCAlgebra.mul_eqToHom hS 0 0
    rw [← Category.assoc, key, Category.assoc, ← MonoidalCategory.tensorHom_comp_tensorHom,
      Category.assoc]
    have h1 : (λ_ (𝟙_ X.Modules)).hom ≫ 𝟙 (𝟙_ X.Modules) =
        (𝟙 (𝟙_ X.Modules) ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (λ_ (𝟙_ X.Modules)).hom := by
      rw [MonoidalCategory.id_tensorHom_id, Category.id_comp, Category.comp_id]
    exact congrArg (fun k => (eqToHom hA ⊗ₘ eqToHom hA) ≫ k) h1

/-- `0 ⊗ₘ ψ = 0` in `X.Modules` (there is no `MonoidalPreadditive X.Modules` instance; computed on pure tensor sections). -/
theorem zero_tensorHom {A B A' B' : X.Modules} (ψ : B ⟶ B') :
    ((0 : A ⟶ A') ⊗ₘ ψ) = 0 := by
  apply tensorObj_hom_ext
  intro U s t
  refine (tensorHom_tensorSections (0 : A ⟶ A') ψ U s t).trans ?_
  change tensorSections A' B' U ((0 : A ⟶ A').app U s) _ = (0 : A ⊗ B ⟶ A' ⊗ B').app U _
  rw [Hom.zero_app, Hom.zero_app]
  exact tensorSections_zero_left A' B' U _

/-- `φ ⊗ₘ 0 = 0` in `X.Modules`. -/
theorem tensorHom_zero {A B A' B' : X.Modules} (φ : A ⟶ A') :
    (φ ⊗ₘ (0 : B ⟶ B')) = 0 := by
  apply tensorObj_hom_ext
  intro U s t
  refine (tensorHom_tensorSections φ (0 : B ⟶ B') U s t).trans ?_
  change tensorSections A' B' U _ ((0 : B ⟶ B').app U t) = (0 : A ⊗ B ⟶ A' ⊗ B').app U _
  rw [Hom.zero_app, Hom.zero_app]
  exact tensorSections_zero_right A' B' U _

/-- Multiplicativity at the level of morphisms: `total.mul ≫ ε = (ε ⊗ₘ ε) ≫ λ_`. -/
theorem symAugmentation_mul_hom (W : X.Modules) :
    (symGradedAlgebra W).total.mul ≫ symAugmentation W =
      (symAugmentation W ⊗ₘ symAugmentation W) ≫ (λ_ (𝟙_ X.Modules)).hom := by
  apply coprod_tensor_hom_ext
  intro m n
  have hL : (Sigma.ι (symGradedAlgebra W).part m ⊗ₘ Sigma.ι (symGradedAlgebra W).part n) ≫
      ((symGradedAlgebra W).total.mul ≫ symAugmentation W) =
        (symGradedAlgebra W).mul m n ≫ (Sigma.ι (symGradedAlgebra W).part (m + n) ≫
          symAugmentation W) :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ symAugmentation W)
        (totalMul_component (symGradedAlgebra W) m n))).trans (Category.assoc _ _ _)
  have hR : (Sigma.ι (symGradedAlgebra W).part m ⊗ₘ Sigma.ι (symGradedAlgebra W).part n) ≫
      ((symAugmentation W ⊗ₘ symAugmentation W) ≫ (λ_ (𝟙_ X.Modules)).hom) =
        ((Sigma.ι (symGradedAlgebra W).part m ≫ symAugmentation W) ⊗ₘ
          (Sigma.ι (symGradedAlgebra W).part n ≫ symAugmentation W)) ≫ (λ_ (𝟙_ X.Modules)).hom := by
    rw [← Category.assoc]
    exact congrArg (fun k => k ≫ (λ_ (𝟙_ X.Modules)).hom)
      (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _)
  refine hL.trans (Eq.trans ?_ hR.symm)
  by_cases hmn : m + n = 0
  · obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
    have h0 : Sigma.ι (symGradedAlgebra W).part (0 + 0) ≫ symAugmentation W =
        symAugmentationZero W := Sigma.ι_desc _ _
    simp only [h0]
    exact symAugmentationZero_mul W
  · rw [ι_comp_symAugmentation_of_ne_zero W (m + n) hmn, comp_zero]
    by_cases hm : m = 0
    · rw [ι_comp_symAugmentation_of_ne_zero W n (by omega), tensorHom_zero, zero_comp]
    · rw [ι_comp_symAugmentation_of_ne_zero W m hm, zero_tensorHom, zero_comp]

/-- `tensorHom_tensorSections` in the `Hom.app` spelling. -/
theorem tensorHom_app_tensorSections {A B A' B' : X.Modules} (φ : A ⟶ A') (ψ : B ⟶ B')
    (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) :
    (φ ⊗ₘ ψ).app U (tensorSections A B U a b) =
      tensorSections A' B' U (φ.app U a) (ψ.app U b) :=
  tensorHom_tensorSections φ ψ U a b

end AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.symAugmentation_mul {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) (U : X.Opens)
    (a b : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.carrier.val.obj
      (Opposite.op U)) :
    (show Γ(X, (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ U) from
      (AlgebraicGeometry.Scheme.Modules.symAugmentation W ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app
          (SheafOfModules.unit X.ringCatSheaf)).app U
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.mul.app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.carrier
            (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.carrier U a b))) =
      (show Γ(X, (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ U) from
        (AlgebraicGeometry.Scheme.Modules.symAugmentation W ≫
          (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app
            (SheafOfModules.unit X.ringCatSheaf)).app U a) *
        (show Γ(X, (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ U) from
          (AlgebraicGeometry.Scheme.Modules.symAugmentation W ≫
            (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app
              (SheafOfModules.unit X.ringCatSheaf)).app U b) := by
  have h : (AlgebraicGeometry.Scheme.Modules.symAugmentation W).app U
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.mul.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b)) =
      (λ_ (𝟙_ X.Modules)).hom.app U
        ((AlgebraicGeometry.Scheme.Modules.symAugmentation W ⊗ₘ
          AlgebraicGeometry.Scheme.Modules.symAugmentation W).app U
            (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b)) :=
    congrArg (fun k => k.app U (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b))
      (AlgebraicGeometry.Scheme.Modules.symAugmentation_mul_hom W)
  have h2 := AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections
    (AlgebraicGeometry.Scheme.Modules.symAugmentation W)
    (AlgebraicGeometry.Scheme.Modules.symAugmentation W) U a b
  have h3 := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections (𝟙_ X.Modules) U
    ((AlgebraicGeometry.Scheme.Modules.symAugmentation W).app U a)
    ((AlgebraicGeometry.Scheme.Modules.symAugmentation W).app U b)
  exact h.trans ((congrArg ((λ_ (𝟙_ X.Modules)).hom.app U) h2).trans h3)
end
