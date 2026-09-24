import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # The total algebra of a graded quasi-coherent algebra

The total algebra `⊕_m S_m` of a graded algebra sheaf, forgetting the grading, as a `QCAlgebra`
(the relative Spec of this algebra is the total space of the jet bundle). The algebra laws
`total_one_mul` / `total_mul_assoc` / `total_mul_comm` are proved through the left naturality of
`totalCurry`, the fact that morphisms out of a coproduct tensored with a coproduct are determined by
the components `ι_m ⊗ₘ ι_n` (`coprod_*_hom_ext`), and the component formula
`tensor_ι_comp_totalMul` for `totalMul`; the `eqToHom`s are absorbed by `Sigma.eqToHom_comp_ι`.
`total_isQuasicoherent` reduces to `isQuasicoherent_colimit` (Stacks 01ID).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- `⊕_m S_m` as a `QCAlgebra`: the underlying sheaf is the countable coproduct `∐ S.part` in `X.Modules`
 (Mathlib's `HasColimits X.Modules`); the multiplication is given componentwise through the tensor–Hom
   adjunction: `(∐_m S_m) ⊗ (∐_n S_n) → ∐_k S_k` is `S.mul m n` followed by the inclusion of the `(m+n)`-th
   summand on the `(m, n)` component. The adjunction `tensorHomEquiv` is stated for `Modules.tensor`; the
   canonical isomorphism `Modules.tensor ≅ ⊗` (`tensorIsoTensorObj`) converts it to the monoidal `⊗`. -/

/-- Currying for the monoidal `⊗`: `(F ⊗ G ⟶ H) ≃ (F ⟶ 𝓗om(G, H))`. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.totalCurry {X : AlgebraicGeometry.Scheme.{u}} (F G H : X.Modules) :
    (F ⊗ G ⟶ H) ≃ (F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H) :=
  ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).homCongr (CategoryTheory.Iso.refl H)).symm.trans
    (AlgebraicGeometry.Scheme.Modules.tensorHomEquiv F G H)

/-- For fixed `m`: `S_m ⊗ C → C` (`C = ∐ S.part`). First swap to `C ⊗ S_m`, then curry on each component
`S_n` of `C`: `S_n ⊗ S_m ≅ S_m ⊗ S_n → S_{m+n} → C`. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMulRow {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) : S.part m ⊗ (∐ S.part) ⟶ (∐ S.part) :=
  (β_ (S.part m) (∐ S.part)).hom ≫
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.totalCurry (∐ S.part) (S.part m) (∐ S.part)).symm
      (CategoryTheory.Limits.Sigma.desc fun n =>
        AlgebraicGeometry.Scheme.GradedQCAlgebra.totalCurry (S.part n) (S.part m) (∐ S.part)
          ((β_ (S.part n) (S.part m)).hom ≫ S.mul m n ≫ CategoryTheory.Limits.Sigma.ι S.part (m + n)))

/-- The multiplication of `⊕_m S_m`: on the `(m, n)` component it is `S.mul m n` followed by the inclusion of
the `(m+n)`-th summand. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) : (∐ S.part) ⊗ (∐ S.part) ⟶ (∐ S.part) :=
  (AlgebraicGeometry.Scheme.GradedQCAlgebra.totalCurry (∐ S.part) (∐ S.part) (∐ S.part)).symm
    (CategoryTheory.Limits.Sigma.desc fun m =>
      AlgebraicGeometry.Scheme.GradedQCAlgebra.totalCurry (S.part m) (∐ S.part) (∐ S.part) (AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMulRow S m))

/- The four proof obligations of `GradedQCAlgebra.total` (quasi-coherence and the three algebra laws) are
   stated as named theorems below. First: the naturality of `totalCurry`, the extensionality lemmas for
   morphisms out of a tensor product of coproducts, and the component formula for `totalMul`. -/

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The inverse of `totalCurry` is `ψ ↦ (ψ ▷ G) ≫ evaluation` (same proof as
`SheafSymmetricAlgebra.tensorObjHomEquiv_symm_apply`; `totalCurry` and `tensorObjHomEquiv` have the same
body, but that file is not imported here to avoid a dependency). -/
theorem totalCurry_symm_apply (F G H : X.Modules) (ψ : F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H) :
    (totalCurry F G H).symm ψ = (ψ ▷ G) ≫ AlgebraicGeometry.Scheme.Modules.internalHomEval G H := by
  have e : (AlgebraicGeometry.Scheme.Modules.tensorHomEquiv F G H).symm ψ =
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).hom ≫ (ψ ▷ G) ≫
        AlgebraicGeometry.Scheme.Modules.internalHomEval G H := rfl
  show ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).homCongr (Iso.refl H))
    ((AlgebraicGeometry.Scheme.Modules.tensorHomEquiv F G H).symm ψ) = _
  rw [e]
  simp [Iso.homCongr]

/-- Currying is natural in the first variable: `a ≫ curry f = curry ((a ▷ G) ≫ f)`. -/
theorem totalCurry_naturality_left {F' F : X.Modules} (G H : X.Modules) (a : F' ⟶ F) (f : F ⊗ G ⟶ H) :
    a ≫ totalCurry F G H f = totalCurry F' G H ((a ▷ G) ≫ f) := by
  apply (totalCurry F' G H).symm.injective
  rw [Equiv.symm_apply_apply, totalCurry_symm_apply, MonoidalCategory.comp_whiskerRight,
    Category.assoc, ← totalCurry_symm_apply, Equiv.symm_apply_apply]

/-- The inverse form: `(a ▷ G) ≫ curry⁻¹ D = curry⁻¹ (a ≫ D)`. -/
theorem whiskerRight_totalCurry_symm {F' F G H : X.Modules} (a : F' ⟶ F)
    (D : F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H) :
    (a ▷ G) ≫ (totalCurry F G H).symm D = (totalCurry F' G H).symm (a ≫ D) := by
  apply (totalCurry F' G H).injective
  rw [Equiv.apply_symm_apply, ← totalCurry_naturality_left, Equiv.apply_symm_apply]

/-- Morphisms out of `(∐ P) ⊗ K` are determined by the `ι_i ▷ K` (`- ⊗ K` is a left adjoint; by currying
this is `Sigma.hom_ext`). -/
theorem coprod_whiskerRight_hom_ext {ι : Type w} (P : ι → X.Modules) [HasCoproduct P] (K : X.Modules)
    {H : X.Modules} {f g : (∐ P) ⊗ K ⟶ H}
    (h : ∀ i, (Sigma.ι P i ▷ K) ≫ f = (Sigma.ι P i ▷ K) ≫ g) : f = g := by
  apply (totalCurry _ _ _).injective
  apply Sigma.hom_ext
  intro i
  rw [totalCurry_naturality_left, totalCurry_naturality_left, h]

/-- Morphisms out of `F ⊗ (∐ P)` are determined by the `F ◁ ι_j` (reduce to the previous lemma by the
braiding). -/
theorem coprod_whiskerLeft_hom_ext (F : X.Modules) {ι : Type w} (P : ι → X.Modules) [HasCoproduct P]
    {H : X.Modules} {f g : F ⊗ (∐ P) ⟶ H}
    (h : ∀ j, (F ◁ Sigma.ι P j) ≫ f = (F ◁ Sigma.ι P j) ≫ g) : f = g := by
  rw [← cancel_epi (β_ (∐ P) F).hom]
  apply coprod_whiskerRight_hom_ext
  intro j
  rw [BraidedCategory.braiding_naturality_left_assoc, BraidedCategory.braiding_naturality_left_assoc, h]

/-- Morphisms out of `(∐ P) ⊗ (∐ Q)` are determined by the components `ι_i ⊗ₘ ι_j`. -/
theorem coprod_tensor_hom_ext {ι κ : Type w} (P : ι → X.Modules) (Q : κ → X.Modules)
    [HasCoproduct P] [HasCoproduct Q] {H : X.Modules} {f g : (∐ P) ⊗ (∐ Q) ⟶ H}
    (h : ∀ i j, (Sigma.ι P i ⊗ₘ Sigma.ι Q j) ≫ f = (Sigma.ι P i ⊗ₘ Sigma.ι Q j) ≫ g) : f = g := by
  apply coprod_whiskerRight_hom_ext
  intro i
  apply coprod_whiskerLeft_hom_ext
  intro j
  rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.tensorHom_def', h]

/-- Morphisms out of `((∐ P) ⊗ (∐ Q)) ⊗ (∐ R)` are determined by the components `(ι_i ⊗ₘ ι_j) ⊗ₘ ι_k`. -/
theorem coprod_tensor_tensor_hom_ext {ι κ μ : Type w} (P : ι → X.Modules) (Q : κ → X.Modules)
    (R : μ → X.Modules) [HasCoproduct P] [HasCoproduct Q] [HasCoproduct R]
    {H : X.Modules} {f g : ((∐ P) ⊗ (∐ Q)) ⊗ (∐ R) ⟶ H}
    (h : ∀ i j k, ((Sigma.ι P i ⊗ₘ Sigma.ι Q j) ⊗ₘ Sigma.ι R k) ≫ f =
      ((Sigma.ι P i ⊗ₘ Sigma.ι Q j) ⊗ₘ Sigma.ι R k) ≫ g) : f = g := by
  apply coprod_whiskerLeft_hom_ext
  intro k
  apply (totalCurry _ _ _).injective
  apply coprod_tensor_hom_ext
  intro i j
  rw [totalCurry_naturality_left, totalCurry_naturality_left]
  congr 1
  rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.tensorHom_def, h]

/-- `(ι_m ▷ C) ≫ totalMul S = totalMulRow S m`. -/
theorem whiskerRight_ι_comp_totalMul (S : X.GradedQCAlgebra) (m : ℕ) :
    (Sigma.ι S.part m ▷ (∐ S.part)) ≫ totalMul S = totalMulRow S m := by
  unfold totalMul
  rw [whiskerRight_totalCurry_symm, Sigma.ι_desc, Equiv.symm_apply_apply]

/-- `(S_m ◁ ι_n) ≫ totalMulRow S m = S.mul m n ≫ ι_{m+n}`. -/
theorem whiskerLeft_ι_comp_totalMulRow (S : X.GradedQCAlgebra) (m n : ℕ) :
    (S.part m ◁ Sigma.ι S.part n) ≫ totalMulRow S m = S.mul m n ≫ Sigma.ι S.part (m + n) := by
  unfold totalMulRow
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc,
    whiskerRight_totalCurry_symm, Sigma.ι_desc, Equiv.symm_apply_apply,
    SymmetricCategory.symmetry_assoc]

/-- The component formula for `totalMul`: `(ι_m ⊗ₘ ι_n) ≫ totalMul S = S.mul m n ≫ ι_{m+n}`. -/
theorem tensor_ι_comp_totalMul (S : X.GradedQCAlgebra) (m n : ℕ) :
    (Sigma.ι S.part m ⊗ₘ Sigma.ι S.part n) ≫ totalMul S = S.mul m n ≫ Sigma.ι S.part (m + n) := by
  rw [MonoidalCategory.tensorHom_def', Category.assoc, whiskerRight_ι_comp_totalMul,
    whiskerLeft_ι_comp_totalMulRow]

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-- Quasi-coherent modules are closed under arbitrary coproducts (Stacks 01ID; quasi-coherent sheaves on a
scheme are closed under colimits). Proof: `∐ S.part` is isomorphic to `∐ (S.part ∘ ULift.down)` via the
reindexing isomorphism `Sigma.reindex Equiv.ulift` (the index type is lifted to `Type u` to match the
universe of `isQuasicoherent_colimit`); the latter is a colimit over `Discrete (ULift ℕ)` with
quasi-coherent vertices `S.part m` (`S.quasicoherent`), hence quasi-coherent by `isQuasicoherent_colimit`;
quasi-coherence is transported along isomorphisms (Mathlib's `SheafOfModules.isQuasicoherent` is an
`ObjectProperty`, `prop_of_iso`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.total_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) : (∐ S.part).IsQuasicoherent := by
  have h : (∐ (S.part ∘ (Equiv.ulift.{u, 0} : ULift.{u} ℕ ≃ ℕ))).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_colimit
      (Discrete.functor (S.part ∘ (Equiv.ulift.{u, 0} : ULift.{u} ℕ ≃ ℕ)))
      (fun j => S.quasicoherent j.as.down)
  exact ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (Sigma.reindex (Equiv.ulift.{u, 0} : ULift.{u} ℕ ≃ ℕ) S.part) h

/-- Left unit law of the total algebra. Proof: both sides are morphisms out of `𝟙 ⊗ ∐ S.part`; compare them
componentwise with `coprod_whiskerLeft_hom_ext`. On the `n`-th component the left side becomes `λ_ ≫ ι_n`
by naturality of the left unitor, the right side becomes `(S.one ▷ S_n) ≫ S.mul 0 n ≫ ι_{0+n}` by
`tensor_ι_comp_totalMul`; then use `S.one_mul n`, and `Sigma.eqToHom_comp_ι` absorbs the `eqToHom`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.total_one_mul {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) :
    (λ_ (∐ S.part)).hom =
      ((S.one ≫ CategoryTheory.Limits.Sigma.ι S.part 0) ▷ (∐ S.part)) ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S := by
  apply AlgebraicGeometry.Scheme.GradedQCAlgebra.coprod_whiskerLeft_hom_ext
  intro n
  have hR : (𝟙_ X.Modules ◁ Sigma.ι S.part n) ≫
      ((S.one ≫ Sigma.ι S.part 0) ▷ (∐ S.part)) ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S =
      (S.one ▷ S.part n) ≫ S.mul 0 n ≫ Sigma.ι S.part (0 + n) := by
    rw [← Category.assoc, ← MonoidalCategory.tensorHom_def',
      ← MonoidalCategory.whiskerRight_comp_tensorHom, Category.assoc,
      AlgebraicGeometry.Scheme.GradedQCAlgebra.tensor_ι_comp_totalMul]
  have e := reassoc_of% (S.one_mul n)
  rw [hR, MonoidalCategory.leftUnitor_naturality, e, Sigma.eqToHom_comp_ι S.part (Nat.zero_add n).symm]

/-- Associativity of the total algebra. Proof: compare componentwise on `(m, n, p)` with
`coprod_tensor_tensor_hom_ext`; naturality of the associator, the interchange laws
`tensorHom_comp_whiskerLeft`/`whiskerLeft_comp_tensorHom`, and `tensor_ι_comp_totalMul` (twice) reduce the
two sides to `α ≫ (S_m ◁ S.mul n p) ≫ S.mul m (n+p) ≫ ι` and `(S.mul m n ▷ S_p) ≫ S.mul (m+n) p ≫ ι`; then use
`S.mul_assoc m n p`, and `Sigma.eqToHom_comp_ι` absorbs the `eqToHom`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.total_mul_assoc {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) :
    (α_ (∐ S.part) (∐ S.part) (∐ S.part)).hom ≫ ((∐ S.part) ◁ AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S) ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S =
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S ▷ (∐ S.part)) ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S := by
  apply AlgebraicGeometry.Scheme.GradedQCAlgebra.coprod_tensor_tensor_hom_ext
  intro m n p
  have hL : ((Sigma.ι S.part m ⊗ₘ Sigma.ι S.part n) ⊗ₘ Sigma.ι S.part p) ≫
      (α_ (∐ S.part) (∐ S.part) (∐ S.part)).hom ≫
        ((∐ S.part) ◁ AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S) ≫
          AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S =
      (α_ (S.part m) (S.part n) (S.part p)).hom ≫ (S.part m ◁ S.mul n p) ≫ S.mul m (n + p) ≫
        Sigma.ι S.part (m + (n + p)) := by
    rw [MonoidalCategory.associator_naturality_assoc, ← Category.assoc (_ ⊗ₘ _),
      MonoidalCategory.tensorHom_comp_whiskerLeft,
      AlgebraicGeometry.Scheme.GradedQCAlgebra.tensor_ι_comp_totalMul,
      ← MonoidalCategory.whiskerLeft_comp_tensorHom, Category.assoc,
      AlgebraicGeometry.Scheme.GradedQCAlgebra.tensor_ι_comp_totalMul]
  have hR : ((Sigma.ι S.part m ⊗ₘ Sigma.ι S.part n) ⊗ₘ Sigma.ι S.part p) ≫
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S ▷ (∐ S.part)) ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S =
      (S.mul m n ▷ S.part p) ≫ S.mul (m + n) p ≫ Sigma.ι S.part (m + n + p) := by
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_whiskerRight,
      AlgebraicGeometry.Scheme.GradedQCAlgebra.tensor_ι_comp_totalMul,
      ← MonoidalCategory.whiskerRight_comp_tensorHom, Category.assoc,
      AlgebraicGeometry.Scheme.GradedQCAlgebra.tensor_ι_comp_totalMul]
  have e := reassoc_of% (S.mul_assoc m n p)
  rw [hL, hR, e, Sigma.eqToHom_comp_ι S.part (Nat.add_assoc m n p)]

/-- Commutativity of the total algebra. Proof: compare componentwise on `(m, n)` with `coprod_tensor_hom_ext`;
naturality of the braiding and `tensor_ι_comp_totalMul` turn the left side into `β ≫ S.mul n m ≫ ι_{n+m}` and
the right side into `S.mul m n ≫ ι_{m+n}`; then use `S.mul_comm m n`, and `Sigma.eqToHom_comp_ι` absorbs the
`eqToHom`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.total_mul_comm {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) :
    (β_ (∐ S.part) (∐ S.part)).hom ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S = AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S := by
  apply AlgebraicGeometry.Scheme.GradedQCAlgebra.coprod_tensor_hom_ext
  intro m n
  rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc,
    AlgebraicGeometry.Scheme.GradedQCAlgebra.tensor_ι_comp_totalMul,
    AlgebraicGeometry.Scheme.GradedQCAlgebra.tensor_ι_comp_totalMul, ← Category.assoc, S.mul_comm m n,
    Category.assoc, Sigma.eqToHom_comp_ι S.part (Nat.add_comm m n)]

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.total {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) : X.QCAlgebra where
  carrier := ∐ S.part
  quasicoherent := AlgebraicGeometry.Scheme.GradedQCAlgebra.total_isQuasicoherent S
  mul := AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul S
  one := S.one ≫ CategoryTheory.Limits.Sigma.ι S.part 0
  one_mul := AlgebraicGeometry.Scheme.GradedQCAlgebra.total_one_mul S
  mul_assoc := AlgebraicGeometry.Scheme.GradedQCAlgebra.total_mul_assoc S
  mul_comm := AlgebraicGeometry.Scheme.GradedQCAlgebra.total_mul_comm S

end
