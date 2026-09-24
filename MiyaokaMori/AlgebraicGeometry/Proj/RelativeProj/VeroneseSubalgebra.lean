import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # The Veronese subalgebra

The Veronese subalgebra `S^{(m)} = ⊕_{ℓ ≥ 0} S_{ℓm}` of a graded quasi-coherent algebra sheaf
(Lemma 2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- Multiplication of the Veronese subalgebra, `S_{ℓm} ⊗ S_{ℓ'm} → S_{(ℓ+ℓ')m}`. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseMul {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (ℓ ℓ' : ℕ) :
    S.part (ℓ * m) ⊗ S.part (ℓ' * m) ⟶ S.part ((ℓ + ℓ') * m) :=
  S.mul (ℓ * m) (ℓ' * m) ≫ eqToHom (congrArg S.part (add_mul ℓ ℓ' m).symm)

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseOne {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) : 𝟙_ X.Modules ⟶ S.part (0 * m) :=
  S.one ≫ eqToHom (congrArg S.part (zero_mul m).symm)

/-- The unit law of the Veronese subalgebra, from `S.one_mul (ℓ * m)` and the transport of the
index equality `0 * m = 0` along `eqToHom`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseMul_one_mul {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (ℓ : ℕ) :
    (S.veroneseOne m ▷ S.part (ℓ * m)) ≫ S.veroneseMul m 0 ℓ =
      (λ_ (S.part (ℓ * m))).hom ≫
        eqToHom (congrArg (fun ℓ => S.part (ℓ * m)) (Nat.zero_add ℓ).symm) := by
  simp only [AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseOne,
    AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseMul,
    MonoidalCategory.comp_whiskerRight,
    Nat.zero_mul, Nat.zero_add]
  simp only [Category.assoc]
  change S.one ▷ S.part (ℓ * m) ≫
      (eqToHom (congrArg S.part (Nat.zero_mul m).symm) ▷ S.part (ℓ * m)) ≫
        S.mul (0 * m) (ℓ * m) ≫ _ = _
  rw [← Category.assoc (eqToHom (congrArg S.part (Nat.zero_mul m).symm) ▷
    S.part (ℓ * m)) (S.mul (0 * m) (ℓ * m))]
  have hnat :
      (eqToHom (congrArg S.part (Nat.zero_mul m).symm) ▷ S.part (ℓ * m)) ≫
          S.mul (0 * m) (ℓ * m) =
        S.mul 0 (ℓ * m) ≫
          eqToHom (congrArg (fun n => S.part (n + ℓ * m)) (Nat.zero_mul m).symm) := by
    rw [MonoidalCategory.eqToHom_whiskerRight]
    rw [eqToHom_naturality (fun n => S.mul n (ℓ * m)) (Nat.zero_mul m).symm]
  rw [hnat]
  rw [← Category.assoc, ← Category.assoc]
  rw [S.one_mul]
  simp only [Category.assoc]
  rw [eqToHom_trans, eqToHom_trans]

/-- Associativity of the Veronese subalgebra, from `S.mul_assoc (ℓ * m) (ℓ' * m) (ℓ'' * m)`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseMul_assoc {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (ℓ ℓ' ℓ'' : ℕ) :
    (α_ (S.part (ℓ * m)) (S.part (ℓ' * m)) (S.part (ℓ'' * m))).hom ≫
        (S.part (ℓ * m) ◁ S.veroneseMul m ℓ' ℓ'') ≫ S.veroneseMul m ℓ (ℓ' + ℓ'') =
        (S.veroneseMul m ℓ ℓ' ▷ S.part (ℓ'' * m)) ≫ S.veroneseMul m (ℓ + ℓ') ℓ'' ≫
        eqToHom (congrArg (fun ℓ => S.part (ℓ * m)) (Nat.add_assoc ℓ ℓ' ℓ'')) := by
  simp only [AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseMul,
    MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [MonoidalCategory.whiskerLeft_comp]
  rw [MonoidalCategory.whiskerLeft_eqToHom]
  simp only [Category.assoc]
  rw [← eqToHom_naturality_assoc (fun n => S.mul (ℓ * m) n)
    (Nat.add_mul ℓ' ℓ'' m).symm]
  conv_lhs =>
    rw [← Category.assoc (S.part (ℓ * m) ◁ S.mul (ℓ' * m) (ℓ'' * m))
      (S.mul (ℓ * m) (ℓ' * m + ℓ'' * m)) _]
    rw [← Category.assoc (α_ (S.part (ℓ * m)) (S.part (ℓ' * m)) (S.part (ℓ'' * m))).hom
      ((S.part (ℓ * m) ◁ S.mul (ℓ' * m) (ℓ'' * m)) ≫
        S.mul (ℓ * m) (ℓ' * m + ℓ'' * m)) _]
    rw [S.mul_assoc (ℓ * m) (ℓ' * m) (ℓ'' * m)]
  conv_rhs =>
    rw [MonoidalCategory.eqToHom_whiskerRight]
    rw [← eqToHom_naturality_assoc (fun n => S.mul n (ℓ'' * m))
      (Nat.add_mul ℓ ℓ' m).symm]
  rw [eqToHom_trans, eqToHom_trans, eqToHom_trans]
  rw [Category.assoc]
  rw [Category.assoc (S.mul (ℓ * m + ℓ' * m) (ℓ'' * m)) _ _]
  rw [eqToHom_trans]

/-- Commutativity of the Veronese subalgebra, from `S.mul_comm (ℓ * m) (ℓ' * m)`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseMul_comm {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (ℓ ℓ' : ℕ) :
      (β_ (S.part (ℓ * m)) (S.part (ℓ' * m))).hom ≫ S.veroneseMul m ℓ' ℓ =
      S.veroneseMul m ℓ ℓ' ≫ eqToHom (congrArg (fun ℓ => S.part (ℓ * m)) (Nat.add_comm ℓ ℓ')) := by
  simp only [AlgebraicGeometry.Scheme.GradedQCAlgebra.veroneseMul,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  conv_lhs =>
    rw [← Category.assoc (β_ (S.part (ℓ * m)) (S.part (ℓ' * m))).hom
      (S.mul (ℓ' * m) (ℓ * m)) _]
    rw [S.mul_comm (ℓ * m) (ℓ' * m)]
  rw [Category.assoc (S.mul (ℓ * m) (ℓ' * m)) _ _]
  rw [eqToHom_trans]
  rw [eqToHom_trans]

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.veronese {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) : X.GradedQCAlgebra where
  part ℓ := S.part (ℓ * m)
  quasicoherent ℓ := S.quasicoherent (ℓ * m)
  mul ℓ ℓ' := S.veroneseMul m ℓ ℓ'
  one := S.veroneseOne m
  one_mul := S.veroneseMul_one_mul m
  mul_assoc := S.veroneseMul_assoc m
  mul_comm := S.veroneseMul_comm m

end
