import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraCongr
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.CategoryTheory.GradedMonoidMultiplicativeFamily

/-! # The universal property of `Sym(W)` with a weight

Given a graded QC algebra `T`, a quasi-coherent module `W` and `g : W ⟶ T_n`, the `d`-fold product
`powProd g d : W^{⊗d} ⟶ T_{n d}` (recursive, `T.one` for `d = 0`) is invariant under the adjacent transpositions
`monoidalPowTransp` (commutativity + associativity of `T`: `braiding_last_two_comp_gmul`), hence descends along
`symPowπ W d` to `symLiftOfQC g d : Sym^d W ⟶ T_{n d}` (`symPowDesc`). The family is multiplicative for `symPowMul`
(cancel the epimorphism `π_a ⊗ π_b`, `symPowπ_tensorHom_cancel`, and use `monoidalPowCat_comp_powProd`, an induction
on `b`) and unital, i.e. `IsGradedMonoidHom` from `symGradedAlgebraOfQC W hW` to `T` along `d ↦ n * d`
(`symLiftOfQC_isGradedMonoidHom`). Transporting along `symGradedAlgebra W = symGradedAlgebraOfQC W hW` gives the same
for `symGradedAlgebra W` (`symLift`, `symLift_isGradedMonoidHom`), and `symGen W ≫ symLift g 1 = g`
(`symGen_comp_symLift`).

Source: Bourbaki, Algebra III §6 no. 1 Prop. 2 (universal property of the symmetric algebra: a linear map `W → A`
into a commutative algebra extends uniquely to `Sym(W) → A`); here the weighted version `Sym^d W → A_{nd}` for a
graded target, at the level of sheaves via the presentation `Sym^d W = coeq(transpositions on W^{⊗d})`
(`SheafSymmetricAlgebra.lean`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (T : X.GradedQCAlgebra) {W : X.Modules} {n : ℕ}

/-- The `d`-fold product `W^{⊗d} ⟶ T_{n d}` of `g : W ⟶ T_n` (`T.one` for `d = 0`). -/
def powProd (g : W ⟶ T.part n) : (d : ℕ) → (monoidalPow W d ⟶ T.part (n * d))
  | 0 => T.one ≫ eqToHom (congrArg T.part (Nat.mul_zero n).symm)
  | d + 1 => (powProd g d ⊗ₘ g) ≫ MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n d).symm

theorem powProd_zero (g : W ⟶ T.part n) :
    powProd T g 0 = T.one ≫ eqToHom (congrArg T.part (Nat.mul_zero n).symm) := rfl

theorem powProd_succ (g : W ⟶ T.part n) (d : ℕ) :
    powProd T g (d + 1) = (powProd T g d ⊗ₘ g) ≫ MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n d).symm := rfl

/-- The product is invariant under the adjacent transpositions of `W^{⊗d}` (commutativity of `T`). -/
theorem monoidalPowTransp_comp_powProd (g : W ⟶ T.part n) :
    ∀ (d i : ℕ), monoidalPowTransp W d i ≫ powProd T g d = powProd T g d
  | 0, _ => by
    rw [show monoidalPowTransp W 0 _ = 𝟙 _ from rfl, Category.id_comp]
  | 1, 0 => by
    rw [show monoidalPowTransp W 1 0 = 𝟙 _ from rfl, Category.id_comp]
  | d + 2, 0 => by
    show ((α_ (monoidalPow W d) W W).hom ≫ (monoidalPow W d ◁ (β_ W W).hom) ≫
        (α_ (monoidalPow W d) W W).inv) ≫
        (((powProd T g d ⊗ₘ g) ≫ MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n d).symm) ⊗ₘ g) ≫
          MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n (d + 1)).symm =
      (((powProd T g d ⊗ₘ g) ≫ MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n d).symm) ⊗ₘ g) ≫
        MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n (d + 1)).symm
    simp only [Category.assoc]
    exact T.isGradedMonoid.braiding_last_two_comp_gmul _ _ _ _
  | d + 1, i + 1 => by
    rw [show monoidalPowTransp W (d + 1) (i + 1) = monoidalPowTransp W d i ▷ W by cases d <;> rfl]
    show (monoidalPowTransp W d i ▷ W) ≫
        (powProd T g d ⊗ₘ g) ≫ MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n d).symm =
      (powProd T g d ⊗ₘ g) ≫ MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n d).symm
    rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
      monoidalPowTransp_comp_powProd g d i]

/-- The descent of the product to `Sym^d W ⟶ T_{n d}`. -/
def symLiftOfQC (g : W ⟶ T.part n) (d : ℕ) : symPow W d ⟶ T.part (n * d) :=
  symPowDesc W d (powProd T g d) (fun i => monoidalPowTransp_comp_powProd T g d i)

theorem symPowπ_comp_symLiftOfQC (g : W ⟶ T.part n) (d : ℕ) :
    symPowπ W d ≫ symLiftOfQC T g d = powProd T g d :=
  symPowπ_desc _ _ _ _

/-- The product is multiplicative along the concatenation `W^{⊗a} ⊗ W^{⊗b} ≅ W^{⊗(a+b)}`. -/
theorem monoidalPowCat_comp_powProd (g : W ⟶ T.part n) (a : ℕ) :
    ∀ b : ℕ, (monoidalPowCat W a b).hom ≫ powProd T g (a + b) =
      (powProd T g a ⊗ₘ powProd T g b) ≫ MiyaokaMori.gmul T.part T.mul (Nat.mul_add n a b).symm
  | 0 => by
    show (ρ_ (monoidalPow W a)).hom ≫ powProd T g a =
      (powProd T g a ⊗ₘ (T.one ≫ eqToHom (congrArg T.part (Nat.mul_zero n).symm))) ≫
        MiyaokaMori.gmul T.part T.mul (Nat.mul_add n a 0).symm
    rw [tensorHom_def, Category.assoc, whiskerLeft_comp, Category.assoc,
      MiyaokaMori.whiskerLeft_eqToHom_comp_gmul T.part T.mul (Nat.mul_zero n).symm,
      T.isGradedMonoid.gmul_mul_one _ rfl, eqToHom_refl, Category.comp_id]
    exact (rightUnitor_naturality _).symm
  | b + 1 => by
    rw [show (monoidalPowCat W a (b + 1)).hom = (α_ (monoidalPow W a) (monoidalPow W b) W).inv ≫
      ((monoidalPowCat W a b).hom ▷ W) from rfl]
    show _ ≫ ((monoidalPowCat W a b).hom ▷ W) ≫ (powProd T g (a + b) ⊗ₘ g) ≫
        MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n (a + b)).symm =
      (powProd T g a ⊗ₘ ((powProd T g b ⊗ₘ g) ≫ MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n b).symm)) ≫
        MiyaokaMori.gmul T.part T.mul (Nat.mul_add n a (b + 1)).symm
    rw [← Category.assoc ((monoidalPowCat W a b).hom ▷ W), ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.id_comp, monoidalPowCat_comp_powProd g a b,
      T.isGradedMonoid.tensorHom_gmul_tensorHom_comp_gmul _ _ _ _ _ (Nat.mul_succ n b).symm
        (by simp only [Nat.succ_eq_add_one]; ring), Iso.inv_hom_id_assoc]

/-- `symLiftOfQC g` is a graded monoid homomorphism `symGradedAlgebraOfQC W hW ⟶ T` along `d ↦ n * d`. -/
theorem symLiftOfQC_isGradedMonoidHom (hW : W.IsQuasicoherent) (g : W ⟶ T.part n) :
    MiyaokaMori.IsGradedMonoidHom (symGradedAlgebraOfQC W hW).part (symGradedAlgebraOfQC W hW).mul
      (symGradedAlgebraOfQC W hW).one T.part T.mul T.one (fun d => n * d) (Nat.mul_add n) (Nat.mul_zero n)
      (symLiftOfQC T g) where
  map_mul a b := by
    apply symPowπ_tensorHom_cancel
    show (symPowπ W a ⊗ₘ symPowπ W b) ≫ symPowMul W a b ≫ symLiftOfQC T g (a + b) =
      (symPowπ W a ⊗ₘ symPowπ W b) ≫ (symLiftOfQC T g a ⊗ₘ symLiftOfQC T g b) ≫
        MiyaokaMori.gmul T.part T.mul (Nat.mul_add n a b).symm
    rw [tensorHom_symPowπ_symPowMul_assoc, symPowπ_comp_symLiftOfQC, ← Category.assoc,
      tensorHom_comp_tensorHom, symPowπ_comp_symLiftOfQC, symPowπ_comp_symLiftOfQC,
      monoidalPowCat_comp_powProd]
  map_one := symPowπ_comp_symLiftOfQC T g 0

/-- Transport of `IsGradedMonoidHom` along an equality of graded QC algebras. -/
theorem isGradedMonoidHom_of_eq {S S' : X.GradedQCAlgebra} (h : S = S') {w : ℕ → ℕ}
    {hw : ∀ a b, w (a + b) = w a + w b} {hw0 : w 0 = 0} {Ψ' : ∀ d, S'.part d ⟶ T.part (w d)}
    (hΨ : MiyaokaMori.IsGradedMonoidHom S'.part S'.mul S'.one T.part T.mul T.one w hw hw0 Ψ') :
    MiyaokaMori.IsGradedMonoidHom S.part S.mul S.one T.part T.mul T.one w hw hw0
      (fun d => eqToHom (congrArg (fun S : X.GradedQCAlgebra => S.part d) h) ≫ Ψ' d) := by
  subst h
  simpa using hΨ

/-- `(symGradedAlgebra W).part d = Sym^d W` for quasi-coherent `W`. -/
theorem symGradedAlgebra_part_eq_symPow_of_isQuasicoherent (hW : W.IsQuasicoherent) (d : ℕ) :
    (symGradedAlgebra W).part d = symPow W d := by
  rw [symGradedAlgebra_eq_ofQC W hW]; rfl

/-- The lift `Sym^d W = (symGradedAlgebra W).part d ⟶ T_{n d}` for quasi-coherent `W`. -/
def symLift (hW : W.IsQuasicoherent) (g : W ⟶ T.part n) (d : ℕ) :
    (symGradedAlgebra W).part d ⟶ T.part (n * d) :=
  eqToHom (symGradedAlgebra_part_eq_symPow_of_isQuasicoherent hW d) ≫ symLiftOfQC T g d

theorem symLift_isGradedMonoidHom (hW : W.IsQuasicoherent) (g : W ⟶ T.part n) :
    MiyaokaMori.IsGradedMonoidHom (symGradedAlgebra W).part (symGradedAlgebra W).mul (symGradedAlgebra W).one
      T.part T.mul T.one (fun d => n * d) (Nat.mul_add n) (Nat.mul_zero n) (symLift T hW g) := by
  exact isGradedMonoidHom_of_eq T (symGradedAlgebra_eq_ofQC W hW) (symLiftOfQC_isGradedMonoidHom T hW g)

/-- The lift sends the generator `symGen W : W ⟶ Sym^1 W` to `g`. -/
theorem symGen_comp_symLift (hW : W.IsQuasicoherent) (g : W ⟶ T.part n) :
    symGen W ≫ symLift T hW g 1 = g ≫ eqToHom (congrArg T.part (Nat.mul_one n).symm) := by
  have p : symPow W 1 = (symGradedAlgebra W).part 1 := (symGradedAlgebra_part_eq_symPow_of_isQuasicoherent hW 1).symm
  have hs : symGen W = (λ_ W).inv ≫ symPowπ W 1 ≫ eqToHom p := by
    rw [symGen, dif_pos hW]
  have e : eqToHom p ≫ eqToHom (symGradedAlgebra_part_eq_symPow_of_isQuasicoherent hW 1) = 𝟙 (symPow W 1) := by
    rw [eqToHom_trans, eqToHom_refl]
  have k : (symPowπ W 1 ≫ eqToHom p) ≫ (eqToHom (symGradedAlgebra_part_eq_symPow_of_isQuasicoherent hW 1) ≫ symLiftOfQC T g 1) =
      powProd T g 1 := by
    rw [Category.assoc, ← Category.assoc (eqToHom p), e, Category.id_comp, symPowπ_comp_symLiftOfQC]
  rw [hs, symLift]
  refine (congrArg (fun x : monoidalPow W 1 ⟶ T.part (n * 1) => (λ_ W).inv ≫ x) k).trans ?_
  show (λ_ W).inv ≫ ((T.one ≫ eqToHom (congrArg T.part (Nat.mul_zero n).symm)) ⊗ₘ g) ≫
      MiyaokaMori.gmul T.part T.mul (Nat.mul_succ n 0).symm = g ≫ eqToHom (congrArg T.part (Nat.mul_one n).symm)
  rw [tensorHom_def', Category.assoc, comp_whiskerRight, Category.assoc,
    MiyaokaMori.eqToHom_whiskerRight_comp_gmul T.part T.mul (Nat.mul_zero n).symm,
    T.isGradedMonoid.gmul_one_mul _ (Nat.mul_one n).symm, leftUnitor_naturality_assoc, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules

end
