import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymSectionsRingEquivSymEvalSpan

/-! # Linear maps out of the sections of tensor powers and symmetric powers, prescribed on pure tensors

Helper module for `exists_linearMap_weightedTensorPure` (`WeightedSymSectionsRingEquivSymEval.lean`). Notation:
`R := Γ(X, U)`, `P_e := monoidalPow F e = F^{⊗e}`.

* `Modules.exists_linearMap_tsec`: for quasi-coherent `A, B` and affine `U`, an `R`-bilinear map
  `Γ(U, A) × Γ(U, B) → C` extends to an `R`-linear map `Γ(U, A ⊗ B) → C` through the `tsec` pairing (Stacks 01I8:
  bijectivity of `tensorSectionsHom` on affine opens, `tensorSectionsHom_app_bijective_of_isAffineOpen`, and
  `TensorProduct.lift`).
* `Modules.exists_linearMap_monoidalPowPure`: an `R`-linear `g : Γ(U, F) → C` (`C` a commutative `R`-algebra) induces
  `ψ_e : Γ(U, F^{⊗e}) → C` with `ψ_e (v_0 ⊗ ⋯ ⊗ v_{e-1}) = ∏ g (v_i)` (induction on `e`).
* `Modules.exists_monoidalPowTransp_app_monoidalPowPure`: an adjacent transposition sends a pure tensor to a pure tensor
  whose factors are a rearrangement (same product of any commutative-monoid-valued function of the factors).
* `Modules.exists_linearMap_factor_of_surjective`: a linear map vanishing on the kernel of a surjection factors.
* `GradedQCAlgebra.exists_linearMap_gradedPure`: `ψ₀ : Γ(U, Sym^e F) → C` with `ψ₀ (gradedPure e v) = ∏ g (v_i)`,
  via the kernel description `symPowπ_app_eq_zero_iff_of_isAffineOpen`
  and the surjectivity of `π_e`; stated for `S = symGradedAlgebraOfQC F hq` and `g` heterogeneously equal to
  `(λ_ F).inv ≫ symPowπ F 1` (so it applies to `symGradedAlgebra F`, `symGen F`).

Sources: Stacks 01CG, 01I8; Bourbaki Algebra III §6 (universal property of `Sym`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)

namespace Modules

/-- **Bilinear maps on sections extend along `tsec`** (Stacks 01I8 on affine opens + `TensorProduct.lift`). -/
theorem exists_linearMap_tsec (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {C : Type*} [AddCommMonoid C] [Module Γ(X, U) C]
    (β : Γ(A, U) →ₗ[Γ(X, U)] Γ(B, U) →ₗ[Γ(X, U)] C) :
    ∃ ψ : Γ(A ⊗ B, U) →ₗ[Γ(X, U)] C, ∀ a b, ψ (tsec A B U a b) = β a b := by
  let e := LinearEquiv.ofBijective (tensorSectionsLin A B U)
    (tensorSectionsHom_app_bijective_of_isAffineOpen A B hU)
  refine ⟨(TensorProduct.lift β).comp e.symm.toLinearMap, fun a b => ?_⟩
  have h : e.symm (tsec A B U a b) = TensorProduct.tmul _ a b :=
    e.symm_apply_eq.mpr (tensorSectionsLin_tmul A B U a b).symm
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, TensorProduct.lift.tmul]

/-- `Γ(U, 𝟙_) = Γ(U)` as an `R`-linear map (the identity). -/
def unitSecLin (U : X.Opens) : Γ(𝟙_ X.Modules, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun := fun x => (show Γ(X, U) from x)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem unitSecLin_unitSec (U : X.Opens) : unitSecLin U (unitSec U) = 1 := rfl

/-- **Linear maps on `Γ(U, F^{⊗e})` prescribed on pure tensors**: `ψ_e (v_0 ⊗ ⋯ ⊗ v_{e-1}) = ∏ g (v_i)`
(`e = 0`: `algebraMap`; `e + 1`: `exists_linearMap_tsec` for `(x, v) ↦ ψ_e x * g v`). -/
theorem exists_linearMap_monoidalPowPure (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {C : Type*} [CommRing C] [Algebra Γ(X, U) C]
    (g : Γ(F, U) →ₗ[Γ(X, U)] C) : ∀ e : ℕ,
    ∃ ψ : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow F e, U) →ₗ[Γ(X, U)] C,
      ∀ v, ψ (monoidalPowPure U F e v) = ∏ i, g (v i)
  | 0 =>
    ⟨(Algebra.linearMap Γ(X, U) C).comp (unitSecLin U), fun v => by
      rw [Fin.prod_univ_zero]
      exact map_one (algebraMap Γ(X, U) C)⟩
  | e + 1 => by
    obtain ⟨ψ, hψ⟩ := exists_linearMap_monoidalPowPure F hU g e
    have : (AlgebraicGeometry.Scheme.Modules.monoidalPow F e).IsQuasicoherent :=
      AlgebraicGeometry.Scheme.Modules.monoidalPow_isQuasicoherent F ‹_› e
    obtain ⟨Ψ, hΨ⟩ := exists_linearMap_tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) F hU
      ((LinearMap.mul Γ(X, U) C).compl₁₂ ψ g)
    refine ⟨Ψ, fun v => (hΨ (monoidalPowPure U F e (Fin.init v)) (v (Fin.last e))).trans ?_⟩
    rw [LinearMap.compl₁₂_apply, LinearMap.mul_apply', hψ, Fin.prod_univ_castSucc]
    rfl

theorem monoidalPowTransp_succ_succ_eq (F : X.Modules) (n j : ℕ) :
    AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F (n + 1) (j + 1) =
      AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F n j ▷ F := by
  cases n <;> rfl

theorem monoidalPowTransp_zero (F : X.Modules) (j : ℕ) :
    AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F 0 j = 𝟙 _ := rfl

theorem monoidalPowTransp_one_zero (F : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F 1 0 = 𝟙 _ := rfl

theorem monoidalPowTransp_two_zero (F : X.Modules) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F (n + 2) 0 =
      (α_ (AlgebraicGeometry.Scheme.Modules.monoidalPow F n) F F).hom ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPow F n ◁ (β_ F F).hom) ≫
        (α_ (AlgebraicGeometry.Scheme.Modules.monoidalPow F n) F F).inv := rfl

/-- The product of `f` over a `snoc` family. -/
theorem prod_comp_snoc {M α : Type*} [CommMonoid M] {n : ℕ} (f : α → M) (p : Fin n → α) (x : α) :
    ∏ j, f (Fin.snoc (α := fun _ => α) p x j) = (∏ j, f (p j)) * f x := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- `(α_).hom ≫ (_ ◁ β_) ≫ (α_).inv` swaps the last two factors of a pure section (variable level). -/
theorem swapLast_app_tsec (A B : X.Modules) (a : Γ(A, U)) (b c : Γ(B, U)) :
    ((α_ A B B).hom ≫ (A ◁ (β_ B B).hom) ≫ (α_ A B B).inv).app U (tsec (A ⊗ B) B U (tsec A B U a b) c) =
      tsec (A ⊗ B) B U (tsec A B U a c) b := by
  rw [comp_app_apply_sec, comp_app_apply_sec, associator_app_tsec, whiskerLeft_app_tsec, braiding_app_tsec,
    associator_inv_app_tsec]

/-- **Adjacent transpositions permute the factors of a pure tensor**: `transp_i (v_0 ⊗ ⋯ ⊗ v_{e-1})` is a pure tensor
`w_0 ⊗ ⋯ ⊗ w_{e-1}` whose factors are a rearrangement of the `v_i` (so that `∏ f (w_i) = ∏ f (v_i)` for any
`f` into a commutative monoid). Follows the recursion of `monoidalPowTransp`: `transp (n+2) 0` is
`(α_).hom ≫ (_ ◁ β_) ≫ (α_).inv` (swap of the last two factors, `associator_app_tsec`, `braiding_app_tsec`);
`transp (n+1) (i+1) = transp n i ▷ F` (induction); out of range it is the identity. -/
theorem exists_monoidalPowTransp_app_monoidalPowPure (F : X.Modules) :
    ∀ (e i : ℕ) (v : Fin e → Γ(F, U)), ∃ w : Fin e → Γ(F, U),
      (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F e i).app U (monoidalPowPure U F e v) =
        monoidalPowPure U F e w ∧
      ∀ {M : Type*} [CommMonoid M] (f : Γ(F, U) → M), ∏ j, f (w j) = ∏ j, f (v j)
  | 0, _, v => ⟨v, by rw [monoidalPowTransp_zero, Hom.id_app]; rfl, fun _ => rfl⟩
  | 1, 0, v => ⟨v, by rw [monoidalPowTransp_one_zero, Hom.id_app]; rfl, fun _ => rfl⟩
  | n + 2, 0, v => by
    refine ⟨Fin.snoc (Fin.snoc (Fin.init (Fin.init v)) (v (Fin.last (n + 1)))) (Fin.init v (Fin.last n)), ?_, ?_⟩
    · have hR : monoidalPowPure U F (n + 2)
          (Fin.snoc (Fin.snoc (Fin.init (Fin.init v)) (v (Fin.last (n + 1)))) (Fin.init v (Fin.last n))) =
          tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F n ⊗ F) F U
            (tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F n) F U (monoidalPowPure U F n (Fin.init (Fin.init v)))
              (v (Fin.last (n + 1)))) (Fin.init v (Fin.last n)) :=
        (monoidalPowPure_snoc U F (n + 1) _ _).trans
          (congrArg (fun y => tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F (n + 1)) F U y
            (Fin.init v (Fin.last n))) (monoidalPowPure_snoc U F n _ _))
      refine Eq.trans ?_ hR.symm
      exact swapLast_app_tsec U (AlgebraicGeometry.Scheme.Modules.monoidalPow F n) F
        (monoidalPowPure U F n (Fin.init (Fin.init v))) (Fin.init v (Fin.last n)) (v (Fin.last (n + 1)))
    · intro M _ f
      rw [prod_comp_snoc, prod_comp_snoc, Fin.prod_univ_castSucc (fun j => f (v j)),
        Fin.prod_univ_castSucc (fun j : Fin (n + 1) => f (v (Fin.castSucc j)))]
      exact mul_right_comm _ _ _
  | n + 1, i + 1, v => by
    obtain ⟨w, hw, hprod⟩ := exists_monoidalPowTransp_app_monoidalPowPure F n i (Fin.init v)
    refine ⟨Fin.snoc w (v (Fin.last n)), ?_, ?_⟩
    · refine Eq.trans ?_ (monoidalPowPure_snoc U F n w (v (Fin.last n))).symm
      refine (congrArg (fun k : AlgebraicGeometry.Scheme.Modules.monoidalPow F n ⊗ F ⟶
          AlgebraicGeometry.Scheme.Modules.monoidalPow F n ⊗ F =>
          k.app U (tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F n) F U (monoidalPowPure U F n (Fin.init v))
            (v (Fin.last n)))) (monoidalPowTransp_succ_succ_eq F n i)).trans ?_
      refine (whiskerRight_app_tsec U _ F _ _).trans ?_
      exact congrArg (fun y => tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F n) F U y (v (Fin.last n))) hw
    · intro M _ f
      rw [prod_comp_snoc, Fin.prod_univ_castSucc (fun j => f (v j))]
      exact congrArg (· * f (v (Fin.last n))) (hprod f)

/-- **A linear map vanishing on the kernel of a surjection factors through it** (`Submodule.liftQ` and
`LinearMap.quotKerEquivOfSurjective`). -/
theorem exists_linearMap_factor_of_surjective {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (ψ : M →ₗ[R] P) (h : ∀ x, f x = 0 → ψ x = 0) : ∃ ψ₀ : N →ₗ[R] P, ∀ x, ψ₀ (f x) = ψ x := by
  have hle : LinearMap.ker f ≤ LinearMap.ker ψ := fun x hx => LinearMap.mem_ker.mpr (h x (LinearMap.mem_ker.mp hx))
  refine ⟨((LinearMap.ker f).liftQ ψ hle).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap, fun x => ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.liftQ_apply]

end Modules

namespace GradedQCAlgebra

/-- **Linear maps on `Γ(U, Sym^e F)` prescribed on `gradedPure`**: for `F` quasi-coherent, `U` affine, `C` a
commutative `R`-algebra and `g' : Γ(U, F) →ₗ[R] C`, there is `ψ₀ : Γ(U, S.part e) →ₗ[R] C` with
`ψ₀ (gradedPure e v) = ∏ g' (v_i)`, for `S = symGradedAlgebraOfQC F hq` and `g` heterogeneously equal to
`(λ_ F).inv ≫ symPowπ F 1`.

Proof: `ψ_e : Γ(U, F^{⊗e}) → C` from `exists_linearMap_monoidalPowPure`; it is invariant under every adjacent
transposition (checked on the spanning pure tensors, `exists_monoidalPowTransp_app_monoidalPowPure`,
`span_range_monoidalPowPure_eq_top`), hence kills the kernel of `π_e` on `U`, the span of the `transp_i x - x`
(`symPowπ_app_eq_zero_iff_of_isAffineOpen`); `π_e` is surjective on `U` (`symPowπ_app_surjective_of_isAffineOpen`), so
`ψ_e` descends (`exists_linearMap_factor_of_surjective`), and `gradedPure e v = π_e (pure tensor)`
(`symPowπ_app_monoidalPowPure`). -/
theorem exists_linearMap_gradedPure (F : X.Modules) (hq : F.IsQuasicoherent) {S : X.GradedQCAlgebra}
    (hS : S = AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC F hq) {g : F ⟶ S.part 1}
    (hg : HEq g ((λ_ F).inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ F 1)) (e : ℕ) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {C : Type*} [CommRing C] [Algebra Γ(X, U) C]
    (g' : Γ(F, U) →ₗ[Γ(X, U)] C) :
    ∃ ψ : Γ(S.part e, U) →ₗ[Γ(X, U)] C, ∀ v, ψ (S.gradedPure U g e v) = ∏ i, g' (v i) := by
  subst hS
  have hg' : g = (λ_ F).inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ F 1 := eq_of_heq hg
  have := hq
  obtain ⟨ψ, hψ⟩ := Modules.exists_linearMap_monoidalPowPure F hU g' e
  have hinv : ∀ (i : Fin e) (x : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow F e, U)),
      ψ ((AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F e i).app U x) = ψ x := by
    intro i
    have hext : ψ.comp (Modules.secLin (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F e i) U) = ψ := by
      refine LinearMap.ext_on_range (Modules.span_range_monoidalPowPure_eq_top F e hU) fun v => ?_
      obtain ⟨w, hw, hprod⟩ := Modules.exists_monoidalPowTransp_app_monoidalPowPure U F e i v
      rw [LinearMap.comp_apply, Modules.secLin_apply, hw, hψ, hψ]
      exact hprod g'
    intro x
    exact LinearMap.congr_fun hext x
  have hker : ∀ y, (AlgebraicGeometry.Scheme.Modules.symPowπ F e).app U y = 0 → ψ y = 0 := by
    intro y hy
    rw [AlgebraicGeometry.Scheme.Modules.symPowπ_app_eq_zero_iff_of_isAffineOpen F e hU] at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨⟨i, x⟩, rfl⟩
      show ψ ((AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F e i).app U x - x) = 0
      rw [map_sub, hinv i x, sub_self]
    · exact map_zero ψ
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_zero]
    · intro c a _ ha
      rw [map_smul, ha, smul_zero]
  obtain ⟨ψ₀, hψ₀⟩ := Modules.exists_linearMap_factor_of_surjective
    (Modules.secLin (AlgebraicGeometry.Scheme.Modules.symPowπ F e) U)
    (AlgebraicGeometry.Scheme.Modules.symPowπ_app_surjective_of_isAffineOpen F e hU) ψ hker
  refine ⟨ψ₀, fun v => ?_⟩
  have h1 : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC F hq).gradedPure U g e v =
      (AlgebraicGeometry.Scheme.Modules.symPowπ F e).app U (Modules.monoidalPowPure U F e v) := by
    rw [hg']
    exact Modules.symPowπ_app_monoidalPowPure U F hq e v
  exact (congrArg ψ₀ h1).trans ((hψ₀ _).trans (hψ v))

end GradedQCAlgebra

end AlgebraicGeometry.Scheme

end
