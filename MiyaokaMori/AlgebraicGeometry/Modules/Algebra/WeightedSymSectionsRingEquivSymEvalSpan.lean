import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymSectionsRingEquivSymPure
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsHomBijectiveAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowSectionsAffine

/-! # Pure tensors span the sections of tensor powers and symmetric powers on an affine open

Helper module for `span_range_weightedTensorPure_eq_top` (`WeightedSymSectionsRingEquivSymEval.lean`). Notation:
`R := Γ(X, U)`, `P_e := monoidalPow F e = F^{⊗e}`.

* `Modules.secLin φ W`: the `Γ(X, W)`-linear map on sections induced by a morphism `φ`.
* `Modules.mem_span_image2_tsec`: for quasi-coherent `A, B` and affine `U`, `Γ(U, A ⊗ B)` is spanned by the
  `tsec a b` with `a`, `b` running through spanning sets of `Γ(U, A)`, `Γ(U, B)` (surjectivity half of Stacks 01I8,
  `tensorSectionsHom_app_bijective_of_isAffineOpen`, plus bilinearity of `tsec`).
* `Modules.monoidalPowPure U F e v`: the pure tensor `v_0 ⊗ ⋯ ⊗ v_{e-1} ∈ Γ(U, F^{⊗e})`, recursive along `monoidalPow`;
  `Modules.span_range_monoidalPowPure_eq_top`: these span `Γ(U, F^{⊗e})` for `F` quasi-coherent, `U` affine.
* `Modules.symPowπ_app_monoidalPowPure`: `π_e (v_0 ⊗ ⋯ ⊗ v_{e-1}) = gradedPure e v` in `symGradedAlgebraOfQC F hq`;
  `GradedQCAlgebra.span_range_gradedPure_eq_top`: the `gradedPure e v` span `Γ(U, Sym^e F)` (via the surjectivity of
  `π_e` on affine opens, `symPowπ_app_surjective_of_isAffineOpen`), stated
  for any `S = symGradedAlgebraOfQC F hq` and `g` heterogeneously equal to `(λ_ F).inv ≫ symPowπ F 1` (so that it applies
  to `symGradedAlgebra F` and `symGen F` through `symGradedAlgebra_of_isQuasicoherent` / `symGen_heq`).

Sources: Stacks 01CG, 01I8.
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

/-- The `Γ(X, W)`-linear map on sections induced by a morphism of sheaves of modules. -/
def secLin {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) : Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W) where
  toFun := (φ.app W).hom
  map_add' := (φ.app W).hom.map_add
  map_smul' := fun r a => AlgebraicGeometry.Scheme.Modules.Hom.app_smul φ r a

theorem secLin_apply {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (s : Γ(M, W)) :
    secLin φ W s = φ.app W s := rfl

/-- The pairing `Γ(U, A) ⊗_R Γ(U, B) → Γ(U, A ⊗ B)` as an `R`-linear map (`tensorSectionsHom` on `U`). -/
def tensorSectionsLin (A B : X.Modules) (U : X.Opens) :
    TensorProduct Γ(X, U) Γ(A, U) Γ(B, U) →ₗ[Γ(X, U)] Γ(A ⊗ B, U) :=
  ((AlgebraicGeometry.Scheme.Modules.tensorSectionsHom A B).app (op U)).hom

theorem tensorSectionsLin_tmul (A B : X.Modules) (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) :
    tensorSectionsLin A B U (TensorProduct.tmul _ a b) = tsec A B U a b :=
  tensorSectionsHom_app A B U a b

/-- Surjectivity half of `tensorSectionsHom_app_bijective_of_isAffineOpen`. -/
theorem tensorSectionsLin_surjective (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) : Function.Surjective (tensorSectionsLin A B U) :=
  (tensorSectionsHom_app_bijective_of_isAffineOpen A B hU).2

/-- Bilinearity of `tsec`: if `a` lies in the span of `sA` and `b` in the span of `sB`, then `tsec a b` lies in
the span of the `tsec a' b'` (`a' ∈ sA`, `b' ∈ sB`). -/
theorem tsec_mem_span_image2 (A B : X.Modules) {sA : Set Γ(A, U)} {sB : Set Γ(B, U)} {a : Γ(A, U)} {b : Γ(B, U)}
    (ha : a ∈ Submodule.span Γ(X, U) sA) (hb : b ∈ Submodule.span Γ(X, U) sB) :
    tsec A B U a b ∈ Submodule.span Γ(X, U) (Set.image2 (tsec A B U) sA sB) := by
  refine Submodule.span_induction (p := fun a _ => tsec A B U a b ∈
    Submodule.span Γ(X, U) (Set.image2 (tsec A B U) sA sB)) ?_ ?_ ?_ ?_ ha
  · intro a' ha'
    refine Submodule.span_induction (p := fun b _ => tsec A B U a' b ∈
      Submodule.span Γ(X, U) (Set.image2 (tsec A B U) sA sB)) ?_ ?_ ?_ ?_ hb
    · intro b' hb'
      exact Submodule.subset_span (Set.mem_image2_of_mem ha' hb')
    · have h0 : tsec A B U a' 0 = 0 := by
        have h := tsec_smul_right U A B 0 a' 0
        rwa [zero_smul, zero_smul] at h
      rw [h0]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [tsec_add_right]
      exact add_mem hx hy
    · intro c x _ hx
      rw [tsec_smul_right]
      exact Submodule.smul_mem _ c hx
  · have h0 : tsec A B U 0 b = 0 := by
      have h := tsec_smul_left U A B 0 0 b
      rwa [zero_smul, zero_smul] at h
    rw [h0]
    exact zero_mem _
  · intro x y _ _ hx hy
    rw [tsec_add_left]
    exact add_mem hx hy
  · intro c x _ hx
    rw [tsec_smul_left]
    exact Submodule.smul_mem _ c hx

/-- **Sections of `A ⊗ B` on an affine open are spanned by pure tensors of spanning sets** (Stacks 01I8, surjectivity of
`tensorSectionsHom` on affine opens, and `TensorProduct.induction_on`). -/
theorem mem_span_image2_tsec (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {sA : Set Γ(A, U)} {sB : Set Γ(B, U)}
    (hA : Submodule.span Γ(X, U) sA = ⊤) (hB : Submodule.span Γ(X, U) sB = ⊤) (x : Γ(A ⊗ B, U)) :
    x ∈ Submodule.span Γ(X, U) (Set.image2 (tsec A B U) sA sB) := by
  obtain ⟨t, rfl⟩ := tensorSectionsLin_surjective A B hU x
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | tmul a b =>
    rw [tensorSectionsLin_tmul]
    exact tsec_mem_span_image2 U A B (hA ▸ Submodule.mem_top) (hB ▸ Submodule.mem_top)
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂

/-- `Γ(U, 𝟙_) = Γ(U)` is spanned by the unit section. -/
theorem span_unitSec_eq_top : Submodule.span Γ(X, U) ({unitSec U} : Set Γ(𝟙_ X.Modules, U)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = (show Γ(X, U) from x) • unitSec U := (mul_one (show Γ(X, U) from x)).symm
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/-- **Pure tensors** `v_0 ⊗ ⋯ ⊗ v_{e-1} ∈ Γ(U, F^{⊗e})`, recursive along `monoidalPow` (`e = 0`: the unit section). -/
def monoidalPowPure (F : X.Modules) : (e : ℕ) → (Fin e → Γ(F, U)) →
    Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow F e, U)
  | 0, _ => unitSec U
  | e + 1, v => tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) F U (monoidalPowPure F e (Fin.init v))
      (v (Fin.last e))

theorem monoidalPowPure_zero (F : X.Modules) (v : Fin 0 → Γ(F, U)) : monoidalPowPure U F 0 v = unitSec U := rfl

theorem monoidalPowPure_succ (F : X.Modules) (e : ℕ) (v : Fin (e + 1) → Γ(F, U)) :
    monoidalPowPure U F (e + 1) v =
      tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) F U (monoidalPowPure U F e (Fin.init v))
        (v (Fin.last e)) := rfl

theorem monoidalPowPure_snoc (F : X.Modules) (e : ℕ) (v : Fin e → Γ(F, U)) (x : Γ(F, U)) :
    monoidalPowPure U F (e + 1) (Fin.snoc v x) =
      tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) F U (monoidalPowPure U F e v) x := by
  rw [monoidalPowPure_succ, Fin.init_snoc, Fin.snoc_last]

/-- **Pure tensors span `Γ(U, F^{⊗e})`** for `F` quasi-coherent and `U` affine (induction on `e` with
`mem_span_image2_tsec`). -/
theorem span_range_monoidalPowPure_eq_top (F : X.Modules) [F.IsQuasicoherent] (e : ℕ) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    Submodule.span Γ(X, U) (Set.range (monoidalPowPure U F e)) = ⊤ := by
  induction e with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have hx : x = (show Γ(X, U) from x) • monoidalPowPure U F 0 Fin.elim0 :=
      (mul_one (show Γ(X, U) from x)).symm
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.elim0, rfl⟩)
  | succ e ih =>
    have : (AlgebraicGeometry.Scheme.Modules.monoidalPow F e).IsQuasicoherent :=
      AlgebraicGeometry.Scheme.Modules.monoidalPow_isQuasicoherent F ‹_› e
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span Γ(X, U) (Set.image2 (tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) F U)
        (Set.range (monoidalPowPure U F e)) Set.univ) :=
      mem_span_image2_tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) F hU ih Submodule.span_univ x
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨v, rfl⟩, y, -, rfl⟩
    exact ⟨Fin.snoc v y, monoidalPowPure_snoc U F e v y⟩

/-! ## The symmetric-power quotient on pure tensors -/

/-- `(monoidalPowCat F e 1).hom = (α_ _ _ _).inv ≫ (ρ_ _).hom ▷ F` (definitional unfolding, spelled with `𝟙_ ⊗ F` for
`monoidalPow F 1`). -/
theorem monoidalPowCat_one_hom (F : X.Modules) (e : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPowCat F e 1).hom =
      (α_ (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) (𝟙_ X.Modules) F).inv ≫
        (ρ_ (AlgebraicGeometry.Scheme.Modules.monoidalPow F e)).hom ▷ F := rfl

/-- `monoidalPowCat F e 1` on sections: `a ⊗ (1 ⊗ x) ↦ a ⊗ x`. -/
theorem monoidalPowCat_one_hom_app_tsec (F : X.Modules) (e : ℕ)
    (a : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow F e, U)) (x : Γ(F, U)) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPowCat F e 1).hom.app U
        (tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) (𝟙_ X.Modules ⊗ F) U a
          (tsec (𝟙_ X.Modules) F U (unitSec U) x)) =
      tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) F U a x := by
  refine (congrArg (fun k : AlgebraicGeometry.Scheme.Modules.monoidalPow F e ⊗ (𝟙_ X.Modules ⊗ F) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow F e ⊗ F =>
      k.app U (tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) (𝟙_ X.Modules ⊗ F) U a
        (tsec (𝟙_ X.Modules) F U (unitSec U) x))) (monoidalPowCat_one_hom F e)).trans ?_
  refine (comp_app_apply_sec U _ _ _).trans ?_
  refine (congrArg _ (associator_inv_app_tsec U _ _ _ a (unitSec U) x)).trans ?_
  refine (whiskerRight_app_tsec U _ _ _ _).trans ?_
  exact congrArg (fun y => tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) F U y x)
    (rightUnitor_app_tsec_unitSec U _ a)

/-- **`π_e` on pure tensors is `gradedPure`** in `symGradedAlgebraOfQC F hq` (with the degree-one map
`(λ_ F).inv ≫ symPowπ F 1`): `π_e (v_0 ⊗ ⋯ ⊗ v_{e-1}) = gradedPure e v`. Induction on `e` with
`tensorHom_symPowπ_symPowMul` and `monoidalPowCat F e 1` on sections. -/
theorem symPowπ_app_monoidalPowPure (F : X.Modules) (hq : F.IsQuasicoherent) :
    ∀ (e : ℕ) (v : Fin e → Γ(F, U)),
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC F hq).gradedPure U
          ((λ_ F).inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ F 1) e v =
        (AlgebraicGeometry.Scheme.Modules.symPowπ F e).app U (monoidalPowPure U F e v)
  | 0, _ => rfl
  | e + 1, v => by
    have h1 := symPowπ_app_monoidalPowPure F hq e (Fin.init v)
    have h2 : ((λ_ F).inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ F 1).app U (v (Fin.last e)) =
        (AlgebraicGeometry.Scheme.Modules.symPowπ F 1).app U
          (tsec (𝟙_ X.Modules) F U (unitSec U) (v (Fin.last e))) :=
      (comp_app_apply_sec U (λ_ F).inv (AlgebraicGeometry.Scheme.Modules.symPowπ F 1) (v (Fin.last e))).trans
        (congrArg _ (leftUnitor_inv_app U F (v (Fin.last e))))
    refine (GradedQCAlgebra.gradedPure_succ U _ _ e v).trans ?_
    refine (congrArg₂ (fun (a : Γ(AlgebraicGeometry.Scheme.Modules.symPow F e, U))
        (b : Γ(AlgebraicGeometry.Scheme.Modules.symPow F 1, U)) =>
        (AlgebraicGeometry.Scheme.Modules.symPowMul F e 1).app U
          (tsec (AlgebraicGeometry.Scheme.Modules.symPow F e) (AlgebraicGeometry.Scheme.Modules.symPow F 1) U a b))
      h1 h2).trans ?_
    refine (congrArg _ (tensorHom_app_tsec U (AlgebraicGeometry.Scheme.Modules.symPowπ F e)
      (AlgebraicGeometry.Scheme.Modules.symPowπ F 1) (monoidalPowPure U F e (Fin.init v))
      (tsec (𝟙_ X.Modules) F U (unitSec U) (v (Fin.last e)))).symm).trans ?_
    refine (comp_app_apply_sec U _ _ _).symm.trans ?_
    refine (congrArg (fun k : AlgebraicGeometry.Scheme.Modules.monoidalPow F e ⊗
        AlgebraicGeometry.Scheme.Modules.monoidalPow F 1 ⟶ AlgebraicGeometry.Scheme.Modules.symPow F (e + 1) =>
        k.app U (tsec (AlgebraicGeometry.Scheme.Modules.monoidalPow F e) (𝟙_ X.Modules ⊗ F) U
          (monoidalPowPure U F e (Fin.init v)) (tsec (𝟙_ X.Modules) F U (unitSec U) (v (Fin.last e)))))
      (AlgebraicGeometry.Scheme.Modules.tensorHom_symPowπ_symPowMul F e 1)).trans ?_
    refine (comp_app_apply_sec U _ _ _).trans ?_
    exact congrArg _ (monoidalPowCat_one_hom_app_tsec U F e _ _)

end Modules

namespace GradedQCAlgebra

/-- **The `gradedPure e v` span `Γ(U, Sym^e F)`** for `F` quasi-coherent and `U` affine, for any graded algebra
`S = symGradedAlgebraOfQC F hq` with degree-one map `g` (heterogeneously) equal to `(λ_ F).inv ≫ symPowπ F 1`
(so it applies to `symGradedAlgebra F`, `symGen F` through `symGradedAlgebra_of_isQuasicoherent`, `symGen_heq`).
Proof: `gradedPure e v = π_e (pure tensor)` (`symPowπ_app_monoidalPowPure`), the pure tensors span `Γ(U, F^{⊗e})`
(`span_range_monoidalPowPure_eq_top`) and `π_e` is surjective on `U` (`symPowπ_app_surjective_of_isAffineOpen`). -/
theorem span_range_gradedPure_eq_top (F : X.Modules) (hq : F.IsQuasicoherent) {S : X.GradedQCAlgebra}
    (hS : S = AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC F hq) {g : F ⟶ S.part 1}
    (hg : HEq g ((λ_ F).inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ F 1)) (e : ℕ) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    Submodule.span Γ(X, U) (Set.range (S.gradedPure U g e)) = ⊤ := by
  subst hS
  have hg' : g = (λ_ F).inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ F 1 := eq_of_heq hg
  have := hq
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := AlgebraicGeometry.Scheme.Modules.symPowπ_app_surjective_of_isAffineOpen F e hU x
  have hy : y ∈ Submodule.span Γ(X, U) (Set.range (Modules.monoidalPowPure U F e)) := by
    rw [Modules.span_range_monoidalPowPure_eq_top F e hU]
    exact Submodule.mem_top
  have hmem : Modules.secLin (AlgebraicGeometry.Scheme.Modules.symPowπ F e) U y ∈ Submodule.span Γ(X, U)
      (Set.range ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC F hq).gradedPure U g e)) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨v, rfl⟩
      refine Submodule.subset_span ⟨v, ?_⟩
      rw [hg']
      exact Modules.symPowπ_app_monoidalPowPure U F hq e v
    · rw [map_zero]
      exact zero_mem _
    · intro a b _ _ ha hb
      rw [map_add]
      exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]
      exact Submodule.smul_mem _ c ha
  exact hmem

end GradedQCAlgebra

end AlgebraicGeometry.Scheme

end
