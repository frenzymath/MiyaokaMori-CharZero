import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra

/-! # Nilpotence of the positive-weight part of the truncated jet algebra

The positive-weight part of the truncated jet algebra `𝒜 = ⊕_{q ≤ κ} L^{-q}` is nilpotent on
sections: if `a ∈ 𝒜(V)` has weight-`0` component `0`, then `a^{κ+1} = 0`.

Source: §3 of the paper (`C̃_(κ)(L) = Spec_{C̃} ⊕_{q≤κ} L^{-q}`): the
multiplication of `𝒜` is graded and truncated (`truncatedJetAlgebra.mulHom`: the product of the
`a`-th and `b`-th pieces lands in the `(a+b)`-th piece and is `0` when `a + b > κ`), so a product of
`κ+1` sections of weight `≥ 1` has weight `≥ κ+1 > κ`, i.e. vanishes.

This is the algebraic half of the surjectivity of the zero section (`JetNeighborhoodZeroSectionSurjective`)
and of the unit criterion (`JetNeighborhoodUnitOfZeroSectionOne`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- A finite sum of morphisms of `𝒪ₓ`-modules acts on a section as the sum of the actions. -/
theorem AlgebraicGeometry.Scheme.Modules.Hom.sum_app_apply {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (U : X.Opens) (x : Γ(M, U)) :
    (∑ i ∈ s, f i).app U x = ∑ i ∈ s, (f i).app U x := by
  let F : (M ⟶ N) →+ Γ(N, U) :=
    { toFun := fun φ => φ.app U x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum F f s

/-- Composition acts on sections by composition of the actions (by definition). -/
theorem AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply' {X : AlgebraicGeometry.Scheme.{u}}
    {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (f ≫ g).app U x = g.app U (f.app U x) := rfl

/-- `ι_i ≫ π_s = 0` for `i ≠ s`, on sections. -/
theorem AlgebraicGeometry.Scheme.Modules.biproduct_ι_π_ne_app_apply {X : AlgebraicGeometry.Scheme.{u}}
    {J : Type} [Fintype J] [DecidableEq J] (f : J → X.Modules) {i s : J} (hne : i ≠ s)
    (U : X.Opens) (y : Γ(f i, U)) :
    (CategoryTheory.Limits.biproduct.ι f i ≫ CategoryTheory.Limits.biproduct.π f s).app U y = 0 := by
  rw [CategoryTheory.Limits.biproduct.ι_π_ne _ hne]
  rfl

namespace truncatedJetAlgebra

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ)

/-- A section of `𝒜(V) = ⊕_{q ≤ κ} L^{-q}(V)` has weight `≥ m` if all its components of weight
`< m` vanish. -/
def WeightGE (V : Ct.toScheme.Opens) (m : ℕ) (a : Γ(truncatedJetAlgebra.obj L κ, V)) : Prop :=
  ∀ q : Fin (κ + 1), q.val < m →
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V a = 0

theorem WeightGE.congr {V : Ct.toScheme.Opens} {m : ℕ} {a b : Γ(truncatedJetAlgebra.obj L κ, V)}
    (e : a = b) (h : WeightGE L κ V m a) : WeightGE L κ V m b := e ▸ h

/-- A section of weight `≥ κ + 1` is zero (all its components vanish; `biproduct.total`). -/
theorem eq_zero_of_weightGE (V : Ct.toScheme.Opens) (a : Γ(truncatedJetAlgebra.obj L κ, V))
    (h : WeightGE L κ V (κ + 1) a) : a = 0 := by
  have h1 : (∑ q : Fin (κ + 1),
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q ≫
        CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V a
      = a := by
    rw [CategoryTheory.Limits.biproduct.total]
    rfl
  rw [AlgebraicGeometry.Scheme.Modules.Hom.sum_app_apply] at h1
  refine h1.symm.trans (Finset.sum_eq_zero (fun q _ => ?_))
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply', h q q.isLt]
  exact map_zero _

/-- The weight-`0` component vanishes ⇒ weight `≥ 1`. -/
theorem weightGE_one_of_π₀_eq_zero (V : Ct.toScheme.Opens) (a : Γ(truncatedJetAlgebra.obj L κ, V))
    (h : (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨0, Nat.succ_pos κ⟩).app V a = 0) :
    WeightGE L κ V 1 a := by
  intro q hq
  have hq0 : q = ⟨0, Nat.succ_pos κ⟩ := Fin.ext (Nat.lt_one_iff.mp hq)
  rw [hq0]
  exact h

/-- Weights add under multiplication: the product of the `i`-th and `j`-th pieces lands in the
`(i+j)`-th piece (or is `0` when `i + j > κ`), so if `a` has weight `≥ m` and `b` has weight `≥ n`
then `mulHom (a ⊗ b)` has weight `≥ m + n`. -/
theorem weightGE_mulHom (V : Ct.toScheme.Opens) {m n : ℕ}
    {a b : Γ(truncatedJetAlgebra.obj L κ, V)}
    (ha : WeightGE L κ V m a) (hb : WeightGE L κ V n b) :
    WeightGE L κ V (m + n) ((truncatedJetAlgebra.mulHom L κ).app V
      (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.obj L κ)
        (truncatedJetAlgebra.obj L κ) V a b)) := by
  intro s hs
  -- the `s`-th component is `(mulHom ≫ π_s) (a ⊗ b)`
  show (truncatedJetAlgebra.mulHom L κ ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) s).app V
    (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.obj L κ)
      (truncatedJetAlgebra.obj L κ) V a b) = 0
  unfold truncatedJetAlgebra.mulHom
  rw [CategoryTheory.Preadditive.sum_comp]
  refine (AlgebraicGeometry.Scheme.Modules.Hom.sum_app_apply Finset.univ _ V _).trans ?_
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [CategoryTheory.Preadditive.sum_comp]
  refine (AlgebraicGeometry.Scheme.Modules.Hom.sum_app_apply Finset.univ _ V _).trans ?_
  refine Finset.sum_eq_zero (fun j _ => ?_)
  split_ifs with hij
  · -- the `(i, j)` term: `(π_i ⊗ π_j) ≫ m_{ij} ≫ ι_{i+j} ≫ π_s` on `a ⊗ b`
    have hT : (CategoryTheory.MonoidalCategory.tensorHom
        (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) i)
        (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) j)).app V
        (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.obj L κ)
          (truncatedJetAlgebra.obj L κ) V a b) =
        AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) i).app V a)
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) j).app V b) :=
      AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections _ _ V a b
    show (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨i.val + j.val, Nat.lt_succ_of_le hij⟩ ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) s).app V
      ((truncatedJetAlgebra.pieceMul L i j).app V
        ((CategoryTheory.MonoidalCategory.tensorHom
          (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) i)
          (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) j)).app V
          (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.obj L κ)
            (truncatedJetAlgebra.obj L κ) V a b))) = 0
    rw [hT]
    -- a vanishing component kills the pure tensor
    have hkill : ∀ (t : Γ(truncatedJetAlgebra.piece L i ⊗ truncatedJetAlgebra.piece L j, V)), t = 0 →
        (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨i.val + j.val, Nat.lt_succ_of_le hij⟩ ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) s).app V
        ((truncatedJetAlgebra.pieceMul L i j).app V t) = 0 := by
      intro t ht
      rw [ht, map_zero, map_zero]
    by_cases hi : i.val < m
    · refine hkill _ ?_
      refine (congrArg (fun x => AlgebraicGeometry.Scheme.Modules.tensorSections
        (truncatedJetAlgebra.piece L i) (truncatedJetAlgebra.piece L j) V x
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) j).app V b))
        (ha i hi)).trans ?_
      exact AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left _ _ V _
    by_cases hj : j.val < n
    · refine hkill _ ?_
      refine (congrArg (fun x => AlgebraicGeometry.Scheme.Modules.tensorSections
        (truncatedJetAlgebra.piece L i) (truncatedJetAlgebra.piece L j) V
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) i).app V a) x)
        (hb j hj)).trans ?_
      exact AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right _ _ V _
    have hne : (⟨i.val + j.val, Nat.lt_succ_of_le hij⟩ : Fin (κ + 1)) ≠ s := by
      intro heq
      have hval : i.val + j.val = s.val := congrArg Fin.val heq
      omega
    exact AlgebraicGeometry.Scheme.Modules.biproduct_ι_π_ne_app_apply _ hne V _
  · rw [CategoryTheory.Limits.zero_comp]
    rfl

/-- `weightGE_mulHom` for the ring multiplication of `𝒜(V)` (`sectionsMul_eq_mul_tensorSections`). -/
theorem weightGE_mul (V : Ct.toScheme.Opens) {m n : ℕ}
    {a b : (truncatedJetAlgebra L κ).sectionsRing V}
    (ha : WeightGE L κ V m a) (hb : WeightGE L κ V n b) : WeightGE L κ V (m + n) (a * b) :=
  WeightGE.congr L κ
    ((truncatedJetAlgebra L κ).sectionsMul_eq_mul_tensorSections V a b).symm
    (weightGE_mulHom L κ V ha hb)

/-- Powers of a section of weight `≥ 1` have weight `≥ n`. -/
theorem weightGE_pow (V : Ct.toScheme.Opens) {a : (truncatedJetAlgebra L κ).sectionsRing V}
    (ha : WeightGE L κ V 1 a) : ∀ n : ℕ, WeightGE L κ V n (a ^ n)
  | 0 => fun _ hq => absurd hq (Nat.not_lt_zero _)
  | n + 1 => WeightGE.congr L κ (pow_succ a n).symm (weightGE_mul L κ V (weightGE_pow V ha n) ha)

/-- **Nilpotence of the positive-weight part of the truncated jet algebra** (on sections over any
open `V`): if the weight-`0` component of `a ∈ 𝒜(V)` vanishes then `a^{κ+1} = 0`. -/
theorem pow_succ_eq_zero_of_π₀_eq_zero (V : Ct.toScheme.Opens)
    (a : (truncatedJetAlgebra L κ).sectionsRing V)
    (h : (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨0, Nat.succ_pos κ⟩).app V a = 0) :
    a ^ (κ + 1) = 0 :=
  eq_zero_of_weightGE L κ V _ (weightGE_pow L κ V (weightGE_one_of_π₀_eq_zero L κ V a h) (κ + 1))

end truncatedJetAlgebra

end
