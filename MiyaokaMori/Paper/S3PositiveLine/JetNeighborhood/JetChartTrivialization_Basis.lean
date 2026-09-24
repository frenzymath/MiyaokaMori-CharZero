import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.BiproductSections
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Frames

/-! # The sections ring of the truncated jet algebra over a frame is a truncated polynomial ring

**Over an open `V` where `L^{-1}` has a frame `μ`, the sections ring `𝒜(V)` of the truncated jet algebra
`𝒜 = ⊕_{q ≤ κ} L^{-q}` is `O(V)[t]/(t^{κ+1})` with `t = ι_1(μ)`** (§3 of the paper, the local description of `C̃_(k)(L)`).

* `framePow μ q = μ^{⊗q} ∈ Γ(V, L^{-q})` (`piece L q = M^{⊗q}`, `M = L^{-1}`), a frame of `L^{-q}` when `μ` is a
  frame (`IsFrame.tensorSections`); the piece multiplication `m_{a,b}` sends `μ^{⊗a} ⊗ μ^{⊗b}` to `μ^{⊗(a+b)}`
  (`pieceMul_app_framePow`: induction on `b`, right unitor and associator on section pairs).
* `tau μ q = ι_q(μ^{⊗q}) ∈ 𝒜(V)`; `tau a * tau b = tau (a+b)` if `a + b ≤ κ`, else `0` (`tau_mul`:
  `sectionsMul_eq_mul_tensorSections`, `tensorHom_tensorSections`, `ι_tensor_ι_comp_mulHom`); `tau 0 = 1`.
* `𝒜(V)` is the free `O(V)`-module on `tau 0, …, tau κ`: `x = Σ_q coord_q(π_q x) · tau q`
  (`biproduct_sections_total` + frame coordinates) and `π_j (Σ_q r_q · tau q) = r_j • μ^{⊗j}`.
* `polyToSections μ : O(V)[t] → 𝒜(V)`, `t ↦ tau' 1` (`tau' n := tau n` for `n ≤ κ`, else `0`), is surjective
  with kernel `(t^{κ+1})` (`X_pow_dvd_iff`); hence `quotToSections μ : O(V)[t]/(t^{κ+1}) → 𝒜(V)` is bijective,
  sends the constants to `sectionsUnit V` and `t` to `tau' 1` (which is `ι_1(1 ⊗ μ)` when `1 ≤ κ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `1` is a frame of the unit `O_X` on every open. -/
theorem isFrame_tensorUnit_one (W : X.Opens) : IsFrame (𝟙_ X.Modules) W (1 : Γ(X, W)) := by
  intro W' h
  have hres : (𝟙_ X.Modules).res h (1 : Γ(X, W)) = (1 : Γ(X, W')) :=
    map_one (X.presheaf.map (homOfLE h).op).hom
  have hfun : (fun r : Γ(X, W') => r • (𝟙_ X.Modules).res h (1 : Γ(X, W))) = id := by
    funext r
    rw [hres]
    exact mul_one r
  rw [hfun]
  exact Function.bijective_id

theorem iso_inv_app_eq_of_hom_app_eq {A B : X.Modules} (e : A ≅ B) (U : X.Opens) {x : Γ(A, U)} {y : Γ(B, U)}
    (h : e.hom.app U x = y) : e.inv.app U y = x := by
  rw [← h]
  exact congrArg (fun φ : A ⟶ A => φ.app U x) e.hom_inv_id

theorem whiskerRight_app_tensorSections_jct {A A' B : X.Modules} (f : A ⟶ A') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 B) U a b

theorem whiskerLeft_app_tensorSections_jct (A : X.Modules) {B B' : X.Modules} (g : B ⟶ B') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (A ◁ g).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B' U a (g.app U b) := by
  rw [← MonoidalCategory.id_tensorHom]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (𝟙 A) g U a b

theorem leftUnitor_inv_app_jct (A : X.Modules) (U : X.Opens) (a : Γ(A, U)) :
    (λ_ A).inv.app U a =
      AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) A U (1 : Γ(X, U)) a :=
  iso_inv_app_eq_of_hom_app_eq (λ_ A) U ((leftUnitor_app_tensorSections A U 1 a).trans (one_smul _ a))

theorem associator_inv_app_tensorSections_jct (A B C : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    (α_ A B C).inv.app U (AlgebraicGeometry.Scheme.Modules.tensorSections A
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C) U a
        (AlgebraicGeometry.Scheme.Modules.tensorSections B C U b c)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) C U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) c :=
  iso_inv_app_eq_of_hom_app_eq (α_ A B C) U (associator_app_tensorSections A B C U a b c)

end AlgebraicGeometry.Scheme.Modules

namespace truncatedJetAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety)
  (V : Ct.toScheme.Opens) (μ : Γ((L.zpow (-1)).toModules, V))

/-- `μ^{⊗q} ∈ Γ(V, M^{⊗q})`: `μ^{⊗0} = 1`, `μ^{⊗(q+1)} = μ^{⊗q} ⊗ μ`. -/
noncomputable def framePow : ∀ q : ℕ, Γ(truncatedJetAlgebra.piece L q, V)
  | 0 => (1 : Γ(Ct.toScheme, V))
  | q + 1 => AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.piece L q)
      (L.zpow (-1)).toModules V (framePow q) μ

theorem framePow_zero : framePow L V μ 0 = (1 : Γ(Ct.toScheme, V)) := rfl

theorem framePow_one : framePow L V μ 1 =
    AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Ct.toScheme.Modules) (L.zpow (-1)).toModules V
      (1 : Γ(Ct.toScheme, V)) μ := rfl

theorem framePow_succ (q : ℕ) : framePow L V μ (q + 1) =
    AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.piece L q)
      (L.zpow (-1)).toModules V (framePow L V μ q) μ := rfl

/-- Tensor powers of a frame of `L^{-1}` are frames of the pieces. -/
theorem framePow_isFrame (hμ : IsFrame (L.zpow (-1)).toModules V μ) :
    ∀ q : ℕ, IsFrame (truncatedJetAlgebra.piece L q) V (framePow L V μ q)
  | 0 => isFrame_tensorUnit_one V
  | q + 1 => IsFrame.tensorSections (framePow_isFrame hμ q) hμ

/-- The piece multiplication on frame powers: `m_{a,b}(μ^{⊗a} ⊗ μ^{⊗b}) = μ^{⊗(a+b)}`. -/
theorem pieceMul_app_framePow (a : ℕ) : ∀ b : ℕ,
    (truncatedJetAlgebra.pieceMul L a b).app V
      (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.piece L a)
        (truncatedJetAlgebra.piece L b) V (framePow L V μ a) (framePow L V μ b)) =
      framePow L V μ (a + b)
  | 0 => by
    show (ρ_ (truncatedJetAlgebra.piece L a)).hom.app V
      (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.piece L a) (𝟙_ _) V
        (framePow L V μ a) (1 : Γ(Ct.toScheme, V))) = framePow L V μ a
    rw [rightUnitor_app_tensorSections, one_smul]
  | b + 1 => by
    show (truncatedJetAlgebra.pieceMul L a b ▷ (L.zpow (-1)).toModules).app V
      ((α_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b) (L.zpow (-1)).toModules).inv.app V
        (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.piece L a)
          (truncatedJetAlgebra.piece L b ⊗ (L.zpow (-1)).toModules) V (framePow L V μ a)
          (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.piece L b)
            (L.zpow (-1)).toModules V (framePow L V μ b) μ))) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.piece L (a + b))
        (L.zpow (-1)).toModules V (framePow L V μ (a + b)) μ
    rw [associator_inv_app_tensorSections_jct, whiskerRight_app_tensorSections_jct, pieceMul_app_framePow a b]

variable (κ : ℕ)

/-- `τ_q := ι_q(μ^{⊗q}) ∈ 𝒜(V)`. -/
noncomputable def tau (q : Fin (κ + 1)) : (truncatedJetAlgebra L κ).sectionsRing V :=
  (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V
    (framePow L V μ q)

theorem tau_zero : tau L V μ κ ⟨0, Nat.succ_pos κ⟩ = 1 := rfl

theorem π_tau_self (q : Fin (κ + 1)) :
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V
      (tau L V μ κ q) = framePow L V μ q :=
  biproduct_π_ι_self_app_apply _ V q _

theorem π_tau_ne {q j : Fin (κ + 1)} (h : q ≠ j) :
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) j).app V
      (tau L V μ κ q) = 0 :=
  biproduct_π_ι_ne_app_apply _ V h _

/-- `τ_a · τ_b = τ_{a+b}` (or `0` when `a + b > κ`). -/
theorem tau_mul (a b : Fin (κ + 1)) :
    tau L V μ κ a * tau L V μ κ b =
      if h : a.val + b.val ≤ κ then tau L V μ κ ⟨a.val + b.val, Nat.lt_succ_of_le h⟩ else 0 := by
  have hmul := (truncatedJetAlgebra L κ).sectionsMul_eq_mul_tensorSections V (tau L V μ κ a) (tau L V μ κ b)
  have hT := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) a)
    (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) b) V
    (framePow L V μ a) (framePow L V μ b)
  have hc := congrArg (fun φ => φ.app V (AlgebraicGeometry.Scheme.Modules.tensorSections
      (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b) V (framePow L V μ a) (framePow L V μ b)))
    (truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ a.val b.val a.2 b.2)
  rw [hmul]
  change (truncatedJetAlgebra.mulHom L κ).app V (AlgebraicGeometry.Scheme.Modules.tensorSections
    (truncatedJetAlgebra.obj L κ) (truncatedJetAlgebra.obj L κ) V (tau L V μ κ a) (tau L V μ κ b)) = _
  unfold tau
  refine (congrArg (fun z => (truncatedJetAlgebra.mulHom L κ).app V z) hT.symm).trans ?_
  refine (show ((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) a ⊗ₘ
      CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) b) ≫
      truncatedJetAlgebra.mulHom L κ).app V (AlgebraicGeometry.Scheme.Modules.tensorSections
        (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b) V (framePow L V μ a) (framePow L V μ b)) =
      _ from hc).trans ?_
  split_ifs with h
  · show (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨a.val + b.val, Nat.lt_succ_of_le h⟩).app V ((truncatedJetAlgebra.pieceMul L a b).app V
        (AlgebraicGeometry.Scheme.Modules.tensorSections (truncatedJetAlgebra.piece L a)
          (truncatedJetAlgebra.piece L b) V (framePow L V μ a) (framePow L V μ b))) = _
    rw [pieceMul_app_framePow]
  · rfl

/-- `τ'_n := τ_n` for `n ≤ κ`, `0` otherwise. -/
noncomputable def tau' (n : ℕ) : (truncatedJetAlgebra L κ).sectionsRing V :=
  if h : n ≤ κ then tau L V μ κ ⟨n, Nat.lt_succ_of_le h⟩ else 0

theorem tau'_of_le {n : ℕ} (h : n ≤ κ) : tau' L V μ κ n = tau L V μ κ ⟨n, Nat.lt_succ_of_le h⟩ := dif_pos h

theorem tau'_of_gt {n : ℕ} (h : κ < n) : tau' L V μ κ n = 0 := dif_neg (Nat.not_le_of_lt h)

theorem tau'_zero : tau' L V μ κ 0 = 1 := by
  rw [tau'_of_le L V μ κ (Nat.zero_le κ)]
  rfl

theorem tau'_mul (m n : ℕ) : tau' L V μ κ m * tau' L V μ κ n = tau' L V μ κ (m + n) := by
  by_cases hm : m ≤ κ
  · by_cases hn : n ≤ κ
    · rw [tau'_of_le L V μ κ hm, tau'_of_le L V μ κ hn, tau_mul]
      unfold tau'
      rfl
    · rw [tau'_of_gt L V μ κ (Nat.lt_of_not_le hn), mul_zero, tau'_of_gt]
      omega
  · rw [tau'_of_gt L V μ κ (Nat.lt_of_not_le hm), zero_mul, tau'_of_gt]
    omega

theorem tau'_one_pow : ∀ n : ℕ, tau' L V μ κ 1 ^ n = tau' L V μ κ n
  | 0 => by rw [pow_zero, tau'_zero]
  | n + 1 => by rw [pow_succ, tau'_one_pow n, tau'_mul]

/-- `sectionsUnit r · τ_q = ι_q (r • μ^{⊗q})`. -/
theorem sectionsUnit_mul_tau (r : Γ(Ct.toScheme, V)) (q : Fin (κ + 1)) :
    (truncatedJetAlgebra L κ).sectionsUnit V r * tau L V μ κ q =
      (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V
        (r • framePow L V μ q) := by
  rw [(truncatedJetAlgebra L κ).smul_eq_sectionsUnit_mul V r (tau L V μ κ q)]
  exact (AlgebraicGeometry.Scheme.Modules.Hom.app_smul _ r _).symm

/-- `π_j (Σ_q sectionsUnit r_q · τ_q) = r_j • μ^{⊗j}`. -/
theorem π_sum_sectionsUnit_mul_tau (r : Fin (κ + 1) → Γ(Ct.toScheme, V)) (j : Fin (κ + 1)) :
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) j).app V
      (∑ q : Fin (κ + 1), (truncatedJetAlgebra L κ).sectionsUnit V (r q) * tau L V μ κ q) =
      r j • framePow L V μ j := by
  simp only [sectionsUnit_mul_tau]
  rw [map_sum, Finset.sum_eq_single j]
  · exact biproduct_π_ι_self_app_apply _ V j _
  · intro q _ hq
    exact biproduct_π_ι_ne_app_apply _ V hq _
  · intro hj
    exact absurd (Finset.mem_univ j) hj

section Frame

variable (hμ : IsFrame (L.zpow (-1)).toModules V μ)
include hμ

/-- Every section of `𝒜` over `V` is an `O(V)`-combination of the `τ_q`, with coefficients the frame
coordinates of its components. -/
theorem eq_sum_coord_mul_tau (x : (truncatedJetAlgebra L κ).sectionsRing V) :
    x = ∑ q : Fin (κ + 1), (truncatedJetAlgebra L κ).sectionsUnit V
      ((framePow_isFrame L V μ hμ q).coord le_rfl
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V x)) *
      tau L V μ κ q := by
  simp only [sectionsUnit_mul_tau]
  refine (biproduct_sections_total (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) V x).trans ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  have h := (framePow_isFrame L V μ hμ q).coord_smul_frame le_rfl
    ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V x)
  rw [res_self] at h
  exact h.symm

theorem coord_eq_zero_of_smul_framePow_eq_zero (q : ℕ) {r : Γ(Ct.toScheme, V)}
    (h : r • framePow L V μ q = 0) : r = 0 := by
  have hinj := ((framePow_isFrame L V μ hμ q) V le_rfl).1
  apply hinj
  show r • (truncatedJetAlgebra.piece L q).res le_rfl (framePow L V μ q) =
    (0 : Γ(Ct.toScheme, V)) • (truncatedJetAlgebra.piece L q).res le_rfl (framePow L V μ q)
  rw [res_self, h, zero_smul]

end Frame

/-- `O(V)[t] → 𝒜(V)`, `t ↦ τ'_1`, constants through `sectionsUnit`. -/
noncomputable def polyToSections : Polynomial Γ(Ct.toScheme, V) →+* (truncatedJetAlgebra L κ).sectionsRing V :=
  Polynomial.eval₂RingHom ((truncatedJetAlgebra L κ).sectionsUnit V) (tau' L V μ κ 1)

theorem polyToSections_C (r : Γ(Ct.toScheme, V)) :
    polyToSections L V μ κ (Polynomial.C r) = (truncatedJetAlgebra L κ).sectionsUnit V r :=
  Polynomial.eval₂_C _ _

theorem polyToSections_X : polyToSections L V μ κ Polynomial.X = tau' L V μ κ 1 :=
  Polynomial.eval₂_X _ _

theorem polyToSections_X_pow (n : ℕ) : polyToSections L V μ κ (Polynomial.X ^ n) = tau' L V μ κ n := by
  rw [map_pow, polyToSections_X, tau'_one_pow]

theorem polyToSections_X_pow_succ : polyToSections L V μ κ (Polynomial.X ^ (κ + 1)) = 0 := by
  rw [polyToSections_X_pow, tau'_of_gt L V μ κ (Nat.lt_succ_self κ)]

theorem polyToSections_apply (p : Polynomial Γ(Ct.toScheme, V)) :
    polyToSections L V μ κ p = p.sum fun n c => (truncatedJetAlgebra L κ).sectionsUnit V c * tau' L V μ κ n := by
  show Polynomial.eval₂ _ _ p = _
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  exact Finset.sum_congr rfl fun n _ => by rw [tau'_one_pow]

/-- `π_j (polyToSections p) = coeff p j • μ^{⊗j}` for `j ≤ κ`. -/
theorem π_polyToSections (p : Polynomial Γ(Ct.toScheme, V)) (j : Fin (κ + 1)) :
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) j).app V
      (polyToSections L V μ κ p) = p.coeff j • framePow L V μ j := by
  classical
  rw [polyToSections_apply, Polynomial.sum_def, map_sum]
  have hterm : ∀ n ∈ p.support,
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) j).app V
        ((truncatedJetAlgebra L κ).sectionsUnit V (p.coeff n) * tau' L V μ κ n) =
      if n = j.val then p.coeff j • framePow L V μ j else 0 := by
    intro n _
    by_cases hn : n ≤ κ
    · rw [tau'_of_le L V μ κ hn, sectionsUnit_mul_tau]
      by_cases hnj : n = j.val
      · rw [if_pos hnj]
        have hfin : (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (κ + 1)) = j := Fin.ext hnj
        subst hfin
        exact biproduct_π_ι_self_app_apply _ V _ _
      · rw [if_neg hnj]
        exact biproduct_π_ι_ne_app_apply _ V (fun h => hnj (congrArg Fin.val h)) _
    · rw [tau'_of_gt L V μ κ (Nat.lt_of_not_le hn), mul_zero, map_zero, if_neg]
      intro hnj
      exact hn (hnj ▸ Nat.le_of_lt_succ j.2)
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' p.support j.val]
  split_ifs with hj
  · rfl
  · rw [Polynomial.notMem_support_iff.mp hj, zero_smul]

theorem polyToSections_eq_zero_of_mem (p : Polynomial Γ(Ct.toScheme, V))
    (hp : p ∈ Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)}) :
    polyToSections L V μ κ p = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hp
  rw [map_mul, polyToSections_X_pow_succ, zero_mul]

/-- `O(V)[t]/(t^{κ+1}) → 𝒜(V)`, `t ↦ τ'_1`, constants through `sectionsUnit`. -/
noncomputable def quotToSections :
    (Polynomial Γ(Ct.toScheme, V) ⧸
      Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)}) →+*
      (truncatedJetAlgebra L κ).sectionsRing V :=
  Ideal.Quotient.lift _ (polyToSections L V μ κ) (polyToSections_eq_zero_of_mem L V μ κ)

theorem quotToSections_mk (p : Polynomial Γ(Ct.toScheme, V)) :
    quotToSections L V μ κ (Ideal.Quotient.mk _ p) = polyToSections L V μ κ p :=
  Ideal.Quotient.lift_mk _ _ _

theorem quotToSections_comp_mk_comp_C :
    (quotToSections L V μ κ).comp
        ((Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)})).comp
          Polynomial.C) =
      (truncatedJetAlgebra L κ).sectionsUnit V := by
  ext r
  exact (quotToSections_mk L V μ κ _).trans (polyToSections_C L V μ κ r)

theorem quotToSections_mk_X :
    quotToSections L V μ κ (Ideal.Quotient.mk _ Polynomial.X) = tau' L V μ κ 1 :=
  (quotToSections_mk L V μ κ _).trans (polyToSections_X L V μ κ)

section Frame

variable (hμ : IsFrame (L.zpow (-1)).toModules V μ)
include hμ

theorem polyToSections_surjective : Function.Surjective (polyToSections L V μ κ) := by
  intro x
  refine ⟨∑ q : Fin (κ + 1), Polynomial.C ((framePow_isFrame L V μ hμ q).coord le_rfl
    ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V x)) *
    Polynomial.X ^ q.val, ?_⟩
  rw [map_sum]
  conv_rhs => rw [eq_sum_coord_mul_tau L V μ κ hμ x]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, polyToSections_C, polyToSections_X_pow, tau'_of_le L V μ κ (Nat.le_of_lt_succ q.2)]

theorem X_pow_succ_dvd_of_polyToSections_eq_zero {p : Polynomial Γ(Ct.toScheme, V)}
    (hp : polyToSections L V μ κ p = 0) : Polynomial.X ^ (κ + 1) ∣ p := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have h := π_polyToSections L V μ κ p ⟨d, hd⟩
  rw [hp, map_zero] at h
  exact coord_eq_zero_of_smul_framePow_eq_zero L V μ hμ d h.symm

/-- **`O(V)[t]/(t^{κ+1}) ≅ 𝒜(V)`** when `μ` is a frame of `L^{-1}` on `V`. -/
theorem quotToSections_bijective : Function.Bijective (quotToSections L V μ κ) := by
  refine ⟨RingHom.lift_injective_of_ker_le_ideal _ _ ?_, Ideal.Quotient.lift_surjective_of_surjective _ _
    (polyToSections_surjective L V μ κ hμ)⟩
  intro p hp
  exact Ideal.mem_span_singleton.mpr
    (X_pow_succ_dvd_of_polyToSections_eq_zero L V μ κ hμ (RingHom.mem_ker.mp hp))

end Frame

end truncatedJetAlgebra

end
