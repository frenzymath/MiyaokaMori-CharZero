import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.CapCommutes
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackSquareVanishes
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors

/-! # Binomial expansion of mixed intersection numbers (`c₁(M) = x·β + y·φ`, `φ² ≡ 0`)

General bookkeeping for the intersection numbers on a fibered variety, entirely at the level of the
ℤ-Chow groups:

* `capDeg X hX M e α := deg(c₁(M)^e ∩ α)` (the same definition as `capDegree` in the negative-curve
  argument).
* `capDeg_succ`: `deg(c₁(M)^{e+1} ∩ α) = deg(c₁(M)^e ∩ (c₁(M) ∩ α))`.
* `degreeOver_pullback_pullback_eq_zero`: the product of the `c₁` of two line bundles pulled back from a
  curve, acting on a 2-dimensional class, has degree `0` (the ℤ-form of `PullbackSquareVanishes.lean`,
  through `ChowGroupRat.degree_tmul`).
* `capDeg_sq_zero`: from the previous item and commutativity of caps, by induction,
  `deg(β^k ∩ φ ∩ φ' ∩ γ) = 0` (`φ, φ'` both pulled back from the curve).
* `capDeg_expand` (main result): if `c₁(M) = x·c₁(β̂) + y·c₁(φ̂)` (in every dimension), the `c₁` of `β̂`,
  `φ̂` commute, and `deg(β^k ∩ φ ∩ φ ∩ γ) = 0`, then for all `n, γ`
  `deg(c₁(M)^{n+1} ∩ γ) = x^{n+1}·deg(β^{n+1} ∩ γ) + (n+1)·x^n·y·deg(β^n ∩ φ ∩ γ)`.

Source: Fulton, Intersection Theory, §2.5 (additivity and commutativity of `c₁`); the expansion used in
the proof of Lemma 2.5 of the paper. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.CapDegreeExpansion

open AlgebraicGeometry

variable {K : Type u} [Field K]

/-- The mixed intersection number `deg(c₁(M)^e ∩ α)` (the same as `FiberedNegativeCurve.capDegree`). -/
def capDeg (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) (α : AlgebraicGeometry.ChowGroup X e) : ℤ :=
  AlgebraicGeometry.ChowGroup.degreeOver K X hX
    (AlgebraicGeometry.firstChernClass.capPow M e 0
      (cast (congrArg (AlgebraicGeometry.ChowGroup X) (zero_add e).symm) α))

variable (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)

private theorem cast_chow_add {m n : ℕ} (h : m = n) (α β : AlgebraicGeometry.ChowGroup X m) :
    cast (congrArg (AlgebraicGeometry.ChowGroup X) h) (α + β) =
      cast (congrArg (AlgebraicGeometry.ChowGroup X) h) α +
        cast (congrArg (AlgebraicGeometry.ChowGroup X) h) β := by
  subst h; rfl

private theorem cast_chow_nsmul {m n : ℕ} (h : m = n) (k : ℕ) (α : AlgebraicGeometry.ChowGroup X m) :
    cast (congrArg (AlgebraicGeometry.ChowGroup X) h) (k • α) =
      k • cast (congrArg (AlgebraicGeometry.ChowGroup X) h) α := by
  subst h; rfl

/-- `cast` commutes with `c₁`. -/
private theorem cast_firstChernClass {m n : ℕ} (h : m = n) (L : X.Modules) [L.IsLineBundle]
    (α : AlgebraicGeometry.ChowGroup X (m + 1)) :
    AlgebraicGeometry.firstChernClass L (n + 1)
        (cast (congrArg (AlgebraicGeometry.ChowGroup X) (congrArg Nat.succ h)) α) =
      cast (congrArg (AlgebraicGeometry.ChowGroup X) h)
        (AlgebraicGeometry.firstChernClass L (m + 1) α) := by
  subst h; rfl

theorem capDeg_add (M : X.Modules) [M.IsLineBundle] (e : ℕ) (α β : AlgebraicGeometry.ChowGroup X e) :
    capDeg X hX M e (α + β) = capDeg X hX M e α + capDeg X hX M e β := by
  unfold capDeg
  rw [cast_chow_add X (zero_add e).symm, map_add, map_add]

theorem capDeg_nsmul (M : X.Modules) [M.IsLineBundle] (e : ℕ) (k : ℕ)
    (α : AlgebraicGeometry.ChowGroup X e) :
    capDeg X hX M e (k • α) = (k : ℤ) * capDeg X hX M e α := by
  unfold capDeg
  rw [cast_chow_nsmul X (zero_add e).symm, map_nsmul, map_nsmul, nsmul_eq_mul]

theorem capDeg_zero_eq (M : X.Modules) [M.IsLineBundle] (α : AlgebraicGeometry.ChowGroup X 0) :
    capDeg X hX M 0 α = AlgebraicGeometry.ChowGroup.degreeOver K X hX α := rfl

/-- `deg(c₁(M)^{e+1} ∩ α) = deg(c₁(M)^e ∩ (c₁(M) ∩ α))`. -/
theorem capDeg_succ (M : X.Modules) [M.IsLineBundle] (e : ℕ)
    (α : AlgebraicGeometry.ChowGroup X (e + 1)) :
    capDeg X hX M (e + 1) α = capDeg X hX M e (AlgebraicGeometry.firstChernClass M (e + 1) α) := by
  unfold capDeg
  show AlgebraicGeometry.ChowGroup.degreeOver K X hX
      (AlgebraicGeometry.firstChernClass.capPow M e 0
        (AlgebraicGeometry.firstChernClass M (0 + e + 1)
          (cast (congrArg (AlgebraicGeometry.ChowGroup X) (zero_add (e + 1)).symm) α))) = _
  congr 2
  exact cast_firstChernClass X (zero_add e).symm M α

/-- Pointwise form of the commutativity `c₁(L)(c₁(L') z) = c₁(L')(c₁(L) z)`. -/
theorem firstChernClass_comm_apply (hX : IsProperOver K X) (L L' : X.Modules) [L.IsLineBundle]
    [L'.IsLineBundle] (k : ℕ) (z : AlgebraicGeometry.ChowGroup X (k + 2)) :
    AlgebraicGeometry.firstChernClass L (k + 1) (AlgebraicGeometry.firstChernClass L' (k + 2) z) =
      AlgebraicGeometry.firstChernClass L' (k + 1) (AlgebraicGeometry.firstChernClass L (k + 2) z) := by
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hX
  exact DFunLike.congr_fun (AlgebraicGeometry.firstChernClass_comm (k := K) L L' k) z

/-- **The product of two classes pulled back from the curve has degree `0` on 2-dimensional classes**
(the ℤ-form of `PullbackSquareVanishes.lean`). -/
theorem degreeOver_pullback_pullback_eq_zero [IsAlgClosed K] {C : SmoothProjectiveCurve K}
    (ρ : X ⟶ C.toScheme) [ρ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsProper ρ]
    (N N' : C.toScheme.Modules) [N.IsLineBundle] [N'.IsLineBundle]
    (β : AlgebraicGeometry.ChowGroup X 2) :
    AlgebraicGeometry.ChowGroup.degreeOver K X hX
      (AlgebraicGeometry.firstChernClass ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N) 1
        (AlgebraicGeometry.firstChernClass ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N') 2 β))
      = 0 := by
  have h := pullback_divisor_mul_cap_degree_eq_zero hX C.isProper ρ N N' ((1 : ℚ) ⊗ₜ[ℤ] β)
  have h1 : AlgebraicGeometry.ratDivisorOpOfLineBundle
      ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N') 1 ((1 : ℚ) ⊗ₜ[ℤ] β) =
      (1 : ℚ) ⊗ₜ[ℤ] (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N') 2 β) := by
    show LinearMap.baseChange ℚ _ _ = _
    rw [LinearMap.baseChange_tmul]
    rfl
  have h2 : ∀ γ : AlgebraicGeometry.ChowGroup X 1, AlgebraicGeometry.ratDivisorOpOfLineBundle
      ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N) 0 ((1 : ℚ) ⊗ₜ[ℤ] γ) =
      (1 : ℚ) ⊗ₜ[ℤ] (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N) 1 γ) := by
    intro γ
    show LinearMap.baseChange ℚ _ _ = _
    rw [LinearMap.baseChange_tmul]
    rfl
  rw [h1, h2, AlgebraicGeometry.ChowGroupRat.degree_tmul, one_mul] at h
  exact_mod_cast h

/-- `deg(β^k ∩ φ ∩ φ' ∩ γ) = 0`: by induction on `k` from the 2-dimensional case and commutativity. -/
theorem capDeg_sq_zero (Bh Φ Φ' : X.Modules) [Bh.IsLineBundle] [Φ.IsLineBundle] [Φ'.IsLineBundle]
    (h0 : ∀ γ : AlgebraicGeometry.ChowGroup X 2,
      AlgebraicGeometry.ChowGroup.degreeOver K X hX
        (AlgebraicGeometry.firstChernClass Φ 1 (AlgebraicGeometry.firstChernClass Φ' 2 γ)) = 0) :
    ∀ (k : ℕ) (γ : AlgebraicGeometry.ChowGroup X (k + 2)),
      capDeg X hX Bh k (AlgebraicGeometry.firstChernClass Φ (k + 1)
        (AlgebraicGeometry.firstChernClass Φ' (k + 2) γ)) = 0
  | 0, γ => h0 γ
  | k + 1, γ => by
    rw [capDeg_succ, firstChernClass_comm_apply X hX Bh Φ k,
      firstChernClass_comm_apply X hX Bh Φ' (k + 1)]
    exact capDeg_sq_zero Bh Φ Φ' h0 k _

/-- **Binomial expansion**: `c₁(M) = x·c₁(β̂) + y·c₁(φ̂)`, `φ̂² ≡ 0` ⇒
`deg(c₁(M)^{n+1} ∩ γ) = x^{n+1}·deg(β̂^{n+1} ∩ γ) + (n+1)·x^n·y·deg(β̂^n ∩ φ̂ ∩ γ)`. -/
theorem capDeg_expand (M Bh Φ : X.Modules) [M.IsLineBundle] [Bh.IsLineBundle] [Φ.IsLineBundle]
    (x y : ℕ)
    (hM : ∀ (k : ℕ) (z : AlgebraicGeometry.ChowGroup X (k + 1)),
      AlgebraicGeometry.firstChernClass M (k + 1) z =
        x • AlgebraicGeometry.firstChernClass Bh (k + 1) z +
          y • AlgebraicGeometry.firstChernClass Φ (k + 1) z)
    (hsq : ∀ (k : ℕ) (γ : AlgebraicGeometry.ChowGroup X (k + 2)),
      capDeg X hX Bh k (AlgebraicGeometry.firstChernClass Φ (k + 1)
        (AlgebraicGeometry.firstChernClass Φ (k + 2) γ)) = 0) :
    ∀ (n : ℕ) (γ : AlgebraicGeometry.ChowGroup X (n + 1)),
      capDeg X hX M (n + 1) γ =
        (x : ℤ) ^ (n + 1) * capDeg X hX Bh (n + 1) γ +
          ((n : ℤ) + 1) * (x : ℤ) ^ n * (y : ℤ) *
            capDeg X hX Bh n (AlgebraicGeometry.firstChernClass Φ (n + 1) γ)
  | 0, γ => by
    rw [capDeg_succ, hM 0 γ, capDeg_add, capDeg_nsmul, capDeg_nsmul, capDeg_succ X hX Bh 0 γ]
    simp only [capDeg_zero_eq]
    ring
  | n + 1, γ => by
    rw [capDeg_succ, hM (n + 1) γ, capDeg_add, capDeg_nsmul, capDeg_nsmul,
      capDeg_expand M Bh Φ x y hM hsq n, capDeg_expand M Bh Φ x y hM hsq n,
      ← capDeg_succ X hX Bh (n + 1) γ, firstChernClass_comm_apply X hX Φ Bh n γ,
      ← capDeg_succ X hX Bh n, hsq n γ]
    push_cast
    ring

end MiyaokaMori.CapDegreeExpansion

end
