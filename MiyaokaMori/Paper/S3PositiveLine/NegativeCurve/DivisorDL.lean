import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.Divisor
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FinitelyManyNonzeroWeightedOrders
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.RamificationIndexDef
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrder
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor

/-! # The divisor `D_L`

`D_L = Σ_y γ_y[y]` (a finite sum, not necessarily effective) and `L = O_{C̃}(D_L)` (§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `γ_y = e_y(η)·β_{η(y)}` is nonzero only at finitely many `y`. -/

theorem divisorDL_support_finite {k : Type u} [Field k] {Ct₁ Ct : SmoothProjectiveCurve k}
    (η : Ct.toScheme ⟶ Ct₁.toScheme) [AlgebraicGeometry.IsFinite η] {n κ : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct₁.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0) :
    {y : Ct.toScheme | (ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y) ≠ 0}.Finite := by
  let s : Set Ct₁.toScheme := {z | weightedOrderQ a hne z ≠ 0}
  have hs : s.Finite := finite_support_weightedOrder a hne
  have hpre : (η.base ⁻¹' s).Finite := η.finite_preimage hs
  refine hpre.subset ?_
  intro y hy
  change weightedOrderQ a hne (η.base y) ≠ 0
  intro hz
  apply hy
  simp [hz]

/- The summands have finite support (directly from the previous lemma): the `finsum` is a genuine finite sum and does not fall under the convention "infinite support gives `0`". -/

theorem divisorDL_summand_support_finite {k : Type u} [Field k] {Ct₁ Ct : SmoothProjectiveCurve k}
    (η : Ct.toScheme ⟶ Ct₁.toScheme) [AlgebraicGeometry.IsFinite η] {n κ : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct₁.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0) :
    (Function.support fun y : Ct.toScheme =>
      ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).num • Divisor.ofPoint y).Finite := by
  refine (divisorDL_support_finite η a hne).subset fun y hy => ?_
  intro h
  exact (Function.mem_support.mp hy) (by simp [h])

/- `D_L = Σ_y γ_y [y]`, written with `finsum` (no finiteness witness is needed as data; well-definedness is the two propositions above). -/

noncomputable def divisorDL {k : Type u} [Field k] {Ct₁ Ct : SmoothProjectiveCurve k}
    (η : Ct.toScheme ⟶ Ct₁.toScheme) [AlgebraicGeometry.IsFinite η] {n κ : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct₁.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0)
    (hint : ∀ y : Ct.toScheme,
      ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).den = 1) :
    CartierDivisor Ct.toVariety :=
  ∑ᶠ y : Ct.toScheme,
    ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).num • Divisor.ofPoint y

private theorem divisorDL_weilCycle_zero {k : Type u} [Field k] {V : Variety k} :
    CartierDivisor.weilCycle V (0 : CartierDivisor V) = 0 := by
  have h := CartierDivisor.weilCycle_add V (0 : CartierDivisor V) 0
  have h' : CartierDivisor.weilCycle V (0 : CartierDivisor V) +
      CartierDivisor.weilCycle V (0 : CartierDivisor V) =
      CartierDivisor.weilCycle V (0 : CartierDivisor V) := by
    simpa using h.symm
  exact (add_eq_left.mp h')

private def divisorDL_weilHom {k : Type u} [Field k] (V : Variety k) :
    CartierDivisor V →+ AlgebraicGeometry.AlgebraicCycle V.toScheme ℤ :=
  { toFun := fun D => (CartierDivisor.weilCycle V D :
        AlgebraicGeometry.AlgebraicCycle V.toScheme ℤ)
    map_zero' := by simp [divisorDL_weilCycle_zero]
    map_add' := by
      intro D E
      exact congrArg Subtype.val (CartierDivisor.weilCycle_add V D E) }

private def divisorDL_evalHom {X : AlgebraicGeometry.Scheme} (y : X) :
    AlgebraicGeometry.AlgebraicCycle X ℤ →+ ℤ :=
  { toFun := fun c => c y
    map_zero' := rfl
    map_add' := by intro c d; rfl }

theorem divisorDL_weilCycle {k : Type u} [Field k] {Ct₁ Ct : SmoothProjectiveCurve k}
    (η : Ct.toScheme ⟶ Ct₁.toScheme) [AlgebraicGeometry.IsFinite η] {n κ : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct₁.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0)
    (hint : ∀ y, ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).den = 1)
    (y : Ct.toScheme) (hy : IsClosed ({y} : Set Ct.toScheme)) :
    ((CartierDivisor.weilCycle Ct.toVariety (divisorDL η a hne hint) :
        AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) y : ℚ)
      = (ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y) := by
  let W := divisorDL_weilHom Ct.toVariety
  let ev := divisorDL_evalHom y
  have hf : Function.HasFiniteSupport (fun z : Ct.toScheme =>
      ((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
        Divisor.ofPoint z) := divisorDL_summand_support_finite η a hne
  have hmap := W.map_finsum hf
  have hcycle :
      (CartierDivisor.weilCycle Ct.toVariety
          (∑ᶠ z : Ct.toScheme,
            ((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
              Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) =
        ∑ᶠ z : Ct.toScheme,
          (CartierDivisor.weilCycle Ct.toVariety
            (((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
              Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) := by
    simpa [W, divisorDL_weilHom] using hmap
  dsimp [divisorDL]
  change (((CartierDivisor.weilCycle Ct.toVariety
      (∑ᶠ z : Ct.toScheme,
        ((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
          Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) y : ℚ) = _)
  rw [hcycle]
  have hfc : Function.HasFiniteSupport (fun z : Ct.toScheme =>
      (CartierDivisor.weilCycle Ct.toVariety
        (((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
          Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ)) := by
    simpa [Function.comp_def, W, divisorDL_weilHom] using
      (hf.comp (g := fun D : CartierDivisor Ct.toVariety =>
        (CartierDivisor.weilCycle Ct.toVariety D :
          AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ))
        (by exact congrArg Subtype.val (divisorDL_weilCycle_zero (V := Ct.toVariety))))
  have hev := (divisorDL_evalHom y).map_finsum hfc
  have hev' :
      ((∑ᶠ z : Ct.toScheme,
        (CartierDivisor.weilCycle Ct.toVariety
          (((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
            Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ)) y) =
        ∑ᶠ z : Ct.toScheme,
          ((CartierDivisor.weilCycle Ct.toVariety
            (((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
              Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) y) := by
    change (∑ᶠ z : Ct.toScheme,
        (CartierDivisor.weilCycle Ct.toVariety
          (((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
            Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ)) y =
      ∑ᶠ z : Ct.toScheme,
        ((CartierDivisor.weilCycle Ct.toVariety
          (((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
            Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) y) at hev
    exact hev
  rw [hev']
  rw [finsum_eq_single _ y]
  · have hscalarY :
        (CartierDivisor.weilCycle Ct.toVariety
            (((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).num •
              Divisor.ofPoint y) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) =
          ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).num •
            (CartierDivisor.weilCycle Ct.toVariety (Divisor.ofPoint y) :
              AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) := by
      exact map_zsmul (divisorDL_weilHom Ct.toVariety)
        ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).num
        (Divisor.ofPoint y)
    rw [hscalarY]
    have hval :
        (((((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).num •
          (CartierDivisor.weilCycle Ct.toVariety (Divisor.ofPoint y) :
            AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ)) y) : ℤ) =
          ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).num := by
      change ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).num •
          ((CartierDivisor.weilCycle Ct.toVariety (Divisor.ofPoint y) :
            AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) y) = _
      rw [Divisor.ofPoint_weilCycle y hy y]
      simp
    rw [hval]
    have hd := hint y
    rw [← Rat.num_div_den ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y))]
    simp [hd]
  · intro z hzy
    by_cases hz : IsClosed ({z} : Set Ct.toScheme)
    · have hscalar :
          (CartierDivisor.weilCycle Ct.toVariety
              (((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
                Divisor.ofPoint z) : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) =
            ((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
              (CartierDivisor.weilCycle Ct.toVariety (Divisor.ofPoint z) :
                AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) := by
        exact map_zsmul (divisorDL_weilHom Ct.toVariety)
          ((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num
          (Divisor.ofPoint z)
      rw [hscalar]
      change ((ramificationIndex η z : ℚ) * weightedOrderQ a hne (η.base z)).num •
        ((CartierDivisor.weilCycle Ct.toVariety (Divisor.ofPoint z) :
          AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) y) = 0
      rw [Divisor.ofPoint_weilCycle z hz y]
      simp [Ne.symm hzy]
    · rw [Divisor.ofPoint_of_not_isClosed z hz]
      simp only [smul_zero]
      change (CartierDivisor.weilCycle Ct.toVariety (0 : CartierDivisor Ct.toVariety) :
        AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) y = 0
      rw [divisorDL_weilCycle_zero]
      rfl

noncomputable def bundleL {k : Type u} [Field k] {Ct₁ Ct : SmoothProjectiveCurve k}
    (η : Ct.toScheme ⟶ Ct₁.toScheme) [AlgebraicGeometry.IsFinite η] {n κ : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct₁.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0)
    (hint : ∀ y, ((ramificationIndex η y : ℚ) * weightedOrderQ a hne (η.base y)).den = 1) :
    LineBundle Ct.toVariety :=
  (divisorDL η a hne hint).lineBundle

end
