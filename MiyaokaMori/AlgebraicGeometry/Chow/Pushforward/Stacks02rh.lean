import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FlatPullbackCycleMap
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.IntegralHomHeightEq
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteFiberDegreeRankAtStalk

/-! # Pushforward of the pullback along a finite locally free morphism

Stacks 02RH: if `f : X → Y` is finite locally free of degree `d`, then `f` is proper and flat (of
relative dimension `0`), and `f_* f^* α = d·α` for every `k`-cycle `α`.

Source: Stacks 02RH (Chow Homology, "finite locally free, pushforward of pullback is multiplication by the degree").

Route (a pointwise route, not the coherent-sheaf route of the original text):
1. `AlgebraicGeometry.AlgebraicCycle.properPushforward f β y = ∑ᶠ x ∈ f⁻¹{y}, β x * mapCoeff f height height x` by definition
   (Mathlib `AlgebraicCycle.map`, `Function.locallyFinsupp.map_apply`), and `mapCoeff f height height x =
   f.residueDegree x` because a finite (hence integral) morphism preserves `Order.height`
   (`Scheme.height_apply_eq_of_isIntegralHom`).
2. `flatPullbackCycle f 0 α x = α (f x) * length(O_{F,x})` where `F = f.fiber (f x)` (`flatPullbackCycle_apply`,
   which needs `LocallyOfFiniteType f` — automatic from `IsFinite f` — and `IsLocallyNoetherian Y`); its side
   condition `coheight (f.asFiber x) = 0` holds because the fiber of a finite morphism is an Artinian scheme,
   hence discrete (`coheight_asFiber_eq_zero_of_isFinite` below), and `height x = height (f x) + 0` is step 1.
3. Hence `(f_* f^* α) y = α y * ∑ᶠ x ∈ f⁻¹{y}, length(O_{F,x}) * [κ(x):κ(y)]`; the sum is finite
   (`Scheme.Hom.finite_preimage_singleton`).
4. The remaining content — the sum equals `rankAtStalk (f_* O_X) y` — is the lemma
   `Scheme.Hom.finsum_length_fiber_mul_residueDegree_eq_rankAtStalk` (Stacks 02RH steps 3–4 / Algebra 02M0),
   module `Morphisms/FiniteFiberDegreeRankAtStalk`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Every point of a fiber of a finite morphism has coheight `0`.

Proof: `f.fiber y` is an Artinian scheme (Mathlib instance for `LocallyQuasiFinite f` + `QuasiCompact f`,
both implied by `IsFinite f`), so its underlying space is discrete, in particular `T1`; on a `T1` space
specialization is equality (`specializes_iff_eq`), so every point is maximal for the specialization order
`a ≤ b ↔ b ⤳ a` (`Scheme.le_iff_specializes`), and `Order.coheight_eq_zero` finishes.
Edge case: an empty fiber has no points, nothing to prove. -/
theorem AlgebraicGeometry.Scheme.Hom.coheight_asFiber_eq_zero_of_isFinite {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] (x : X) :
    Order.coheight (f.asFiber x) = 0 := by
  have : DiscreteTopology (f.fiber (f.base x)) := inferInstance
  refine Order.coheight_eq_zero.mpr fun z hz => ?_
  have hspec : z ⤳ f.asFiber x := AlgebraicGeometry.Scheme.le_iff_specializes.mp hz
  rw [specializes_iff_eq] at hspec
  rw [hspec]

/-- Stacks 02RH: for `f : X → Y` finite locally free of degree `d` (here: finite, flat, with
`rank_y (f_* O_X) = d` at every `y`) over a locally Noetherian `Y`, `f_* f^* α = d • α` for every cycle `α`.
Route: see the module docstring; the pointwise computation is done here, the fiber-degree formula is
`Scheme.Hom.finsum_length_fiber_mul_residueDegree_eq_rankAtStalk`. -/
theorem AlgebraicGeometry.properPushforward_flatPullbackCycle_of_finiteLocallyFree
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f]
    [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsLocallyNoetherian Y] (d : ℕ)
    (hd : ∀ y : Y, AlgebraicGeometry.Scheme.Modules.rankAtStalk
      ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) y = d)
    (α : AlgebraicGeometry.AlgebraicCycle Y ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (AlgebraicGeometry.flatPullbackCycle f 0 α) = (d : ℤ) • α := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hfin : (f.base ⁻¹' {y}).Finite := f.finite_preimage_singleton y
  have hL : AlgebraicGeometry.AlgebraicCycle.properPushforward f (AlgebraicGeometry.flatPullbackCycle f 0 α) y =
      ∑ᶠ x ∈ f.base ⁻¹' {y}, AlgebraicGeometry.flatPullbackCycle f 0 α x *
        ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f Order.height Order.height x : ℕ) : ℤ) := rfl
  have hterm : ∀ x ∈ f.base ⁻¹' {y}, AlgebraicGeometry.flatPullbackCycle f 0 α x *
        ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f Order.height Order.height x : ℕ) : ℤ) =
      α y * (((Module.length ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))
          ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))).toNat : ℤ) * (f.residueDegree x : ℤ)) := by
    intro x hx
    have hxy : f.base x = y := hx
    subst hxy
    have hh := AlgebraicGeometry.Scheme.height_apply_eq_of_isIntegralHom f x
    rw [AlgebraicGeometry.flatPullbackCycle_apply,
      if_pos ⟨f.coheight_asFiber_eq_zero_of_isFinite x, by rw [hh, Nat.cast_zero, add_zero]⟩,
      AlgebraicGeometry.AlgebraicCycle.mapCoeff, if_pos hh.symm]
    ring
  rw [hL, finsum_mem_congr rfl hterm, ← mul_finsum_mem' _ _ hfin,
    f.finsum_length_fiber_mul_residueDegree_eq_rankAtStalk y, hd y,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul, mul_comm]

end
