import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureDimensionTrdeg
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldBaseFiniteType
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldBaseTower

/-! # Proper pushforward preserves the dimension of cycles

Proper pushforward sends `Z_i(X)` into `Z_i(Y)` (components whose dimension drops get coefficient `0`,
so the pushforward is still purely `i`-dimensional); e.g. `f_*[C] ∈ Z_1(X)` in Theorem 1.1 of the
paper, and the one-cycles `Φ_*`, `b_*` of §4. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The proper pushforward of an `i`-cycle is an `i`-cycle. -/
theorem properPushforward_mem_cycleGroup {k : Type*} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] {i : ℕ}
    (c : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) (hc : c ∈ CycleGroup X i) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c ∈ CycleGroup Y i := by
  intro y hy
  have happ : AlgebraicGeometry.AlgebraicCycle.properPushforward f c y =
      ∑ᶠ x ∈ f.base ⁻¹' {y}, c x *
        ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f (Order.height (α := X.toScheme))
          (Order.height (α := Y.toScheme)) x : ℕ) : ℤ) := rfl
  rw [happ] at hy
  obtain ⟨x, (hxy : f.base x = y), hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  have hax : c x ≠ 0 := fun h => hx (by simp [h])
  have hdim : Order.height x = Order.height (f.base x) := by
    by_contra h
    exact hx (by simp [AlgebraicGeometry.AlgebraicCycle.mapCoeff, h])
  rw [← hxy, ← hdim]
  exact hc x hax

/-- The substantial part (Stacks 02R4 / Fulton §1.4): for a `k`-morphism of varieties, at a point
preserving the dimension (`height x = height f(x)`, i.e. `dim closure{x} = dim closure{f x}`) the
residue field extension is finite, so the `residueDegree` in the pushforward coefficient is the genuine
degree `[κ(x):κ(f x)] ≥ 1` and not Mathlib's fallback value `0` for infinite extensions. This is the
predicate `FiniteDimensionPreservingResidues`, proved for varieties in terms of `Order.height`.
Argument: `κ(x)/κ(f x)` is finitely generated, `dim closure{x} = trdeg_k κ(x)`, the two transcendence
degrees agree ⇒ algebraic ⇒ finite. -/
theorem properPushforward_residueField_finite {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (x : X.toScheme) (hx : Order.height x = Order.height (f.base x)) :
    (f.residueFieldMap x).hom.Finite := by
  classical
  let S := AlgebraicGeometry.Spec (CommRingCat.of k)
  let XO : AlgebraicGeometry.Proj.SchemeOver k := ⟨X.toScheme, X.toScheme ↘ S⟩
  let YO : AlgebraicGeometry.Proj.SchemeOver k := ⟨Y.toScheme, Y.toScheme ↘ S⟩
  have hF : f ≫ YO.toBase = XO.toBase := comp_over f S
  letI algkX : Algebra k (X.toScheme.residueField x) :=
    (AlgebraicGeometry.Intersection.pointBaseMap XO.toBase x).hom.toAlgebra
  letI algkY : Algebra k (Y.toScheme.residueField (f.base x)) :=
    (AlgebraicGeometry.Intersection.pointBaseMap YO.toBase (f.base x)).hom.toAlgebra
  letI algYX : Algebra (Y.toScheme.residueField (f.base x)) (X.toScheme.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  haveI htower : IsScalarTower k (Y.toScheme.residueField (f.base x))
      (X.toScheme.residueField x) := AlgebraicGeometry.Intersection.residueFieldBase_isScalarTower (X := XO) (Y := YO) f hF x
  haveI hfsX : FaithfulSMul k (X.toScheme.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap k (X.toScheme.residueField x)).injective
  haveI hfsY : FaithfulSMul k (Y.toScheme.residueField (f.base x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap k (Y.toScheme.residueField (f.base x))).injective
  haveI hfsYX : FaithfulSMul (Y.toScheme.residueField (f.base x)) (X.toScheme.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (Y.toScheme.residueField (f.base x)) (X.toScheme.residueField x)).injective
  -- (1) the transcendence degrees of the two residue fields are the heights of the two points (Stacks 0A21(6))
  have hXd := MiyaokaMori.PointClosureTrdeg.pointClosureDimension_eq_trdeg XO x
  have hYd := MiyaokaMori.PointClosureTrdeg.pointClosureDimension_eq_trdeg YO (f.base x)
  rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_height] at hXd hYd
  have hXe : (Order.height x : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg k (X.toScheme.residueField x)) := WithBot.coe_injective hXd
  have hYe : (Order.height (f.base x) : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg k (Y.toScheme.residueField (f.base x))) :=
    WithBot.coe_injective hYd
  have hEq : Cardinal.toENat (Algebra.trdeg k (X.toScheme.residueField x)) =
      Cardinal.toENat (Algebra.trdeg k (Y.toScheme.residueField (f.base x))) := by
    rw [← hXe, ← hYe, hx]
  -- (2) both transcendence degrees are finite (locally of finite type over `k` ⇒ finite transcendence degree)
  haveI : FinTrdeg k (X.toScheme.residueField x) :=
    AlgebraicGeometry.Intersection.pointBaseMap_finTrdeg XO.toBase x
  haveI : FinTrdeg k (Y.toScheme.residueField (f.base x)) :=
    AlgebraicGeometry.Intersection.pointBaseMap_finTrdeg YO.toBase (f.base x)
  have hfinX : Algebra.trdeg k (X.toScheme.residueField x) < Cardinal.aleph0 :=
    trdeg_lt_aleph0 k _
  have hfinY : Algebra.trdeg k (Y.toScheme.residueField (f.base x)) < Cardinal.aleph0 :=
    trdeg_lt_aleph0 k _
  -- (3) additivity of trdeg ⇒ the transcendence degree of `κ(x)/κ(f x)` is `0`
  have hadd := trdeg_add_eq k (Y.toScheme.residueField (f.base x))
    (A := X.toScheme.residueField x)
  have hfinYX : Algebra.trdeg (Y.toScheme.residueField (f.base x))
      (X.toScheme.residueField x) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt ?_ hfinX
    rw [← hadd]
    exact le_add_self
  obtain ⟨p, hp⟩ := Cardinal.lt_aleph0.mp hfinY
  obtain ⟨q, hq⟩ := Cardinal.lt_aleph0.mp hfinX
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hfinYX
  rw [hp, hq, hr] at hadd
  have hpqr : p + r = q := by exact_mod_cast hadd
  have hqp : q = p := by
    have := hEq
    rw [hp, hq] at this
    simpa using this
  have hr0 : r = 0 := by omega
  haveI halg : Algebra.IsAlgebraic (Y.toScheme.residueField (f.base x))
      (X.toScheme.residueField x) := by
    refine trdeg_eq_zero_iff.mp ?_
    rw [hr, hr0]
    simp
  -- (4) algebraic + essentially of finite type ⇒ finite
  haveI hess : Algebra.EssFiniteType (Y.toScheme.residueField (f.base x))
      (X.toScheme.residueField x) :=
    AlgebraicGeometry.Intersection.overBase_residueFieldMap_essFiniteType (X := XO) (Y := YO) f hF x
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic
    (F := Y.toScheme.residueField (f.base x)) (E := X.toScheme.residueField x)

theorem properPushforward_residueDegree_pos {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (x : X.toScheme) (hx : Order.height x = Order.height (f.base x)) :
    0 < f.residueDegree x := by
  letI : Algebra (Y.toScheme.residueField (f.base x)) (X.toScheme.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  haveI : Module.Finite (Y.toScheme.residueField (f.base x)) (X.toScheme.residueField x) :=
    properPushforward_residueField_finite f x hx
  exact Module.finrank_pos

end
