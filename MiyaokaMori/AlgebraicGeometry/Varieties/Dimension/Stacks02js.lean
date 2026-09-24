import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02fx
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02js_StalkDimAdditive
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02js_LocalDimOverField

/-! # Additivity of local dimension along a flat morphism (Stacks 02JS)

Stacks 02JS: if `f` is flat and locally of finite type and `x ↦ y`, then
`dim_x(X) = dim_y(Y) + dim_x(X_y)`.

## Proof sketch

Write `y := f x`, `g : Y → Spec k` for the structure morphism, `X_y` for the fibre and `x'` for `x`
as a point of `X_y`. All local dimensions below are the untruncated ones
`⨅_{U ∋ z} dim U ∈ WithBot ℕ∞`; they are finite natural numbers here
(`coe_localDimension_eq_iInf_of_ne_top`), so the truncated `localDimension` identity follows.

1. Local rings (Stacks 00ON + 0HA1; `ringKrullDim_stalk_eq_add_fiber_stalk`):
   `dim 𝒪_{X,x} = dim 𝒪_{Y,y} + dim 𝒪_{X_y,x'}` (`f` is flat, `X`, `Y` locally Noetherian since
   locally of finite type over a field).
2. Stacks 0A21(10) (= 02FX for the structure morphisms;
   `iInf_topologicalKrullDim_opens_eq_stalk_add_trdeg_over_field`):
   `dim_x X = dim 𝒪_{X,x} + trdeg_{κ(pt)} κ(x)`, `dim_y Y = dim 𝒪_{Y,y} + trdeg_{κ(pt)} κ(y)`,
   where `pt` is the point of `Spec k`; and 02FX for `f`: `dim_{x'} X_y = dim 𝒪_{X_y,x'} + trdeg_{κ(y)} κ(x)`.
3. Transcendence degree is additive in the tower `κ(pt) → κ(y) → κ(x)` (Stacks 030H,
   `Algebra.trdeg_add_eq`); the tower is compatible because
   `(f ≫ g).residueFieldMap x = g.residueFieldMap y ≫ f.residueFieldMap x`.
4. Add up: `dim_x X = dim_y Y + dim_{x'} X_y`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 02JS with `S = Spec k`: `Y` is locally of finite type over the field `k` (and `f` is
locally of finite type, so `X` is locally of finite type over `k` as well). -/

theorem AlgebraicGeometry.localDimension_flat_additive {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFiniteType f] (x : X) :
    localDimension X x = localDimension Y (f.base x) +
      localDimension (f.fiber (f.base x)) (AlgebraicGeometry.Scheme.Hom.asFiber f x) := by
  set g := Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k) with hg
  have : AlgebraicGeometry.LocallyOfFiniteType (f ≫ g) := inferInstance
  have : AlgebraicGeometry.IsLocallyNoetherian Y :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian g
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (f ≫ g)
  -- residue fields and the tower κ(pt) → κ(y) → κ(x)
  let _ : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
      (Y.residueField (f.base x)) :=
    (g.residueFieldMap (f.base x)).hom.toAlgebra
  let _ : Algebra ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
      (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  have : IsScalarTower ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
      (Y.residueField (f.base x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have h := congrArg
        (fun h : (AlgebraicGeometry.Spec (CommRingCat.of k)).residueField ((f ≫ g).base x) ⟶
          X.residueField x => h r)
        (AlgebraicGeometry.Scheme.residueFieldMap_comp f g x)
      exact h
  have : FaithfulSMul ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
      (Y.residueField (f.base x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  have : FaithfulSMul (Y.residueField (f.base x)) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  have hT := trdeg_add_eq
    ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
    (Y.residueField (f.base x)) (A := X.residueField x)
  have hT' : (Cardinal.toENat (Algebra.trdeg
      ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
      (X.residueField x)) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg
        ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
        (Y.residueField (f.base x))) : WithBot ℕ∞) +
      (Cardinal.toENat (Algebra.trdeg (Y.residueField (f.base x)) (X.residueField x)) : WithBot ℕ∞) := by
    rw [← hT, map_add, WithBot.coe_add]
  -- step 2: the three dimension formulas (0A21(10) / 02FX)
  have hX : (⨅ U ∈ {U : X.Opens | x ∈ U}, topologicalKrullDim U) =
      ringKrullDim (X.presheaf.stalk x) +
        (Cardinal.toENat (Algebra.trdeg
          ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
          (X.residueField x)) : WithBot ℕ∞) :=
    AlgebraicGeometry.iInf_topologicalKrullDim_opens_eq_stalk_add_trdeg_over_field (f ≫ g) x
  have hY : (⨅ U ∈ {U : Y.Opens | f.base x ∈ U}, topologicalKrullDim U) =
      ringKrullDim (Y.presheaf.stalk (f.base x)) +
        (Cardinal.toENat (Algebra.trdeg
          ((AlgebraicGeometry.Spec (CommRingCat.of k)).residueField (g.base (f.base x)))
          (Y.residueField (f.base x))) : WithBot ℕ∞) :=
    AlgebraicGeometry.iInf_topologicalKrullDim_opens_eq_stalk_add_trdeg_over_field g (f.base x)
  have hF : (⨅ U ∈ {U : (f.fiber (f.base x)).Opens | f.asFiber x ∈ U}, topologicalKrullDim U) =
      ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) +
        (Cardinal.toENat (Algebra.trdeg (Y.residueField (f.base x)) (X.residueField x)) : WithBot ℕ∞) :=
    AlgebraicGeometry.iInf_topologicalKrullDim_fiber_eq_stalk_add_trdeg f x
  -- step 1: local rings
  have hS := AlgebraicGeometry.ringKrullDim_stalk_eq_add_fiber_stalk f x
  -- truncations
  have hXtop := AlgebraicGeometry.iInf_topologicalKrullDim_opens_ne_top_of_locallyOfFiniteType (f ≫ g) x
  have tX := AlgebraicGeometry.coe_localDimension_eq_iInf_of_ne_top x hXtop
  have tY := AlgebraicGeometry.coe_localDimension_eq_iInf_of_ne_top (f.base x)
    (AlgebraicGeometry.iInf_topologicalKrullDim_opens_ne_top_of_locallyOfFiniteType g (f.base x))
  have tF := AlgebraicGeometry.coe_localDimension_eq_iInf_of_ne_top (f.asFiber x)
    (ne_top_of_le_ne_top hXtop (AlgebraicGeometry.iInf_topologicalKrullDim_fiber_le f x))
  -- step 4: add up
  have key : ((localDimension X x : ℕ) : WithBot ℕ∞) =
      ((localDimension Y (f.base x) + localDimension (f.fiber (f.base x)) (f.asFiber x) : ℕ) :
        WithBot ℕ∞) := by
    rw [Nat.cast_add, ← tX, ← tY, ← tF, hX, hY, hF, hS, hT']
    exact add_add_add_comm _ _ _ _
  exact_mod_cast key

end
