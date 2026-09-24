import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.ChowGroupRatCongr
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.CapCommutes
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassRat
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator

/-! # Pushforward of a power of the tautological class: the algebraic part

The purely algebraic part of the pushforward computation `π_*(H^{s−1} ∩ [Y]) = v · [C]`:

* `AlgebraicGeometry.ChowGroupRat.congr_apply_ratDivisorOp`: the dimension transport `congr` commutes with divisor
  operators;
* `AlgebraicGeometry.RatDivisorOp.comp_capPow_of_comm`: an operator `D` commuting with `H` in each dimension
  commutes with the power `H^e` (the algebraic skeleton of "`c_1(π^*O_C(c))` commutes with `H^{s-1}`" in the proof
  of Proposition 2.4 of the paper; Fulton 2.4.2 and `ℚ`-linearity);
* `AlgebraicGeometry.ratDivisorOpOfLineBundle_comm`: the `ℚ`-divisor operators of two line bundles commute (the
  `ℚ`-version of `firstChernClass_comm`);
* `AlgebraicGeometry.chowPushforwardRat_ratDivisorOpOfLineBundle_pullback`,
  `AlgebraicGeometry.chowPushforwardRat_capPow_pullback`: the `ℚ`-version of the projection formula
  `π_*(c_1(π^*L) ∩ α) = c_1(L) ∩ π_*α` and its `e`-fold iterate (the `ℚ`-version of
  `chowPushforward_firstChernClass_pullback`);
* `AlgebraicGeometry.isProper_fiberι_of_isClosed`: the embedding of the scheme-theoretic fiber at a closed point is
  a closed immersion, hence proper.

The paper only takes degrees; the formulation at the level of classes is ours.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The dimension transport `ChowGroupRat.congr` commutes with divisor operators (`congr` is transport along an
equality; after `subst` this is `rfl`). -/
theorem AlgebraicGeometry.ChowGroupRat.congr_apply_ratDivisorOp {X : AlgebraicGeometry.Scheme.{u}}
    (H : AlgebraicGeometry.RatDivisorOp X) {p q : ℕ} (h : p = q) (h' : p + 1 = q + 1)
    (z : AlgebraicGeometry.ChowGroupRat X (p + 1)) :
    H q (AlgebraicGeometry.ChowGroupRat.congr X h' z)
      = AlgebraicGeometry.ChowGroupRat.congr X h (H p z) := by
  subst h
  rfl

/-- Two dimension transports compose to one. -/
theorem AlgebraicGeometry.ChowGroupRat.congr_congr {X : AlgebraicGeometry.Scheme.{u}} {p q r : ℕ}
    (h₁ : p = q) (h₂ : q = r) (z : AlgebraicGeometry.ChowGroupRat X p) :
    AlgebraicGeometry.ChowGroupRat.congr X h₂ (AlgebraicGeometry.ChowGroupRat.congr X h₁ z)
      = AlgebraicGeometry.ChowGroupRat.congr X (h₁.trans h₂) z := by
  subst h₁; subst h₂
  rfl

/-- Dimension transport sends the fundamental class to the fundamental class (proof irrelevance for the
dimension). -/
theorem AlgebraicGeometry.ChowGroupRat.congr_fundamentalClassRat {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] {p q : ℕ} (h : p = q) (hp : X.dimension = p) (hq : X.dimension = q) :
    AlgebraicGeometry.ChowGroupRat.congr X h (AlgebraicGeometry.fundamentalClassRat X p hp)
      = AlgebraicGeometry.fundamentalClassRat X q hq := by
  subst h
  rfl

/-- Dimension transport commutes with `ℚ`-pushforward. -/
theorem AlgebraicGeometry.chowPushforwardRat_congr {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] {p q : ℕ} (h : p = q)
    (z : AlgebraicGeometry.ChowGroupRat X p) :
    AlgebraicGeometry.chowPushforwardRat f q (AlgebraicGeometry.ChowGroupRat.congr X h z)
      = AlgebraicGeometry.ChowGroupRat.congr Y h (AlgebraicGeometry.chowPushforwardRat f p z) := by
  subst h
  rfl

/-- If `D` commutes with `H` in every dimension, then `D` commutes with the power `H^e`: `D (H^e z) = H^e (D z)`
(dimensions transported by `congr`). -/
theorem AlgebraicGeometry.RatDivisorOp.comp_capPow_of_comm {X : AlgebraicGeometry.Scheme.{u}}
    (D H : AlgebraicGeometry.RatDivisorOp X)
    (hcomm : ∀ d, (D d).comp (H (d + 1)) = (H d).comp (D (d + 1))) (e : ℕ) :
    ∀ (d : ℕ) (z : AlgebraicGeometry.ChowGroupRat X (d + 1 + e)),
      D d (AlgebraicGeometry.RatDivisorOp.capPow H e (d + 1) z)
        = AlgebraicGeometry.RatDivisorOp.capPow H e d
            (D (d + e) (AlgebraicGeometry.ChowGroupRat.congr X (by omega) z)) := by
  induction e with
  | zero =>
      intro d z
      rfl
  | succ e ih =>
      intro d z
      show D d (AlgebraicGeometry.RatDivisorOp.capPow H e (d + 1) (H (d + 1 + e) z))
        = AlgebraicGeometry.RatDivisorOp.capPow H e d
            (H (d + e) (D (d + e + 1) (AlgebraicGeometry.ChowGroupRat.congr X (by omega) z)))
      rw [ih d (H (d + 1 + e) z)]
      congr 1
      have h1 := AlgebraicGeometry.ChowGroupRat.congr_apply_ratDivisorOp H
        (p := d + 1 + e) (q := d + e + 1) (by omega) (by omega) z
      rw [← h1]
      exact LinearMap.congr_fun (hcomm (d + e)) _

/-- The `ℚ`-divisor operators of two line bundles commute (`firstChernClass_comm` extended along `ratExtend`). -/
theorem AlgebraicGeometry.ratDivisorOpOfLineBundle_comm {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (d : ℕ) :
    (AlgebraicGeometry.ratDivisorOpOfLineBundle L d).comp
        (AlgebraicGeometry.ratDivisorOpOfLineBundle L' (d + 1))
      = (AlgebraicGeometry.ratDivisorOpOfLineBundle L' d).comp
        (AlgebraicGeometry.ratDivisorOpOfLineBundle L (d + 1)) := by
  have hcomp :
      (AlgebraicGeometry.firstChernClass L (d + 1)).toIntLinearMap ∘ₗ
          (AlgebraicGeometry.firstChernClass L' (d + 2)).toIntLinearMap =
        (AlgebraicGeometry.firstChernClass L' (d + 1)).toIntLinearMap ∘ₗ
          (AlgebraicGeometry.firstChernClass L (d + 2)).toIntLinearMap := by
    ext z
    exact DFunLike.congr_fun (AlgebraicGeometry.firstChernClass_comm (k := k) L L' d) z
  change (LinearMap.baseChange ℚ (AlgebraicGeometry.firstChernClass L (d + 1)).toIntLinearMap).comp
      (LinearMap.baseChange ℚ (AlgebraicGeometry.firstChernClass L' (d + 2)).toIntLinearMap)
    = (LinearMap.baseChange ℚ (AlgebraicGeometry.firstChernClass L' (d + 1)).toIntLinearMap).comp
      (LinearMap.baseChange ℚ (AlgebraicGeometry.firstChernClass L (d + 2)).toIntLinearMap)
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hcomp]

/-- The `ℚ`-version of the projection formula: `π_*(c_1(π^*L) ∩ z) = c_1(L) ∩ π_*z`. -/
theorem AlgebraicGeometry.chowPushforwardRat_ratDivisorOpOfLineBundle_pullback {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : X ⟶ Y) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper p]
    (L : Y.Modules) [L.IsLineBundle] (d : ℕ) (z : AlgebraicGeometry.ChowGroupRat X (d + 1)) :
    AlgebraicGeometry.chowPushforwardRat p d
        (AlgebraicGeometry.ratDivisorOpOfLineBundle
          ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) d z) =
      AlgebraicGeometry.ratDivisorOpOfLineBundle L d
        (AlgebraicGeometry.chowPushforwardRat p (d + 1) z) := by
  have hcomp :
      (AlgebraicGeometry.chowPushforward p d).toIntLinearMap ∘ₗ
          (AlgebraicGeometry.firstChernClass
            ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L)
            (d + 1)).toIntLinearMap =
        (AlgebraicGeometry.firstChernClass L (d + 1)).toIntLinearMap ∘ₗ
          (AlgebraicGeometry.chowPushforward p (d + 1)).toIntLinearMap := by
    ext z
    exact AlgebraicGeometry.chowPushforward_firstChernClass_pullback (k := k) p L d z
  change
    ((LinearMap.baseChange ℚ
        (AlgebraicGeometry.chowPushforward p d).toIntLinearMap).comp
      (LinearMap.baseChange ℚ (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L)
        (d + 1)).toIntLinearMap)) z =
    ((LinearMap.baseChange ℚ
        (AlgebraicGeometry.firstChernClass L (d + 1)).toIntLinearMap).comp
      (LinearMap.baseChange ℚ
        (AlgebraicGeometry.chowPushforward p (d + 1)).toIntLinearMap)) z
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hcomp]

/-- The `e`-fold iterate of the projection formula: `π_*(c_1(π^*L)^e ∩ z) = c_1(L)^e ∩ π_*z`. -/
theorem AlgebraicGeometry.chowPushforwardRat_capPow_pullback {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : X ⟶ Y) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper p]
    (L : Y.Modules) [L.IsLineBundle] (e : ℕ) :
    ∀ (d : ℕ) (z : AlgebraicGeometry.ChowGroupRat X (d + e)),
      AlgebraicGeometry.chowPushforwardRat p d
          (AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L)) e d z) =
        AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle L) e d
          (AlgebraicGeometry.chowPushforwardRat p (d + e) z) := by
  induction e with
  | zero =>
      intro d z
      rfl
  | succ e ih =>
      intro d z
      show AlgebraicGeometry.chowPushforwardRat p d
          (AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L)) e d
            (AlgebraicGeometry.ratDivisorOpOfLineBundle
              ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + e) z)) =
        AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle L) e d
          (AlgebraicGeometry.ratDivisorOpOfLineBundle L (d + e)
            (AlgebraicGeometry.chowPushforwardRat p (d + e + 1) z))
      rw [ih d, AlgebraicGeometry.chowPushforwardRat_ratDivisorOpOfLineBundle_pullback (k := k) p L (d + e) z]

/-- The embedding `f.fiberι c` of the scheme-theoretic fiber at a closed point is a closed immersion
(`Spec κ(c) → X` is a closed immersion at a closed point, and closed immersions are stable under base change),
hence proper. -/
theorem AlgebraicGeometry.isProper_fiberι_of_isClosed {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) (c : X) (hc : IsClosed ({c} : Set X)) :
    AlgebraicGeometry.IsProper (f.fiberι c) := by
  have h1 : AlgebraicGeometry.IsClosedImmersion (X.fromSpecResidueField c) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hc
  have h2 : AlgebraicGeometry.IsClosedImmersion
      (CategoryTheory.Limits.pullback.fst f (X.fromSpecResidueField c)) := inferInstance
  have h3 : AlgebraicGeometry.IsClosedImmersion (f.fiberι c) := h2
  infer_instance

end
