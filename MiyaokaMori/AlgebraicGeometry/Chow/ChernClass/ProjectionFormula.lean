import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapDivisorEqFirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassMk
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward

/-! # The projection formula

The projection formula `f_*(f^*D ∩ [Z]) = D ∩ f_*[Z]` (Fulton, Intersection Theory, Prop. 2.3(c)),
the main tool for the degree identity `-K_X · f_*[C] = deg f^*T_X` of §1 of the paper. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.chowPushforward_firstChernClass_pullback {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : X ⟶ Y) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper p]
    (L : Y.Modules) [L.IsLineBundle] (d : ℕ) (α : AlgebraicGeometry.ChowGroup X (d + 1)) :
    AlgebraicGeometry.chowPushforward p d
        (AlgebraicGeometry.firstChernClass ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1) α)
      = AlgebraicGeometry.firstChernClass L (d + 1) (AlgebraicGeometry.chowPushforward p (d + 1) α) := by
  let : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let : AlgebraicGeometry.IsLocallyNoetherian Y :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective α
  change AlgebraicGeometry.chowPushforward p d
      (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1)
        (AlgebraicGeometry.ChowGroup.mk a)) =
    AlgebraicGeometry.firstChernClass L (d + 1)
      (AlgebraicGeometry.chowPushforward p (d + 1) (AlgebraicGeometry.ChowGroup.mk a))
  have hdesc : AlgebraicGeometry.PushforwardDescends p (d + 1) := by
    intro β γ hβγ
    exact AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent
      (k := k) p (d + 1) β γ hβγ
  have hmem := AlgebraicGeometry.properPushforward_mem_cycleSubgroup p (d + 1) hdesc a
  have hpush : AlgebraicGeometry.chowPushforward p (d + 1)
      (AlgebraicGeometry.ChowGroup.mk a) =
      AlgebraicGeometry.ChowGroup.mk
        ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward p a, hmem⟩ := by
    have hp : AlgebraicGeometry.chowPushforward p (d + 1) =
        QuotientAddGroup.map _ _
          (AlgebraicGeometry.cyclePushforwardHom p (d + 1) hdesc)
          (AlgebraicGeometry.cyclePushforwardHom_rel p (d + 1) hdesc) := by
      unfold AlgebraicGeometry.chowPushforward
      exact dif_pos hdesc
    rw [hp]
    rfl
  rw [AlgebraicGeometry.firstChernClass_mk (k := k) _ (Nat.succ_pos d), hpush,
    AlgebraicGeometry.firstChernClass_mk (k := k) _ (Nat.succ_pos d)]
  exact AlgebraicGeometry.chowPushforward_firstChernCapCycle_pullback
    (k := k) p L d a a.2

/-- **The projection formula** for a proper morphism `f : X → Y` of varieties and Cartier divisors
`D` on `Y`, `D'` on `X` with `O_X(D') ≅ f^*O_Y(D)`: `f_*(D' ∩ Z) = D ∩ f_*Z`. -/
theorem projection_formula {k : Type*} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] (D : CartierDivisor Y) (D' : CartierDivisor X)
    (hD' : Nonempty (D'.lineBundle.toModules
      ≅ (AlgebraicGeometry.Scheme.Modules.pullback f).obj D.lineBundle.toModules))
    (i : ℕ) (Z : CycleGroup X (i + 1)) :
    chowPushforward f i (capDivisor D' i Z) = capDivisor D i (cyclePushforward f (i + 1) Z) := by
  let : AlgebraicGeometry.Scheme.Modules.IsLineBundle
      (X := X.toScheme) D'.lineBundle.toModules := by
    refine ⟨fun x ↦ ?_⟩
    exact SheafOfModules.IsLineBundle.locally_trivial
      (M := D'.lineBundle.toModules) x
  let : AlgebraicGeometry.Scheme.Modules.IsLineBundle
      (X := Y.toScheme) D.lineBundle.toModules := by
    refine ⟨fun y ↦ ?_⟩
    exact SheafOfModules.IsLineBundle.locally_trivial
      (M := D.lineBundle.toModules) y
  rw [capDivisor_eq_firstChernClass, capDivisor_eq_firstChernClass]
  obtain ⟨e⟩ := hD'
  rw [AlgebraicGeometry.firstChernClass_congr D'.lineBundle.toModules
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj D.lineBundle.toModules) e i]
  let : X.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨f ≫ Y.structureMorphism⟩
  let : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  let : AlgebraicGeometry.LocallyOfFiniteType
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType (f ≫ Y.structureMorphism))
  unfold chowPushforward
  rw [AlgebraicGeometry.chowPushforward_firstChernClass_pullback (k := k)]
  congr 1
  exact chowPushforward_mk_variety f (i + 1) Z

end
