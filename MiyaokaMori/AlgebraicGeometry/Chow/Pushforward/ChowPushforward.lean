import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.VarietyCyclePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure

/-! # Proper pushforward on Chow groups of varieties

The proper pushforward `f_* : A_i(X) → A_i(Y)` on Chow groups (Fulton, Intersection Theory, §1.4). It is
the scheme-level `AlgebraicGeometry.chowPushforward f i` (Stacks 02S2 descent), written as an `abbrev`.

The scheme-level `chowPushforward` has a fallback branch `if PushforwardDescends f p then … else 0` (the
same pattern as `firstChernClass`); a proper morphism between varieties always takes the positive branch
(`chowPushforward_descends`): the scheme form of Stacks 02S2, `properPushforward_rationallyEquivalent`,
requires `f` to be a `k`-morphism with both sides locally of finite type over `k`; `f` need not be a
`k`-morphism, but replacing the `k`-structure of `X` by the one induced from `Y` through `f`,
`⟨f ≫ Y.structureMorphism⟩`, keeps `X` locally of finite type over `k` and makes `f` a `k`-morphism, while
`PushforwardDescends` only involves the underlying schemes and `f`. The evaluation lemma
`chowPushforward_mk_variety` reads `f_* [c] = [cyclePushforward f i c]`, where the underlying cycle of
`cyclePushforward` is by definition `AlgebraicGeometry.AlgebraicCycle.properPushforward f c`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The pushforward along a proper morphism of varieties preserves rational equivalence (Stacks 02S2): the
scheme-level `chowPushforward` takes its positive branch. `f` need not be a `k`-morphism: after replacing
the `k`-structure of the source by `⟨f ≫ Y.structureMorphism⟩`, `f` is a `k`-morphism. -/
theorem chowPushforward_descends {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] (i : ℕ) :
    AlgebraicGeometry.PushforwardDescends f i := by
  let : X.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨f ≫ Y.structureMorphism⟩
  let : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  let : AlgebraicGeometry.LocallyOfFiniteType
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType (f ≫ Y.structureMorphism))
  intro β γ hβγ
  exact AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent
    (k := k) f i β γ hβγ

/-- The proper pushforward `f_* : A_i(X) → A_i(Y)` on Chow groups: the scheme-level
`AlgebraicGeometry.chowPushforward`. -/
abbrev chowPushforward {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] (i : ℕ) :
    ChowGroup X i →+ ChowGroup Y i :=
  AlgebraicGeometry.chowPushforward f i

/-- Evaluation: `f_* [c] = [f_* c]`, where the cycle-level pushforward is `cyclePushforward`. -/
theorem chowPushforward_mk_variety {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] (i : ℕ) (c : CycleGroup X i) :
    chowPushforward f i (AlgebraicGeometry.ChowGroup.mk c)
      = AlgebraicGeometry.ChowGroup.mk (cyclePushforward f i c) := by
  have h := AlgebraicGeometry.chowPushforward_mk f i (chowPushforward_descends f i) c
  change AlgebraicGeometry.chowPushforward f i (AlgebraicGeometry.ChowGroup.mk c) =
    AlgebraicGeometry.ChowGroup.mk (cyclePushforward f i c)
  rw [h]
  congr 1

end
