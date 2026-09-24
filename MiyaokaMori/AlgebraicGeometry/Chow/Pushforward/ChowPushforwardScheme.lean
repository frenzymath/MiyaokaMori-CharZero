import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.ChowRatExtend
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.VarietyCyclePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme

/-! # Proper pushforward on Chow groups of schemes

The proper pushforward `f_* : CH_p(X) → CH_p(Y)` on Chow groups of schemes and its version with
ℚ-coefficients (the pushforward of cycles, Stacks 02R4, descended to rational equivalence by
Stacks 02S2). The pushforward on Chow groups of varieties is an `abbrev` of the one defined here. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The pushforward of cycles preserves rational equivalence of `p`-cycles (a `Prop`; it holds by
Stacks 02S2 when `X`, `Y` are locally of finite type over a field). Taking `α = β` shows that it also
implies that the pushforward preserves `Z_p`. -/
def AlgebraicGeometry.PushforwardDescends {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (p : ℕ) : Prop :=
  ∀ α β : AlgebraicGeometry.AlgebraicCycle X ℤ, AlgebraicGeometry.RationallyEquivalent p α β →
    AlgebraicGeometry.RationallyEquivalent p (AlgebraicGeometry.AlgebraicCycle.properPushforward f α)
      (AlgebraicGeometry.AlgebraicCycle.properPushforward f β)

/-- The descent condition implies that the pushforward preserves `Z_p` (take `α = β = c`: `c` is
rationally equivalent to itself if and only if `c ∈ Z_p`). -/
theorem AlgebraicGeometry.properPushforward_mem_cycleSubgroup {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (p : ℕ) (h : AlgebraicGeometry.PushforwardDescends f p)
    (c : ↥(AlgebraicGeometry.cycleSubgroup X p)) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c ∈ AlgebraicGeometry.cycleSubgroup Y p := by
  have hr : AlgebraicGeometry.RationallyEquivalent p
      (c : AlgebraicGeometry.AlgebraicCycle X ℤ) c := by
    exact ⟨c.property, c.property, by simp⟩
  exact (h (c : AlgebraicGeometry.AlgebraicCycle X ℤ) c hr).1

/-- The pushforward of cycles is additive (Mathlib's `AlgebraicCycle.map` is linear in the coefficients). -/
theorem AlgebraicGeometry.properPushforward_add {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (a b : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (a + b) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward f a + AlgebraicGeometry.AlgebraicCycle.properPushforward f b :=
  AlgebraicGeometry.AlgebraicCycle.map_add f Order.height Order.height a b

/-- The pushforward of cycles restricted to `Z_p(X) → Z_p(Y)`. -/
noncomputable def AlgebraicGeometry.cyclePushforwardHom {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (p : ℕ) (h : AlgebraicGeometry.PushforwardDescends f p) :
    ↥(AlgebraicGeometry.cycleSubgroup X p) →+ ↥(AlgebraicGeometry.cycleSubgroup Y p) where
  toFun c := ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward f c, AlgebraicGeometry.properPushforward_mem_cycleSubgroup f p h c⟩
  map_zero' := Subtype.ext (by
    simpa using AlgebraicGeometry.properPushforward_add f (0 : AlgebraicGeometry.AlgebraicCycle X ℤ) 0)
  map_add' a b := Subtype.ext (AlgebraicGeometry.properPushforward_add f a b)

/-- The descent condition implies that the pushforward sends cycles rationally equivalent to zero
(intersected with `Z_p`) to cycles rationally equivalent to zero (the form of Stacks 02S2). -/
theorem AlgebraicGeometry.cyclePushforwardHom_rel {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (p : ℕ) (h : AlgebraicGeometry.PushforwardDescends f p) :
    (AlgebraicGeometry.ratEquivZero X p).addSubgroupOf (AlgebraicGeometry.cycleSubgroup X p) ≤
      ((AlgebraicGeometry.ratEquivZero Y p).addSubgroupOf (AlgebraicGeometry.cycleSubgroup Y p)).comap
        (AlgebraicGeometry.cyclePushforwardHom f p h) := by
  intro x hx
  rw [AddSubgroup.mem_comap]
  apply AddSubgroup.mem_addSubgroupOf.mpr
  have hxrat : (x : AlgebraicGeometry.AlgebraicCycle X ℤ) ∈
      AlgebraicGeometry.ratEquivZero X p :=
    AddSubgroup.mem_addSubgroupOf.mp hx
  have hr : AlgebraicGeometry.RationallyEquivalent p
      (x : AlgebraicGeometry.AlgebraicCycle X ℤ) 0 := by
    exact ⟨x.property, zero_mem _, by simpa using hxrat⟩
  have hp := h (x : AlgebraicGeometry.AlgebraicCycle X ℤ) 0 hr
  have hzero : AlgebraicGeometry.AlgebraicCycle.properPushforward f
      (0 : AlgebraicGeometry.AlgebraicCycle X ℤ) = 0 := by
    unfold AlgebraicGeometry.AlgebraicCycle.properPushforward
    exact AlgebraicGeometry.AlgebraicCycle.map_zero f Order.height Order.height
  change AlgebraicGeometry.AlgebraicCycle.properPushforward f
      (x : AlgebraicGeometry.AlgebraicCycle X ℤ) ∈ AlgebraicGeometry.ratEquivZero Y p
  simpa [hzero] using hp.2.2

open Classical in
/-- The proper pushforward `f_* : CH_p(X) → CH_p(Y)` on Chow groups: the descent of the pushforward of cycles
when it preserves rational equivalence (`PushforwardDescends`, true by Stacks 02S2 over a field), and `0`
otherwise. -/
noncomputable def AlgebraicGeometry.chowPushforward {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (p : ℕ) :
    AlgebraicGeometry.ChowGroup X p →+ AlgebraicGeometry.ChowGroup Y p :=
  if h : AlgebraicGeometry.PushforwardDescends f p then
    QuotientAddGroup.map _ _ (AlgebraicGeometry.cyclePushforwardHom f p h)
      (AlgebraicGeometry.cyclePushforwardHom_rel f p h)
  else 0

/-- The proper pushforward on Chow groups with rational coefficients. -/
noncomputable def AlgebraicGeometry.chowPushforwardRat {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (p : ℕ) :
    AlgebraicGeometry.ChowGroupRat X p →ₗ[ℚ] AlgebraicGeometry.ChowGroupRat Y p :=
  (AlgebraicGeometry.chowPushforward f p).ratExtend

end
