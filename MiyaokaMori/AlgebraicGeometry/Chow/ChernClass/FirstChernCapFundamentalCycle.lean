import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointGeneric
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureTransport
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ClosedImmersionPushforwardRatEquiv
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointClosurePushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5

/-! # The cap with the fundamental cycle of an integral scheme (cycle level)

The cycle-level part of the comparison `c_1(L) ∩ [X] = [div_L(s)]`:
(F1) on an integral scheme, `firstChernCapCycleAux L (m+1) [X] = firstChernCapPoint L η`;
(PC) on an integral scheme, the principal cycle `div(g)` is an `IsRatEquivGen X m η` (hence rationally
trivial); together with four small lemmas on `topologicalKrullDim` and the height of the generic point
when `dim X = m + 1`. This module imports nothing from the `firstChernClass` layer, so that the proof
of Stacks 02ST can use (F1)/(PC).

Source: Stacks 02SJ, 02SH.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace AlgebraicGeometry
open MiyaokaMori.FirstChernCapPointClosurePushforward MiyaokaMori.FirstChernCapPointGeneric
  MiyaokaMori.PointClosureTransport MiyaokaMori.ClosedImmersionPushforward


theorem topologicalKrullDim_ne_top_of_dimension_pos {X : Scheme.{u}} {m : ℕ}
    (hX : X.dimension = m + 1) : topologicalKrullDim X ≠ ⊤ := by
  intro h
  unfold Scheme.dimension at hX
  rw [h] at hX
  have : (WithBot.unbotD 0 (⊤ : WithBot ℕ∞)).toNat = 0 := by
    show (⊤ : ℕ∞).toNat = 0
    exact ENat.toNat_top
  omega

theorem topologicalKrullDim_ne_bot_of_isIntegral {X : Scheme.{u}} [IsIntegral X] :
    topologicalKrullDim X ≠ ⊥ := by
  unfold topologicalKrullDim
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨Set.univ, (IrreducibleSpace.isIrreducible_univ X), isClosed_univ⟩⟩
  exact Order.krullDim_ne_bot_iff.mpr inferInstance

theorem topologicalKrullDim_eq_of_dimension_pos {X : Scheme.{u}} [IsIntegral X] {m : ℕ}
    (hX : X.dimension = m + 1) : topologicalKrullDim X = ((m + 1 : ℕ) : WithBot ℕ∞) := by
  rw [X.dimension_spec topologicalKrullDim_ne_bot_of_isIntegral
    (topologicalKrullDim_ne_top_of_dimension_pos hX), hX]

theorem height_genericPoint_of_dimension_pos {X : Scheme.{u}} [IsIntegral X] {m : ℕ}
    (hX : X.dimension = m + 1) : Order.height (genericPoint X) = ((m + 1 : ℕ) : ℕ∞) := by
  have hk : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints X _ _ _ : TopologicalSpace.IrreducibleCloseds X ≃o X)).symm
  have h1 : ((Order.height (⊤ : X) : ℕ∞) : WithBot ℕ∞) = Order.krullDim X :=
    Order.height_top_eq_krullDim
  rw [hk, topologicalKrullDim_eq_of_dimension_pos hX] at h1
  have h2 : Order.height (⊤ : X) = ((m + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
  exact h2

/-- (F1) `c_1(L) ∩ [X]` (the cycle-level linear extension) is the single-point contribution of the
generic point. -/
theorem firstChernCapCycleAux_fundamentalCycle_of_isIntegral {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] {m : ℕ}
    (hX : X.dimension = m + 1) :
    firstChernCapCycleAux L (m + 1) (X.fundamentalCycle (m + 1)) =
      firstChernCapPoint L (genericPoint X) := by
  classical
  have hfund : ∀ x : X, X.fundamentalCycle (m + 1) x = if x = genericPoint X then 1 else 0 := by
    intro x
    have h := congrFun (X.fundamentalCycle_of_isIntegral
      (topologicalKrullDim_ne_top_of_dimension_pos hX)) x
    rw [hX] at h
    rw [h]
  ext z
  show (∑ᶠ w : X, firstChernCapTerm L (m + 1) (X.fundamentalCycle (m + 1)) z w) = _
  rw [finsum_eq_single _ (genericPoint X)]
  · unfold firstChernCapTerm
    rw [if_pos (height_genericPoint_of_dimension_pos hX), hfund, if_pos rfl, one_mul]
  · intro w hw
    unfold firstChernCapTerm
    rw [hfund, if_neg hw, zero_mul, ite_self]

/-- (PC) On an integral scheme, a principal cycle is a generator in the sense of Stacks 02RW (for `w = η`). -/
theorem isRatEquivGen_principalCycle {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {m : ℕ} (hη : Order.height (genericPoint X) = ((m + 1 : ℕ) : ℕ∞)) (g : X.functionFieldˣ) :
    IsRatEquivGen X m (genericPoint X) (X.principalCycle g) := by
  have hLN : IsLocallyNoetherian (X.pointClosure (genericPoint X)) :=
    Scheme.isLocallyNoetherian_pointClosure _
  obtain ⟨f', hf'⟩ := exists_principalCycle_eq_properPushforward_iso
    (inv (X.pointClosureι (genericPoint X))) g
  refine ⟨hη, inferInstance, inferInstance, hLN, f', ?_⟩
  rw [← hf']
  refine Eq.trans ?_ (AlgebraicCycle.properPushforward_comp _ _ _).symm
  have hid : inv (X.pointClosureι (genericPoint X)) ≫ X.pointClosureι (genericPoint X) = 𝟙 X :=
    IsIso.inv_hom_id _
  refine Eq.trans ?_ (properPushforward_congr hid.symm _)
  exact (AlgebraicCycle.map_id Order.height (X.principalCycle g)).symm

end AlgebraicGeometry
end
