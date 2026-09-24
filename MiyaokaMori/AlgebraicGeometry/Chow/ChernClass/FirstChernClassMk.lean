import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02ti

/-! # Evaluating the first Chern class on the class of a cycle

Let `X` be locally Noetherian and locally of finite type over a field `k`, `L` a line bundle, `d > 0`
and `α ∈ Z_d(X)`. Then the value of `c_1(L) ∩ −` on the Chow group (`firstChernClass`, whose body is a
`dite`) at the class `[α]` is the cycle-level `firstChernCapCycle L d α`: the `dite` takes its positive
branch.

Proof:
1. The condition of the `dite` is "`0 < d` and there are a locally Noetherian instance and a proof of
   local finite type over a field such that `firstChernCapCycle` sends rationally equivalent `d`-cycles
   to the same class"; it holds by Stacks 02TI (`firstChernCapCycle_rationallyEquivalent`), so `dif_pos`.
2. The positive branch is a `QuotientAddGroup.lift`, whose value at `ChowGroup.mk ⟨α, hα⟩` is by
   definition `firstChernCapCycle _ L d α`; the data of `firstChernCapCycle` does not depend on the
   particular proof `hX` (proof irrelevance), hence `rfl`.

Source: unfolding of the definition of `firstChernClass`; Stacks 02TI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem dite_addMonoidHom_apply_pos {c : Prop} {_ : Decidable c} {A B : Type*} [AddZeroClass A]
    [AddZeroClass B] (t : c → (A →+ B)) (e : ¬c → (A →+ B)) (hc : c) (x : A) :
    (dite c t e) x = t hc x := by
  rw [dif_pos hc]

/-- `c_1(L) ∩ [α] = firstChernCapCycle L d α` for `d > 0` on a locally Noetherian scheme locally of finite
type over a field. -/
theorem AlgebraicGeometry.firstChernClass_mk {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] {d : ℕ} (hd : 0 < d)
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) (hα : α ∈ AlgebraicGeometry.cycleSubgroup X d) :
    AlgebraicGeometry.firstChernClass L d (AlgebraicGeometry.ChowGroup.mk ⟨α, hα⟩) =
      AlgebraicGeometry.firstChernCapCycle
        (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X) L d α := by
  have hc : 0 < d ∧ ∃ (_ : AlgebraicGeometry.IsLocallyNoetherian X)
      (hX : X.IsLocallyOfFiniteTypeOverField),
      ∀ α β : AlgebraicGeometry.AlgebraicCycle X ℤ, AlgebraicGeometry.RationallyEquivalent d α β →
        AlgebraicGeometry.firstChernCapCycle hX L d α = AlgebraicGeometry.firstChernCapCycle hX L d β :=
    ⟨hd, ‹AlgebraicGeometry.IsLocallyNoetherian X›,
      AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X,
      fun α β h => AlgebraicGeometry.firstChernCapCycle_rationallyEquivalent (k := k) L d α β h⟩
  unfold AlgebraicGeometry.firstChernClass
  exact (dite_addMonoidHom_apply_pos _ _ hc _).trans rfl

end
