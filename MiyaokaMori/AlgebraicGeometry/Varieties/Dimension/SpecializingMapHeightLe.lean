import MiyaokaMori.Prelude

/-! # Specializing maps do not raise the height of points

If the underlying map of `f` is specializing (e.g. the closed map of a proper morphism), then
`height f(x) ≤ height x`, i.e. `dim closure {f(x)} ≤ dim closure {x}`.

Sources: Stacks 02R5, 02RM, 02RH, 02RT, 02S2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.height_apply_le_of_specializingMap {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (hf : SpecializingMap f.base) (x : X) :
    Order.height (f.base x) ≤ Order.height x := by
  have key : ∀ (n : ℕ) (x : X), Order.height x ≤ n → Order.height (f.base x) ≤ n := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [Order.height_le_coe_iff] at hx ⊢
      intro y hy
      obtain ⟨x', hx', rfl⟩ := hf hy.le
      have hlt : x' < x := lt_of_le_not_ge hx' fun hge =>
        hy.not_ge (f.base.hom.continuous.specialization_monotone hge)
      exact absurd (hx x' hlt) (by simp)
    | succ k ih =>
      intro x hx
      rw [Order.height_le_coe_iff] at hx ⊢
      intro y hy
      obtain ⟨x', hx', rfl⟩ := hf hy.le
      have hlt : x' < x := lt_of_le_not_ge hx' fun hge =>
        hy.not_ge (f.base.hom.continuous.specialization_monotone hge)
      have h1 : Order.height x' ≤ k := Order.le_of_lt_add_one (by exact_mod_cast hx x' hlt)
      exact lt_of_le_of_lt (ih x' h1) (by exact_mod_cast Nat.lt_succ_self k)
  rcases eq_or_ne (Order.height x) ⊤ with h | h
  · rw [h]; exact le_top
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    rw [← hn]
    exact key n x hn.symm.le

end
