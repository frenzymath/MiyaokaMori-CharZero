import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.LocallyFiniteCycleSum
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup

/-! # Locally finite families and proper pushforward (preparation for Stacks 02S2)

Three topological and cycle-level preparatory lemmas for Stacks 02S2 (for **any** proper morphism
`f : X → Y`, no field needed):

(a) `properPushforward_mem_cycleSubgroup_of_mem`: the pushforward preserves `Z_p` (the height version of
    Stacks 02R6; by the coefficient convention, a component whose dimension drops gets coefficient `0`, so
    if `f_* c` is nonzero at `y` there is `x ↦ y` with `c x ≠ 0` and `height x = height y`).
(b) `exists_isOpen_superset_fiber_finite` / `locallyFinitePoints_map_of_isProper`: a proper morphism sends
    locally finite families of points to locally finite families. Proof: the fiber `f⁻¹{y}` is
    quasi-compact (`Scheme.Hom.isCompact_preimage_singleton`); cover it by the opens given by local
    finiteness and take a finite subcover `V`; `f` is a closed map, so `U := (f(Vᶜ))ᶜ` is an open
    neighbourhood of `y` with `f(w_j) ∈ U ⇒ w_j ∈ V`, which holds for finitely many `j` only.
(c) `properPushforward_apply_finsum`: the pushforward commutes with locally finite pointwise sums: if
    `α z = Σᶠ_j c_j z`, `{w_j}` is locally finite and `c_j` is supported in `closure{w_j}`, then
    `(f_* α)(y) = Σᶠ_j (f_* c_j)(y)`. Proof: take `V ⊇ f⁻¹{y}` from (b); `J₀ := {j | w_j ∈ V}` is finite;
    `β := α − Σ_{j∈J₀} c_j` vanishes on `V` (for `x ∈ V`, `c_j x ≠ 0 ⇒ w_j ⤳ x ⇒ w_j ∈ V ⇒ j ∈ J₀`), so
    `(f_* β)(y) = 0` (the coefficient only involves points of the fiber); the pushforward is additive and
    `(f_* c_j)(y) = 0` for `j ∉ J₀`, so both sides equal `Σ_{j∈J₀} (f_* c_j)(y)`.

Source: the first paragraph of the proof of Stacks 02S2 ("the family {W'_j} is locally finite since f is
proper"), 02R6.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Unfolding of the pushforward coefficient (the definition of `AlgebraicCycle.map`). -/
theorem properPushforward_apply' {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : AlgebraicCycle X ℤ) (y : Y) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c y = ∑ᶠ x ∈ f.base ⁻¹' {y}, c x *
      ((AlgebraicCycle.mapCoeff f (Order.height (α := X)) (Order.height (α := Y)) x : ℕ) : ℤ) :=
  rfl

/-- If the pushforward is nonzero at `y`, there is a point `x` of the fiber with `c x ≠ 0` and
`height x = height y`. -/
theorem exists_of_properPushforward_apply_ne_zero {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : AlgebraicCycle X ℤ) {y : Y} (hy : AlgebraicGeometry.AlgebraicCycle.properPushforward f c y ≠ 0) :
    ∃ x : X, f.base x = y ∧ c x ≠ 0 ∧ Order.height x = Order.height y := by
  rw [properPushforward_apply'] at hy
  obtain ⟨x, hxy, hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  have hxy' : f.base x = y := hxy
  refine ⟨x, hxy', fun h => hx (by simp [h]), ?_⟩
  by_contra h
  rw [← hxy'] at h
  exact hx (by simp [AlgebraicCycle.mapCoeff, h])

/-- (a) Proper pushforward preserves `Z_p`. -/
theorem properPushforward_mem_cycleSubgroup_of_mem {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (p : ℕ) {c : AlgebraicCycle X ℤ} (hc : c ∈ cycleSubgroup X p) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c ∈ cycleSubgroup Y p := by
  intro y hy
  obtain ⟨x, -, hcx, hht⟩ := exists_of_properPushforward_apply_ne_zero f c hy
  rw [← hht]
  exact hc x hcx

/-- (b) An open neighbourhood `V` of the fiber `f⁻¹{y}` containing only finitely many `w_j`. -/
theorem exists_isOpen_superset_fiber_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {J : Type v} {w : J → X} (hw : LocallyFinitePoints w) (y : Y) :
    ∃ V : Set X, IsOpen V ∧ f.base ⁻¹' {y} ⊆ V ∧ {j | w j ∈ V}.Finite := by
  classical
  choose U hUopen hxU hUfin using hw
  have hcpt : IsCompact (f.base ⁻¹' {y}) := f.isCompact_preimage_singleton y
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover U hUopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨⋃ i ∈ t, U i, isOpen_biUnion fun i _ => hUopen i, ht, ?_⟩
  refine (t.finite_toSet.biUnion fun i _ => hUfin i).subset ?_
  intro j hj
  obtain ⟨i, hi, hj⟩ := Set.mem_iUnion₂.mp hj
  exact Set.mem_biUnion hi hj

/-- (b) A proper morphism sends locally finite families of points to locally finite families. -/
theorem locallyFinitePoints_map_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {J : Type v} {w : J → X} (hw : LocallyFinitePoints w) :
    LocallyFinitePoints (fun j => f.base (w j)) := by
  intro y
  obtain ⟨V, hVopen, hfib, hfin⟩ := exists_isOpen_superset_fiber_finite f hw y
  have hclosed : IsClosed (f.base '' Vᶜ) := f.isClosedMap _ hVopen.isClosed_compl
  refine ⟨(f.base '' Vᶜ)ᶜ, hclosed.isOpen_compl, ?_, hfin.subset ?_⟩
  · rintro ⟨x, hxV, hxy⟩
    exact hxV (hfib (show f.base x ∈ ({y} : Set Y) from hxy))
  · intro j hj
    by_contra hjV
    exact hj ⟨w j, hjV, rfl⟩

/-- (c) The pushforward commutes with locally finite pointwise sums. -/
theorem properPushforward_apply_finsum {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {J : Type v} {w : J → X} (hw : LocallyFinitePoints w) (c : J → AlgebraicCycle X ℤ)
    (hc : ∀ (j : J) (z : X), c j z ≠ 0 → w j ⤳ z) (α : AlgebraicCycle X ℤ)
    (hα : ∀ z, α z = ∑ᶠ j, c j z) (y : Y) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f α y =
      ∑ᶠ j, AlgebraicGeometry.AlgebraicCycle.properPushforward f (c j) y := by
  classical
  obtain ⟨V, hVopen, hfib, hfin⟩ := exists_isOpen_superset_fiber_finite f hw y
  set J₀ : Finset J := hfin.toFinset with hJ₀
  have hmemJ₀ : ∀ j, j ∈ J₀ ↔ w j ∈ V := fun j => by simp [hJ₀]
  -- on `V`, the pointwise sum only has terms from `J₀`
  have hsupp : ∀ x ∈ V, (Function.support fun j => c j x) ⊆ ↑J₀ := by
    intro x hx j hj
    exact (hmemJ₀ j).mpr ((hc j x hj).mem_open hVopen hx)
  set β : AlgebraicCycle X ℤ := α - ∑ j ∈ J₀, c j with hβ
  have hβV : ∀ x ∈ V, β x = 0 := by
    intro x hx
    have h1 : (∑ j ∈ J₀, c j) x = ∑ j ∈ J₀, c j x := by
      change AlgebraicCycle.evalHom x (∑ j ∈ J₀, c j) = _
      rw [map_sum]; rfl
    change α x - (∑ j ∈ J₀, c j) x = 0
    rw [h1, hα x, finsum_eq_sum_of_support_subset _ (hsupp x hx), sub_self]
  -- `f_* β` vanishes at `y`
  have hβy : AlgebraicGeometry.AlgebraicCycle.properPushforward f β y = 0 := by
    rw [properPushforward_apply']
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    rw [hβV x (hfib hx), zero_mul]
  -- `(f_* c_j)(y) = 0` for `j ∉ J₀`
  have hout : ∀ j, j ∉ J₀ → AlgebraicGeometry.AlgebraicCycle.properPushforward f (c j) y = 0 := by
    intro j hj
    by_contra hne
    obtain ⟨x, hxy, hcx, -⟩ := exists_of_properPushforward_apply_ne_zero f (c j) hne
    have hxV : x ∈ V := hfib (show f.base x ∈ ({y} : Set Y) from hxy)
    exact hj ((hmemJ₀ j).mpr ((hc j x hcx).mem_open hVopen hxV))
  have hαeq : α = (∑ j ∈ J₀, c j) + β := by
    rw [hβ, add_sub_cancel]
  calc AlgebraicGeometry.AlgebraicCycle.properPushforward f α y
      = (AlgebraicCycle.evalHom y).comp (AlgebraicCycle.properPushforwardHom f)
          ((∑ j ∈ J₀, c j) + β) := by rw [← hαeq]; rfl
    _ = ∑ j ∈ J₀, AlgebraicGeometry.AlgebraicCycle.properPushforward f (c j) y := by
      rw [map_add, map_sum]
      change _ + AlgebraicGeometry.AlgebraicCycle.properPushforward f β y = _
      rw [hβy, add_zero]
      rfl
    _ = ∑ᶠ j, AlgebraicGeometry.AlgebraicCycle.properPushforward f (c j) y := by
      symm
      refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
      by_contra hjJ
      exact hj (hout j hjJ)

end AlgebraicGeometry

end
