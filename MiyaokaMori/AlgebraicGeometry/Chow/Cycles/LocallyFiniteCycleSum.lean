import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureSubscheme
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.VarietyCyclePushforward

/-! # Sums of locally finite families of cycles

The bookkeeping for the sum `Σ (i_j)_* div(f_j)` of Stacks 02RW over a locally finite family.

Source: Stacks 02RV (introduction), 02RW (definition), Topology 0051 (locally finite families), 02RZ
(infinite sums and rational equivalence).

This file only provides the mechanism and does not involve rational equivalence itself:
* `AlgebraicGeometry.LocallyFinitePoints w`: a family of points `w : J → X` is locally finite, equivalently
  the family of closures `{closure {w j}}` is locally finite (`locallyFinitePoints_iff_locallyFinite_closure`)
  — the requirement on `{W_j}` in Stacks 02RW, written in terms of generic points.
* The support of `AlgebraicGeometry.AlgebraicCycle.properPushforward` along `pointClosureι w` lies in
  `closure {w}` (`properPushforward_pointClosure_specializes`), so the pointwise sum `∑ᶠ j, c j z` of a locally
  finite family has only finitely many nonzero terms at each point (`finite_support_of_locallyFinitePoints`).
* Two exchange-of-summation lemmas for `finsum`: `finsum_sum_elim` (union of two families, for closure under
  addition) and `finsum_sigma` (families of families, for the second paragraph of Stacks 02RZ).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- The "locally finite family" of Stacks Topology 0051, written on generic points: every `x` has an open
neighbourhood `U` such that only finitely many indices satisfy `w j ∈ U`. By
`locallyFinitePoints_iff_locallyFinite_closure` this is the same as local finiteness of the family of
closures `{closure {w j}}_{j}` in the sense of Stacks. -/
def LocallyFinitePoints {X : AlgebraicGeometry.Scheme.{u}} {J : Type v} (w : J → X) : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ {j | w j ∈ U}.Finite

/-- An open set `U` meets `closure {w}` if and only if `w ∈ U` (open sets are closed under generization). -/
theorem closure_singleton_inter_nonempty_iff {X : Type*} [TopologicalSpace X] {w : X} {U : Set X}
    (hU : IsOpen U) : (closure {w} ∩ U).Nonempty ↔ w ∈ U := by
  constructor
  · rintro ⟨y, hy, hyU⟩
    exact (specializes_iff_mem_closure.mpr hy).mem_open hU hyU
  · exact fun h => ⟨w, subset_closure rfl, h⟩

/-- A family of generic points is locally finite iff the family of closures (the `{W_j}` of Stacks 02RW) is
locally finite. -/
theorem locallyFinitePoints_iff_locallyFinite_closure {X : AlgebraicGeometry.Scheme.{u}}
    {J : Type v} (w : J → X) :
    LocallyFinitePoints w ↔ LocallyFinite (fun j => closure {w j}) := by
  constructor
  · intro h x
    obtain ⟨U, hU, hxU, hfin⟩ := h x
    refine ⟨U, hU.mem_nhds hxU, hfin.subset fun j hj => ?_⟩
    exact (closure_singleton_inter_nonempty_iff hU).mp hj
  · intro h x
    obtain ⟨t, ht, hfin⟩ := h x
    refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht,
      hfin.subset fun j hj => ?_⟩
    exact ⟨w j, subset_closure rfl, interior_subset hj⟩

/-- The support of a cycle is itself a locally finite family of points (the condition of
`Function.locallyFinsupp`). -/
theorem locallyFinitePoints_support {X : AlgebraicGeometry.Scheme.{u}}
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    LocallyFinitePoints (fun j : Function.support (α : X → ℤ) => (j : X)) := by
  intro x
  obtain ⟨t, ht, hfin⟩ := α.locallyFiniteSupport x
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht, ?_⟩
  have hsub : {j : Function.support (α : X → ℤ) | (j : X) ∈ interior t} ⊆
      Subtype.val ⁻¹' (t ∩ Function.support (α : X → ℤ)) := by
    rintro ⟨j, hj⟩ hjt
    exact ⟨interior_subset hjt, hj⟩
  exact (hfin.preimage Subtype.val_injective.injOn).subset hsub

/-- A set of points contained in the support of a cycle is a locally finite family. -/
theorem locallyFinitePoints_of_subset_support {X : AlgebraicGeometry.Scheme.{u}}
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) {S : Set X}
    (hS : S ⊆ Function.support (α : X → ℤ)) :
    LocallyFinitePoints (fun j : S => (j : X)) := by
  intro x
  obtain ⟨t, ht, hfin⟩ := α.locallyFiniteSupport x
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht, ?_⟩
  have hsub : {j : S | (j : X) ∈ interior t} ⊆
      Subtype.val ⁻¹' (t ∩ Function.support (α : X → ℤ)) := by
    rintro ⟨j, hj⟩ hjt
    exact ⟨interior_subset hjt, hS hj⟩
  exact (hfin.preimage Subtype.val_injective.injOn).subset hsub

/-- Evaluation at a point is a homomorphism of additive groups. -/
def AlgebraicCycle.evalHom {X : AlgebraicGeometry.Scheme.{u}} (z : X) :
    AlgebraicGeometry.AlgebraicCycle X ℤ →+ ℤ where
  toFun c := c z
  map_zero' := rfl
  map_add' _ _ := rfl

theorem AlgebraicCycle.zsmul_apply {X : AlgebraicGeometry.Scheme.{u}} (n : ℤ)
    (c : AlgebraicGeometry.AlgebraicCycle X ℤ) (z : X) : (n • c) z = n * c z := by
  simp

/-- The support of the proper pushforward along `pointClosureι w` lies in `closure {w}`:
`c z ≠ 0 → w ⤳ z`. This formalizes `supp((i_j)_*div(f_j)) ⊂ W_j` in Stacks 02RW. -/
theorem properPushforward_pointClosure_specializes {X : AlgebraicGeometry.Scheme.{u}} {w : X}
    [AlgebraicGeometry.IsProper (X.pointClosureι w)]
    (γ : AlgebraicGeometry.AlgebraicCycle (X.pointClosure w) ℤ) {z : X}
    (h : AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) γ z ≠ 0) : w ⤳ z := by
  unfold AlgebraicGeometry.AlgebraicCycle.properPushforward AlgebraicGeometry.AlgebraicCycle.map at h
  simp only [Function.locallyFinsupp.map_apply] at h
  obtain ⟨z', hz', -⟩ := exists_ne_zero_of_finsum_mem_ne_zero h
  rw [specializes_iff_mem_closure]
  have hr := AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {w}, isClosed_closure⟩)
  rw [AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal] at hr
  exact hr.subset ⟨z', hz'⟩

/-- The pointwise sum of a locally finite family has only finitely many nonzero terms at each point. -/
theorem finite_support_of_locallyFinitePoints {X : AlgebraicGeometry.Scheme.{u}} {J : Type v}
    {w : J → X} (hw : LocallyFinitePoints w) (c : J → AlgebraicGeometry.AlgebraicCycle X ℤ)
    (hc : ∀ (j : J) (z : X), c j z ≠ 0 → w j ⤳ z) (z : X) :
    (Function.support (fun j => c j z)).Finite := by
  obtain ⟨U, hU, hzU, hfin⟩ := hw z
  exact hfin.subset fun j hj => (hc j z hj).mem_open hU hzU

/-- The proper pushforward as a homomorphism of additive groups (Mathlib's `AlgebraicCycle.map` is linear in
the coefficients). -/
noncomputable def AlgebraicCycle.properPushforwardHom {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] :
    AlgebraicGeometry.AlgebraicCycle X ℤ →+ AlgebraicGeometry.AlgebraicCycle Y ℤ :=
  AddMonoidHom.mk' (AlgebraicGeometry.AlgebraicCycle.properPushforward f)
    (AlgebraicGeometry.AlgebraicCycle.map_add f Order.height Order.height)

theorem AlgebraicCycle.properPushforward_neg {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (a : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (-a) = -AlgebraicGeometry.AlgebraicCycle.properPushforward f a :=
  map_neg (AlgebraicCycle.properPushforwardHom f) a

theorem AlgebraicCycle.properPushforward_zsmul {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (n : ℤ)
    (a : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (n • a) = n • AlgebraicGeometry.AlgebraicCycle.properPushforward f a :=
  map_zsmul (AlgebraicCycle.properPushforwardHom f) n a

end AlgebraicGeometry

/-! ## Two exchange-of-summation lemmas for `finsum` -/

/-- The `finsum` over the union of two families. -/
theorem finsum_sum_elim {J : Type u} {K : Type v} {M : Type w} [AddCommMonoid M]
    (f : J → M) (g : K → M) (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) :
    (∑ᶠ q : J ⊕ K, Sum.elim f g q) = (∑ᶠ j, f j) + ∑ᶠ k, g k := by
  classical
  have hsub : Function.support (Sum.elim f g) ⊆ ↑(hf.toFinset.disjSum hg.toFinset) := by
    rintro (a | b) hab
    · exact Finset.mem_coe.mpr (Finset.inl_mem_disjSum.mpr (by simpa using hab))
    · exact Finset.mem_coe.mpr (Finset.inr_mem_disjSum.mpr (by simpa using hab))
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset) (by simp),
    finsum_eq_sum_of_support_subset g (s := hg.toFinset) (by simp),
    finsum_eq_sum_of_support_subset (Sum.elim f g) hsub, Finset.sum_disjSum]
  rfl

/-- Exchange of summation for the `finsum` over a family of families (a `Sigma` type). -/
theorem finsum_sigma {I : Type u} {J : I → Type v} {M : Type w} [AddCommMonoid M]
    (F : (Σ i, J i) → M) (h : (Function.support F).Finite) :
    (∑ᶠ q : Σ i, J i, F q) = ∑ᶠ i, ∑ᶠ j, F ⟨i, j⟩ := by
  classical
  have hi : ∀ i : I, (Function.support (fun j : J i => F ⟨i, j⟩)).Finite := fun i =>
    (h.preimage (f := fun j : J i => (⟨i, j⟩ : Σ i, J i))
      (fun a _ b _ hab => by simpa using hab)).subset (fun j hj => hj)
  set s : Finset I := (h.image Sigma.fst).toFinset with hs
  set t : ∀ i : I, Finset (J i) := fun i => (hi i).toFinset with ht
  have hmem : ∀ (i : I) (j : J i), F ⟨i, j⟩ ≠ 0 → i ∈ s := by
    intro i j hij
    have hsup : (⟨i, j⟩ : Σ i, J i) ∈ Function.support F := hij
    simpa [hs] using Set.mem_image_of_mem Sigma.fst hsup
  have h1 : (∑ᶠ q : Σ i, J i, F q) = ∑ x ∈ s.sigma t, F x := by
    refine finsum_eq_sum_of_support_subset F ?_
    rintro ⟨i, j⟩ hij
    simp only [Function.mem_support] at hij
    exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨hmem i j hij, by simpa [ht] using hij⟩)
  have h3 : ∀ i : I, (∑ᶠ j : J i, F ⟨i, j⟩) = ∑ j ∈ t i, F ⟨i, j⟩ := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp [ht])
  have h2 : (∑ᶠ i, ∑ᶠ j, F ⟨i, j⟩) = ∑ i ∈ s, ∑ᶠ j : J i, F ⟨i, j⟩ := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro i hi'
    simp only [Function.mem_support] at hi'
    obtain ⟨j, hj⟩ : ∃ j, F ⟨i, j⟩ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hi' (finsum_eq_zero_of_forall_eq_zero hcon)
    exact Finset.mem_coe.mpr (hmem i j hj)
  rw [h1, h2, Finset.sum_congr rfl (fun i _ => h3 i),
    Finset.sum_sigma' s t (fun i j => F ⟨i, j⟩)]

end
