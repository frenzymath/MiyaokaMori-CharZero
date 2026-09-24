import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SpecializingMapHeightLe
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition

/-! # Proper pushforward is compatible with composition (Stacks 02R5)

Stacks 02R5: proper pushforward is compatible with composition, `g_* ∘ f_* = (g∘f)_*` at the level of
cycles; the proof uses the multiplicativity of the degree of field extensions (Stacks 02NZ). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry in
private lemma mapCoeff_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f]
    [IsProper g] (x : X) :
    AlgebraicCycle.mapCoeff (f ≫ g) (Order.height (α := X)) (Order.height (α := Z)) x =
      AlgebraicCycle.mapCoeff f (Order.height (α := X)) (Order.height (α := Y)) x *
        AlgebraicCycle.mapCoeff g (Order.height (α := Y)) (Order.height (α := Z)) (f.base x) := by
  have h1 : Order.height (f.base x) ≤ Order.height x :=
    Scheme.height_apply_le_of_specializingMap f f.isClosedMap.specializingMap x
  have h2 : Order.height (g.base (f.base x)) ≤ Order.height (f.base x) :=
    Scheme.height_apply_le_of_specializingMap g g.isClosedMap.specializingMap (f.base x)
  unfold AlgebraicCycle.mapCoeff
  change (if Order.height x = Order.height (g.base (f.base x)) then _ else _) = _
  by_cases h : Order.height x = Order.height (g.base (f.base x))
  · have e1 : Order.height x = Order.height (f.base x) := le_antisymm (h ▸ h2) h1
    have e2 : Order.height (f.base x) = Order.height (g.base (f.base x)) := e1 ▸ h
    rw [if_pos h, if_pos e1, if_pos e2, AlgebraicGeometry.Intersection.residueDegree_comp, mul_comm]
  · rw [if_neg h]
    by_cases e1 : Order.height x = Order.height (f.base x)
    · have e2 : ¬ Order.height (f.base x) = Order.height (g.base (f.base x)) := fun e2 =>
        h (e1.trans e2)
      rw [if_neg e2, mul_zero]
    · rw [if_neg e1, zero_mul]

theorem AlgebraicGeometry.AlgebraicCycle.properPushforward_comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsProper g]
    (c : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward g (AlgebraicGeometry.AlgebraicCycle.properPushforward f c)
      = AlgebraicGeometry.AlgebraicCycle.properPushforward (f ≫ g) c := by
  classical
  ext z
  set wf : X → ℤ := fun x => ((AlgebraicCycle.mapCoeff f (Order.height (α := X))
    (Order.height (α := Y)) x : ℕ) : ℤ) with hwf
  set wg : Y → ℤ := fun y => ((AlgebraicCycle.mapCoeff g (Order.height (α := Y))
    (Order.height (α := Z)) y : ℕ) : ℤ) with hwg
  set wfg : X → ℤ := fun x => ((AlgebraicCycle.mapCoeff (f ≫ g) (Order.height (α := X))
    (Order.height (α := Z)) x : ℕ) : ℤ) with hwfg
  have hw : ∀ x, wfg x = wf x * wg (f.base x) := fun x => by
    simp only [hwf, hwg, hwfg, mapCoeff_comp f g x, Nat.cast_mul]
  change ∑ᶠ y ∈ g.base ⁻¹' {z}, (∑ᶠ x ∈ f.base ⁻¹' {y}, c x * wf x) * wg y =
    ∑ᶠ x ∈ (f ≫ g).base ⁻¹' {z}, c x * wfg x
  -- a compact open neighbourhood `U` of `z`; `S = supp c ∩ (f≫g)⁻¹U` is finite
  obtain ⟨U, hU, hzU, -⟩ := (PrespectralSpace.isTopologicalBasis (X := Z)).exists_subset_of_mem_open
    (Set.mem_univ z) isOpen_univ
  have hS : ((f ≫ g).base ⁻¹' U ∩ Function.support c).Finite :=
    c.locallyFiniteSupport.finite_inter_support_of_isCompact
      ((f ≫ g).isSpectralMap.2 hU.1 hU.2)
  set Sf : Finset X := hS.toFinset with hSf
  have hmemS : ∀ x, c x ≠ 0 → g.base (f.base x) = z → x ∈ Sf := fun x hx hxz => by
    rw [hSf, Set.Finite.mem_toFinset]
    exact ⟨by change g.base (f.base x) ∈ U; rw [hxz]; exact hzU, hx⟩
  -- the right-hand side
  have hR : ∑ᶠ x ∈ (f ≫ g).base ⁻¹' {z}, c x * wfg x =
      ∑ x ∈ Sf.filter (fun x => g.base (f.base x) = z), c x * wfg x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Function.mem_support,
      Finset.coe_filter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hne⟩
      exact ⟨⟨hmemS x (left_ne_zero_of_mul hne) hx, hx⟩, hne⟩
    · rintro ⟨⟨-, hx⟩, hne⟩
      exact ⟨hx, hne⟩
  -- the inner sum
  have hI : ∀ y ∈ g.base ⁻¹' {z}, (∑ᶠ x ∈ f.base ⁻¹' {y}, c x * wf x) * wg y =
      (∑ x ∈ Sf.filter (fun x => f.base x = y), c x * wf x) * wg y := by
    intro y hy
    congr 1
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Function.mem_support,
      Finset.coe_filter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hne⟩
      exact ⟨⟨hmemS x (left_ne_zero_of_mul hne) (by rw [hx]; exact hy), hx⟩, hne⟩
    · rintro ⟨⟨-, hx⟩, hne⟩
      exact ⟨hx, hne⟩
  rw [hR, finsum_mem_congr rfl hI]
  -- the outer sum
  have hO : ∑ᶠ y ∈ g.base ⁻¹' {z}, (∑ x ∈ Sf.filter (fun x => f.base x = y), c x * wf x) * wg y =
      ∑ y ∈ (Sf.image f.base).filter (fun y => g.base y = z),
        (∑ x ∈ Sf.filter (fun x => f.base x = y), c x * wf x) * wg y := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Function.mem_support,
      Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_image]
    constructor
    · rintro ⟨hy, hne⟩
      refine ⟨⟨?_, hy⟩, hne⟩
      obtain ⟨x, hx, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hne)
      rw [Finset.mem_filter] at hx
      exact ⟨x, hx.1, hx.2⟩
    · rintro ⟨⟨-, hy⟩, hne⟩
      exact ⟨hy, hne⟩
  rw [hO]
  have hstep : ∀ y ∈ (Sf.image f.base).filter (fun y => g.base y = z),
      (∑ x ∈ Sf.filter (fun x => f.base x = y), c x * wf x) * wg y =
        ∑ x ∈ Sf.filter (fun x => f.base x = y), c x * wfg x := by
    intro y _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_filter] at hx
    rw [hw x, hx.2, mul_assoc]
  rw [Finset.sum_congr rfl hstep]
  refine (Finset.sum_fiberwise_eq_sum_filter Sf _ (fun x => f.base x)
    (fun x => c x * wfg x)).trans ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hx, -, hz⟩
    exact ⟨hx, hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨hx, ⟨x, hx, rfl⟩, hz⟩

end
