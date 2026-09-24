import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureTransport
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.LocallyFiniteCycleSum
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5

/-! # Pushforward along a closed immersion preserves rational equivalence

Let `i : W → X` be **any** closed immersion. Then `i_*` sends rationally trivial `p`-cycles on `W` to
rationally trivial `p`-cycles on `X`, with the witnessing family supported in `range i` (the
closed-immersion case of Stacks 02S2, with the support information needed in the second paragraph of
02RZ). In the special case `W = X.pointClosure w`, `i = ι_w`, the witnessing family lies in `closure{w}`.
Accompanying elementary facts for a closed immersion `i : W → X`: (a) coefficients vanish outside the
image; (b) the image of a locally finite family of points is locally finite; (c) generators map to
generators: `IsRatEquivGen W p v c → IsRatEquivGen X p (ι v) (ι_* c)`.

Proof:
1. (c): heights are preserved (`Scheme.Hom.height_of_isClosedImmersion`); `ι_v ≫ i` is a closed immersion
   of the integral scheme `W.pointClosure v` into `X`, so `θ : W.pointClosure v ≅ X.pointClosure (i v)`
   (`PointClosureTransport`); `ι_*(ι_v)_* div f = (ι_v ≫ ι)_* div f` (Stacks 02R5)
   `= (θ ≫ ι_{ιv})_* div f = (ι_{ιv})_* θ_* div f = (ι_{ιv})_* div f′`.
2. Main statement: the witnessing family is `(ι v_j, ι_* c_j)`; the supports `ι v_j ∈ range ι = closure{w}`;
   local finiteness by (b); pointwise sums: for `z = ι z′` both sides reduce by
   `properPushforward_closedImmersion_apply` to `γ z′ = Σ c_j z′`, and for `z ∉ range ι` both sides vanish
   by (a).

Source: Stacks 02S2 (closed-immersion case), 02RW, 02RZ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace MiyaokaMori.ClosedImmersionPushforward
open MiyaokaMori.PointClosureTransport MiyaokaMori.FirstChernCapPointGeneric

/-- Equal morphisms have equal pushforwards (avoiding a dependent rewrite of the `IsProper` instance). -/
theorem properPushforward_congr {W X : Scheme.{u}} {f g : W ⟶ X} (h : f = g) [IsProper f]
    [IsProper g] (c : AlgebraicCycle W ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c = AlgebraicGeometry.AlgebraicCycle.properPushforward g c := by
  subst h; rfl

/-- (a) At points outside the image, the coefficient of the pushforward vanishes. -/
theorem properPushforward_apply_of_notMem_range {W X : Scheme.{u}} (i : W ⟶ X) [IsProper i]
    (c : AlgebraicCycle W ℤ) {z : X} (hz : z ∉ Set.range i.base) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i c z = 0 := by
  have happ : AlgebraicGeometry.AlgebraicCycle.properPushforward i c z =
      ∑ᶠ y ∈ i.base ⁻¹' {z}, c y *
        ((AlgebraicCycle.mapCoeff i (Order.height (α := W)) (Order.height (α := X)) y : ℕ) : ℤ) :=
    rfl
  have hset : i.base ⁻¹' {z} = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h => hz ⟨y, h⟩
  rw [happ, hset, finsum_mem_empty]

/-- (b) A closed immersion sends locally finite families of points to locally finite families. -/
theorem locallyFinitePoints_comp_of_isClosedImmersion {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] {J : Type v} {v : J → W} (hv : LocallyFinitePoints v) :
    LocallyFinitePoints (fun j => i.base (v j)) := by
  intro x
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨x', rfl⟩ := hx
    obtain ⟨U', hU', hx', hfin⟩ := hv x'
    obtain ⟨U, hU, rfl⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp hU'
    exact ⟨U, hU, hx', hfin⟩
  · refine ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl, hx, ?_⟩
    convert Set.finite_empty
    ext j
    simp

/-- The image of the closed immersion of a point closure lies in `closure {w}`. -/
theorem pointClosureι_mem_closure {X : Scheme.{u}} (w : X) (v : X.pointClosure w) :
    (X.pointClosureι w).base v ∈ closure ({w} : Set X) := by
  have hr := Scheme.IdealSheafData.range_subschemeι
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {w}, isClosed_closure⟩)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hr
  exact hr.subset ⟨v, rfl⟩

/-- (c) Generators map to generators (the closed-immersion case of Stacks 02S2; valid for **any** closed
immersion). -/
theorem isRatEquivGen_properPushforward_of_isClosedImmersion {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (p : ℕ) (v : W) (c : AlgebraicCycle W ℤ)
    (h : IsRatEquivGen W p v c) :
    IsRatEquivGen X p (i.base v) (AlgebraicGeometry.AlgebraicCycle.properPushforward i c) := by
  obtain ⟨hv, hint, hci, hLN, f, rfl⟩ := h
  obtain ⟨θ, hθ⟩ := exists_iso_pointClosure_of_isClosedImmersion (W.pointClosureι v ≫ i)
    (i.base v) (by
      show i.base ((W.pointClosureι v).base _) = _
      rw [Scheme.pointClosureι_genericPoint])
  have hLN' : IsLocallyNoetherian (X.pointClosure (i.base v)) :=
    LocallyOfFiniteType.isLocallyNoetherian θ.inv
  obtain ⟨f', hf'⟩ := exists_principalCycle_eq_properPushforward_iso θ.hom f
  refine ⟨(Scheme.Hom.height_of_isClosedImmersion _ v).trans hv, inferInstance, inferInstance,
    hLN', f', ?_⟩
  -- both sides are the same constant
  -- `AlgebraicGeometry.AlgebraicCycle.properPushforward`, so `rw [properPushforward_comp]` hits the
  -- left side first; rewrite both compositions, then compare the two morphisms.
  rw [← hf', AlgebraicCycle.properPushforward_comp, AlgebraicCycle.properPushforward_comp]
  exact properPushforward_congr hθ.symm _

/-- **The closed-immersion case of Stacks 02S2 (with restricted support)**: a closed immersion `i` sends
rationally trivial cycles to rationally trivial cycles, with witnessing family in `range i`. -/
theorem properPushforward_mem_ratEquivZeroOn_of_isClosedImmersion {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (p : ℕ) (γ : AlgebraicCycle W ℤ) (hγ : γ ∈ ratEquivZero W p) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i γ ∈ ratEquivZeroOn X p (Set.range i.base) := by
  obtain ⟨J, v, c, -, hg, hlf, hs⟩ := hγ
  refine ⟨J, fun j => i.base (v j), fun j => AlgebraicGeometry.AlgebraicCycle.properPushforward i (c j),
    fun j => ⟨v j, rfl⟩,
    fun j => isRatEquivGen_properPushforward_of_isClosedImmersion i p (v j) (c j) (hg j),
    locallyFinitePoints_comp_of_isClosedImmersion _ hlf, fun z => ?_⟩
  by_cases hz : z ∈ Set.range i.base
  · obtain ⟨z', rfl⟩ := hz
    rw [properPushforward_closedImmersion_apply, hs z']
    exact finsum_congr fun j => (properPushforward_closedImmersion_apply _ (c j) z').symm
  · rw [properPushforward_apply_of_notMem_range _ _ hz]
    exact (finsum_eq_zero_of_forall_eq_zero fun j =>
      properPushforward_apply_of_notMem_range _ (c j) hz).symm

/-- The point-closure special case of (c). -/
theorem isRatEquivGen_properPushforward_pointClosure {X : Scheme.{u}} (w : X) (p : ℕ)
    (v : X.pointClosure w) (c : AlgebraicCycle (X.pointClosure w) ℤ)
    (h : IsRatEquivGen (X.pointClosure w) p v c) :
    IsRatEquivGen X p ((X.pointClosureι w).base v)
      (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) c) :=
  isRatEquivGen_properPushforward_of_isClosedImmersion _ p v c h

/-- **Stacks 02S2 along the closed immersion of a point closure, with restricted support.** -/
theorem properPushforward_pointClosure_mem_ratEquivZeroOn {X : Scheme.{u}} (w : X) (p : ℕ)
    (γ : AlgebraicCycle (X.pointClosure w) ℤ) (hγ : γ ∈ ratEquivZero (X.pointClosure w) p) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) γ ∈ ratEquivZeroOn X p (closure {w}) :=
  ratEquivZeroOn_mono (by rintro _ ⟨v, rfl⟩; exact pointClosureι_mem_closure w v)
    (properPushforward_mem_ratEquivZeroOn_of_isClosedImmersion _ p γ hγ)

end MiyaokaMori.ClosedImmersionPushforward
end
