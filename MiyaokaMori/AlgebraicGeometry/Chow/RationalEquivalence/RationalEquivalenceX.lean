import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.LocallyFiniteCycleSum
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureSubscheme
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor

/-! # Rational equivalence of cycles

Rational equivalence of algebraic cycles (the relation defining the Chow group), in the form of Stacks 02RV,
02RW: cycles rationally equivalent to zero are the locally finite sums of pushforwards of principal
divisors on integral closed subschemes. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- The generating data of Stacks 02RW: a point `w` of height `p+1` (corresponding to the integral closed
subscheme `W_w = X.pointClosure w`) and an `f ∈ K(W_w)^×`, giving the cycle `c = (ι_w)_* div(f)`.

The integrality of `W_w`, the fact that `ι_w` is a closed immersion (always true) and the local
Noetherianity of `W_w` are instances inside the existential (they always hold for `X` locally of finite
type over a field), so the definition makes sense for any scheme. -/
def IsRatEquivGen (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) (w : X)
    (c : AlgebraicGeometry.AlgebraicCycle X ℤ) : Prop :=
  ∃ (_ : Order.height w = ((p + 1 : ℕ) : ℕ∞))
    (_ : AlgebraicGeometry.IsIntegral (X.pointClosure w))
    (_ : AlgebraicGeometry.IsClosedImmersion (X.pointClosureι w))
    (_ : AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w))
    (f : (X.pointClosure w).functionFieldˣ),
    c = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
      ((X.pointClosure w).principalCycle f)

/-- The support of a generator lies in `W_w = closure {w}` (`supp((i_j)_*div(f_j)) ⊂ W_j` in Stacks 02RW). -/
theorem IsRatEquivGen.specializes {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} {w : X}
    {c : AlgebraicGeometry.AlgebraicCycle X ℤ} (h : IsRatEquivGen X p w c) {z : X}
    (hz : c z ≠ 0) : w ⤳ z := by
  obtain ⟨hw, hint, hci, hLN, f, hceq⟩ := h
  rw [hceq] at hz
  exact AlgebraicGeometry.properPushforward_pointClosure_specializes _ hz

/-- `div(f⁻¹) = −div(f)`: the negative of a generator is a generator. -/
theorem IsRatEquivGen.neg {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} {w : X}
    {c : AlgebraicGeometry.AlgebraicCycle X ℤ} (h : IsRatEquivGen X p w c) :
    IsRatEquivGen X p w (-c) := by
  obtain ⟨hw, hint, hci, hLN, f, rfl⟩ := h
  refine ⟨hw, hint, hci, hLN, f⁻¹, ?_⟩
  rw [AlgebraicGeometry.Scheme.principalCycle_inv,
    AlgebraicCycle.properPushforward_neg]

/-- `div(f^n) = n·div(f)`: an integer multiple of a generator is a generator. -/
theorem IsRatEquivGen.zsmul {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} {w : X}
    {c : AlgebraicGeometry.AlgebraicCycle X ℤ} (h : IsRatEquivGen X p w c) (n : ℤ) :
    IsRatEquivGen X p w (n • c) := by
  obtain ⟨hw, hint, hci, hLN, f, rfl⟩ := h
  refine ⟨hw, hint, hci, hLN, f ^ n, ?_⟩
  rw [AlgebraicGeometry.Scheme.principalCycle_zpow,
    AlgebraicCycle.properPushforward_zsmul]

/-- In the sum of a locally finite family of generators, only finitely many terms are nonzero at each point. -/
theorem finite_support_of_ratEquivGen {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} {J : Type v}
    {w : J → X} {c : J → AlgebraicGeometry.AlgebraicCycle X ℤ}
    (hlf : AlgebraicGeometry.LocallyFinitePoints w)
    (hg : ∀ j, IsRatEquivGen X p (w j) (c j)) (z : X) :
    (Function.support fun j => c j z).Finite :=
  AlgebraicGeometry.finite_support_of_locallyFinitePoints hlf c
    (fun j _ hz => (hg j).specializes hz) z

/-- **Stacks 02RW with restricted support**: rationally trivial cycles whose `W_j` all have generic points in
`T`. This is the parameter needed in the second paragraph of Stacks 02RZ
(`ratEquivZero_of_locallyFinite_sum`). -/
def ratEquivZeroOn (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) (T : Set X) :
    AddSubgroup (AlgebraicGeometry.AlgebraicCycle X ℤ) where
  carrier := {α | ∃ (J : Type u) (w : J → X) (c : J → AlgebraicGeometry.AlgebraicCycle X ℤ),
    (∀ j, w j ∈ T) ∧ (∀ j, IsRatEquivGen X p (w j) (c j)) ∧
      AlgebraicGeometry.LocallyFinitePoints w ∧ ∀ z, α z = ∑ᶠ j, c j z}
  add_mem' := by
    rintro α β ⟨J₁, w₁, c₁, hT₁, hg₁, hlf₁, hs₁⟩ ⟨J₂, w₂, c₂, hT₂, hg₂, hlf₂, hs₂⟩
    refine ⟨J₁ ⊕ J₂, Sum.elim w₁ w₂, Sum.elim c₁ c₂, ?_, ?_, ?_, ?_⟩
    · rintro (a | b)
      exacts [hT₁ a, hT₂ b]
    · rintro (a | b)
      exacts [hg₁ a, hg₂ b]
    · intro x
      obtain ⟨U₁, hU₁, hx₁, hf₁⟩ := hlf₁ x
      obtain ⟨U₂, hU₂, hx₂, hf₂⟩ := hlf₂ x
      refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hx₁, hx₂⟩,
        ((hf₁.image Sum.inl).union (hf₂.image Sum.inr)).subset ?_⟩
      rintro (a | b) hab
      · exact Or.inl ⟨a, hab.1, rfl⟩
      · exact Or.inr ⟨b, hab.2, rfl⟩
    · intro z
      have he : (fun j : J₁ ⊕ J₂ => Sum.elim c₁ c₂ j z)
          = Sum.elim (fun j => c₁ j z) (fun j => c₂ j z) := by
        funext j; cases j <;> rfl
      rw [he, finsum_sum_elim _ _ (finite_support_of_ratEquivGen hlf₁ hg₁ z)
        (finite_support_of_ratEquivGen hlf₂ hg₂ z), ← hs₁, ← hs₂]
      rfl
  zero_mem' := by
    refine ⟨PEmpty.{u + 1}, PEmpty.elim, PEmpty.elim, (fun j => j.elim), (fun j => j.elim),
      fun x => ⟨Set.univ, isOpen_univ, Set.mem_univ x, Set.toFinite _⟩, fun z => ?_⟩
    rw [finsum_of_isEmpty]
    rfl
  neg_mem' := by
    rintro α ⟨J, w, c, hT, hg, hlf, hs⟩
    refine ⟨J, w, fun j => -c j, hT, fun j => (hg j).neg, hlf, fun z => ?_⟩
    have he : (fun j => (-c j) z) = fun j => -(c j z) := rfl
    show (-α) z = _
    rw [he, finsum_neg_distrib, ← hs z]
    rfl

/-- **Stacks 02RW**: the group of cycles rationally equivalent to zero, defined as the sums of **locally
finite** families of pushforwards of principal cycles (the original sense of Stacks 02RW; Stacks 02RV
explains that without locally finite sums the descent of `c_1(L) ∩ −` to rational equivalence, 02TI, is not
known to hold).

Relation to the finite-sum variant: `ratEquivZeroFinite ≤ ratEquivZero`
(`ratEquivZeroFinite_le_ratEquivZero`), with equality for `X` quasi-compact
(`ratEquivZero_eq_finite_of_compactSpace`) and strict inequality in general (Stacks 02RS). -/
def ratEquivZero (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) :
    AddSubgroup (AlgebraicGeometry.AlgebraicCycle X ℤ) :=
  ratEquivZeroOn X p Set.univ

/-- The **finite**-sum variant, kept for comparison. -/
def ratEquivZeroFinite (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) :
    AddSubgroup (AlgebraicGeometry.AlgebraicCycle X ℤ) :=
  AddSubgroup.closure {c | ∃ w : X, IsRatEquivGen X p w c}

theorem ratEquivZeroOn_mono {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} {T T' : Set X}
    (h : T ⊆ T') : ratEquivZeroOn X p T ≤ ratEquivZeroOn X p T' := by
  rintro α ⟨J, w, c, hT, hg, hlf, hs⟩
  exact ⟨J, w, c, fun j => h (hT j), hg, hlf, hs⟩

theorem ratEquivZeroOn_le_ratEquivZero {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} (T : Set X) :
    ratEquivZeroOn X p T ≤ ratEquivZero X p :=
  ratEquivZeroOn_mono (Set.subset_univ T)

/-- A single generator belongs to the (support-restricted) group of rationally trivial cycles. -/
theorem single_mem_ratEquivZeroOn {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} {T : Set X} {w : X}
    {c : AlgebraicGeometry.AlgebraicCycle X ℤ} (hw : w ∈ T) (h : IsRatEquivGen X p w c) :
    c ∈ ratEquivZeroOn X p T := by
  refine ⟨PUnit.{u + 1}, fun _ => w, fun _ => c, fun _ => hw, fun _ => h,
    fun x => ⟨Set.univ, isOpen_univ, Set.mem_univ x, Set.toFinite _⟩, fun z => ?_⟩
  rw [finsum_unique]

theorem single_mem_ratEquivZero {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} {w : X}
    {c : AlgebraicGeometry.AlgebraicCycle X ℤ} (h : IsRatEquivGen X p w c) :
    c ∈ ratEquivZero X p :=
  single_mem_ratEquivZeroOn (Set.mem_univ w) h

theorem ratEquivZeroFinite_le_ratEquivZero (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) :
    ratEquivZeroFinite X p ≤ ratEquivZero X p := by
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro c ⟨w, h⟩
  exact single_mem_ratEquivZero h

/-- For a quasi-compact space, locally finite families are finite, so the two definitions agree (the
parenthetical remark of Stacks 02RS: "make sure your spaces are always quasi-compact"). -/
theorem ratEquivZero_eq_finite_of_compactSpace (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X]
    (p : ℕ) : ratEquivZero X p = ratEquivZeroFinite X p := by
  refine le_antisymm ?_ (ratEquivZeroFinite_le_ratEquivZero X p)
  rintro α ⟨J, w, c, -, hg, hlf, hs⟩
  classical
  choose U hUopen hxU hUfin using hlf
  obtain ⟨F, hF⟩ := (isCompact_univ (X := X)).elim_finite_subcover U hUopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  have hJfin : (Set.univ : Set J).Finite := by
    refine (F.finite_toSet.biUnion (fun x _ => hUfin x)).subset ?_
    intro j _
    obtain ⟨-, ⟨x, rfl⟩, hj⟩ := hF (Set.mem_univ (w j))
    obtain ⟨-, ⟨hxF, rfl⟩, hj⟩ := hj
    exact Set.mem_biUnion hxF hj
  have : Finite J := Set.finite_univ_iff.mp hJfin
  cases nonempty_fintype J with
  | intro hfin =>
    have hα : α = ∑ j : J, c j := by
      refine Function.locallyFinsuppWithin.ext fun z => ?_
      let ev : AlgebraicGeometry.AlgebraicCycle X ℤ →+ ℤ :=
        { toFun := fun d => d z, map_zero' := rfl, map_add' := fun _ _ => rfl }
      show α z = ev (∑ j : J, c j)
      rw [map_sum, hs z, finsum_eq_sum_of_support_subset _ (s := Finset.univ) (by simp)]
      rfl
    rw [hα]
    exact AddSubgroup.sum_mem _ fun j _ =>
      AddSubgroup.subset_closure ⟨w j, hg j⟩

/-- **Second paragraph of Stacks 02RZ**: if `{T i}` is a locally finite family of sets, the witnesses of
rational equivalence of `a i` all lie in `T i`, and `α` is the (pointwise finite) sum of the `a i`, then
`α` is rationally trivial.

Stacks points out that the more general statement of the first paragraph (knowing only that each `a i` is
rationally trivial) **fails**: the union of the witnessing families `{W_{i,j}}` need not be locally finite.
The support parameter `T` supplies exactly this. -/
theorem ratEquivZero_of_locallyFinite_sum {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} {I : Type u}
    (T : I → Set X) (hT : LocallyFinite T) (α : AlgebraicGeometry.AlgebraicCycle X ℤ)
    (a : I → AlgebraicGeometry.AlgebraicCycle X ℤ)
    (ha : ∀ i, a i ∈ ratEquivZeroOn X p (T i)) (hsum : ∀ z, α z = ∑ᶠ i, a i z) :
    α ∈ ratEquivZero X p := by
  classical
  choose J w c hTw hg hlf hs using ha
  have hlfSigma : AlgebraicGeometry.LocallyFinitePoints
      (fun q : Σ i, J i => w q.1 q.2) := by
    intro x
    obtain ⟨t, ht, hFfin⟩ := hT x
    choose U hUopen hxU hUfin using fun i => hlf i x
    refine ⟨interior t ∩ (⋂ i ∈ {i | (T i ∩ t).Nonempty}, U i),
      isOpen_interior.inter (Set.Finite.isOpen_biInter hFfin fun i _ => hUopen i),
      ⟨mem_interior_iff_mem_nhds.mpr ht, Set.mem_biInter fun i _ => hxU i⟩, ?_⟩
    refine (hFfin.biUnion (fun i _ =>
      (hUfin i).image (fun j => (⟨i, j⟩ : Σ i, J i)))).subset ?_
    rintro ⟨i, j⟩ hij
    have hiF : i ∈ {i | (T i ∩ t).Nonempty} :=
      ⟨w i j, hTw i j, interior_subset hij.1⟩
    exact Set.mem_biUnion hiF ⟨j, Set.mem_iInter₂.mp hij.2 i hiF, rfl⟩
  refine ⟨Σ i, J i, fun q => w q.1 q.2, fun q => c q.1 q.2, fun _ => Set.mem_univ _,
    fun q => hg q.1 q.2, hlfSigma, fun z => ?_⟩
  rw [hsum z, finsum_congr (fun i => hs i z)]
  exact (finsum_sigma (fun q : Σ i, J i => c q.1 q.2 z)
    (finite_support_of_ratEquivGen hlfSigma (fun q => hg q.1 q.2) z)).symm

/-- Two `p`-cycles are rationally equivalent when both lie in `Z_p(X)` and their difference lies in
`ratEquivZero X p`. -/
def RationallyEquivalent {X : AlgebraicGeometry.Scheme.{u}} (p : ℕ)
    (α β : AlgebraicGeometry.AlgebraicCycle X ℤ) : Prop :=
  α ∈ AlgebraicGeometry.cycleSubgroup X p ∧ β ∈ AlgebraicGeometry.cycleSubgroup X p ∧
    α - β ∈ AlgebraicGeometry.ratEquivZero X p

end AlgebraicGeometry

end
