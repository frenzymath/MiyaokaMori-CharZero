import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrimeDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs

/-! # Weil divisors

The group of Weil divisors `Div(X)`: the free abelian group on the set of prime divisors (Noetherian case),
whose elements are finite formal sums `Σ n_i Z_i`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The group of Weil divisors: the free abelian group on the prime divisors of `X`. -/
def AlgebraicGeometry.Scheme.WeilDivisor (X : AlgebraicGeometry.Scheme.{u}) : Type u :=
  FreeAbelianGroup {Z : X // X.IsPrimeDivisor Z}

instance (X : AlgebraicGeometry.Scheme.{u}) : AddCommGroup X.WeilDivisor :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup _))

open Classical in
/-- Comparison with cycles: `Σ n_i Z_i ↦ Σ n_i [Z_i]`. -/
noncomputable def AlgebraicGeometry.Scheme.WeilDivisor.toCycle {X : AlgebraicGeometry.Scheme.{u}} :
    X.WeilDivisor →+ AlgebraicGeometry.AlgebraicCycle X ℤ :=
  FreeAbelianGroup.lift (fun Z => Function.locallyFinsuppWithin.single Z.1 1)

open Classical in
/-- The value of `toCycle a` at the generic point of a prime divisor `Z` is the coefficient of `Z` in the formal
sum `a` (`FreeAbelianGroup.coeff`); by `FreeAbelianGroup.induction_on`, the case of a generator being
`single_apply` (distinct prime divisors are distinct points). -/
theorem AlgebraicGeometry.Scheme.WeilDivisor.toCycle_apply_eq_coeff {X : AlgebraicGeometry.Scheme.{u}}
    (Z : {Z : X // X.IsPrimeDivisor Z}) (a : FreeAbelianGroup {Z : X // X.IsPrimeDivisor Z}) :
    (AlgebraicGeometry.Scheme.WeilDivisor.toCycle a : X → ℤ) Z.1 = FreeAbelianGroup.coeff Z a := by
  -- write the domain of `toCycle` explicitly as `FreeAbelianGroup` so that the `+`/`-` produced by the induction match `map_add`/`map_neg` syntactically
  let L : FreeAbelianGroup {Z : X // X.IsPrimeDivisor Z} →+ AlgebraicGeometry.AlgebraicCycle X ℤ :=
    AlgebraicGeometry.Scheme.WeilDivisor.toCycle
  have hL : ∀ W : {Z : X // X.IsPrimeDivisor Z},
      L (FreeAbelianGroup.of W) = Function.locallyFinsuppWithin.single W.1 (1 : ℤ) :=
    fun W => FreeAbelianGroup.lift_apply_of _ _
  change (L a : X → ℤ) Z.1 = _
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  | of W =>
    rw [hL, Function.locallyFinsuppWithin.single_apply, FreeAbelianGroup.coeff, AddMonoidHom.comp_apply,
      FreeAbelianGroup.toFinsupp_of, Finsupp.applyAddHom_apply]
    by_cases h : W = Z
    · subst h; rw [if_pos rfl, Finsupp.single_eq_same]
    · rw [if_neg (fun h' => h (Subtype.ext h').symm)]
      first
        | exact (Finsupp.single_eq_of_ne h).symm
        | exact (Finsupp.single_eq_of_ne (Ne.symm h)).symm
  | neg W ih => rw [map_neg, Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, ih, map_neg]
  | add a b iha ihb =>
    rw [map_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, iha, ihb, map_add]

/-- `toCycle` is injective. -/
theorem AlgebraicGeometry.Scheme.WeilDivisor.toCycle_injective {X : AlgebraicGeometry.Scheme.{u}} :
    Function.Injective (@AlgebraicGeometry.Scheme.WeilDivisor.toCycle X) := by
  intro a b hab
  apply (FreeAbelianGroup.equivFinsupp _).injective
  ext Z
  have h := AlgebraicGeometry.Scheme.WeilDivisor.toCycle_apply_eq_coeff Z a
  rw [hab, AlgebraicGeometry.Scheme.WeilDivisor.toCycle_apply_eq_coeff Z b] at h
  exact h.symm

open Classical in
/-- On a variety, `Div(X) ≅ Z_{dim X − 1}(X)` (for `dim X ≥ 1`; for `dim X = 0` the left side is `0` while the
right side contains `[X]`, since truncated subtraction gives `0 − 1 = 0`). -/
theorem WeilDivisor.toCycle_range {k : Type u} [Field k] (X : Variety k)
    (hdim : 0 < X.toScheme.dimension) :
    (@AlgebraicGeometry.Scheme.WeilDivisor.toCycle X.toScheme).range
      = CycleGroup X (X.toScheme.dimension - 1) := by
  set n := X.toScheme.dimension - 1 with hn
  have hdn : X.toScheme.dimension = n + 1 := by omega
  -- dimension formula height + coheight = dim: coheight 1 iff height dim − 1
  have hheight : ∀ x : X.toScheme, X.toScheme.IsPrimeDivisor x ↔ Order.height x = (n : ℕ∞) := by
    intro x
    have h := Variety.height_add_coheight X x
    rw [hdn] at h
    push_cast at h
    constructor
    · intro hc
      rw [AlgebraicGeometry.Scheme.IsPrimeDivisor] at hc
      rw [hc] at h
      exact WithTop.add_right_cancel WithTop.one_ne_top h
    · intro hh
      rw [hh] at h
      exact WithTop.add_left_cancel (WithTop.natCast_ne_top n) h
  -- write the domain of `toCycle` explicitly as `FreeAbelianGroup` so that `map_add`/`map_neg`/`map_sum` match syntactically
  let L : FreeAbelianGroup {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z} →+
      AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ :=
    AlgebraicGeometry.Scheme.WeilDivisor.toCycle
  have hL : ∀ W : {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z},
      L (FreeAbelianGroup.of W) = Function.locallyFinsuppWithin.single W.1 (1 : ℤ) :=
    fun W => FreeAbelianGroup.lift_apply_of _ _
  change L.range = AlgebraicGeometry.cycleSubgroup X.toScheme n
  apply le_antisymm
  · rintro c ⟨a, rfl⟩
    show L a ∈ AlgebraicGeometry.cycleSubgroup X.toScheme n
    induction a using FreeAbelianGroup.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of W =>
      intro x hx
      rw [hL, Function.locallyFinsuppWithin.single_apply] at hx
      by_cases hxe : x = W.1
      · subst hxe; exact (hheight _).1 W.2
      · exact absurd (if_neg hxe) hx
    | neg W ih => rw [map_neg]; exact neg_mem ih
    | add a b iha ihb => rw [map_add]; exact add_mem iha ihb
  · intro c hc
    have hfin : (Function.support c).Finite := by
      simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ
    have hpd : ∀ x ∈ hfin.toFinset, X.toScheme.IsPrimeDivisor x := fun x hx =>
      (hheight x).2 (hc x (by simpa using hx))
    refine ⟨∑ x ∈ hfin.toFinset.attach, c x.1 • FreeAbelianGroup.of
      (⟨x.1, hpd x.1 x.2⟩ : {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z}), ?_⟩
    show L _ = c
    rw [map_sum]
    simp only [map_zsmul, hL]
    rw [Finset.sum_attach hfin.toFinset
      (fun x => c x • Function.locallyFinsuppWithin.single x (1 : ℤ))]
    refine Function.locallyFinsuppWithin.ext fun w => ?_
    rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
      Function.locallyFinsuppWithin.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Set.Finite.mem_toFinset, Function.mem_support]
    split_ifs with hw
    · rfl
    · exact (not_not.mp hw).symm

end
