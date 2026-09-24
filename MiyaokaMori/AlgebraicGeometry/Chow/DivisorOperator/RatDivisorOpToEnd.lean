import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator

/-! # ℚ-divisor operators as endomorphisms of the graded Chow group

A ℚ-divisor operator is assembled into a dimension-lowering ℚ-linear endomorphism `D ↦ D̂` of the
graded Chow group `⨁_j CH_j(X)_ℚ` (the `CH_0` component is sent to `0`); the assignment is ℚ-linear in
`D`, and `capPow` and `capProd` are the restrictions of the corresponding products of endomorphisms
to the relevant components. Pairwise commuting divisor operators thus generate a commutative
subalgebra of `End`, in which the expansion of equation (2.10) of the paper (proof of
Proposition 2.4) can be carried out. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The graded Chow group with rational coefficients `⨁_j CH_j(X)_ℚ`. -/
abbrev AlgebraicGeometry.ChowRat (X : AlgebraicGeometry.Scheme.{u}) : Type u :=
  DirectSum ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j)

/-- The components of `D ↦ D̂`: the `CH_0` component is sent to `0`, and the `CH_{d+1}` component is
mapped by `D d` to `CH_d` and then embedded into the direct sum. -/

noncomputable def AlgebraicGeometry.RatDivisorOp.toEndComponent {X : AlgebraicGeometry.Scheme.{u}}
    (D : AlgebraicGeometry.RatDivisorOp X) :
    (j : ℕ) → AlgebraicGeometry.ChowGroupRat X j →ₗ[ℚ] AlgebraicGeometry.ChowRat X
  | 0 => 0
  | d + 1 => (DirectSum.lof ℚ ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j) d).comp (D d)

/-- `D̂ := DirectSum.toModule` applied to the family `toEndComponent D`; ℚ-linearity in `D` is proved
below (componentwise linearity, and `toModule` is linear in the family). -/

noncomputable def AlgebraicGeometry.RatDivisorOp.toEnd {X : AlgebraicGeometry.Scheme.{u}} :
    AlgebraicGeometry.RatDivisorOp X →ₗ[ℚ] Module.End ℚ (AlgebraicGeometry.ChowRat X) where
  toFun D := DirectSum.toModule ℚ ℕ (AlgebraicGeometry.ChowRat X)
    (AlgebraicGeometry.RatDivisorOp.toEndComponent D)
  map_add' := by
    intro D E
    apply DirectSum.linearMap_ext ℚ
    intro j
    apply LinearMap.ext
    intro x
    change (DirectSum.toModule ℚ ℕ (AlgebraicGeometry.ChowRat X)
      (AlgebraicGeometry.RatDivisorOp.toEndComponent (D + E)))
      (DirectSum.lof ℚ ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j) j x) = _
    simp only [DirectSum.toModule_lof]
    cases j with
    | zero => rfl
    | succ j =>
        simp [AlgebraicGeometry.RatDivisorOp.toEndComponent]
  map_smul' := by
    intro c D
    apply DirectSum.linearMap_ext ℚ
    intro j
    apply LinearMap.ext
    intro x
    change (DirectSum.toModule ℚ ℕ (AlgebraicGeometry.ChowRat X)
      (AlgebraicGeometry.RatDivisorOp.toEndComponent (c • D)))
      (DirectSum.lof ℚ ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j) j x) = _
    simp only [DirectSum.toModule_lof]
    cases j with
    | zero => rfl
    | succ j =>
        simp [AlgebraicGeometry.RatDivisorOp.toEndComponent]

theorem AlgebraicGeometry.RatDivisorOp.toEnd_of {X : AlgebraicGeometry.Scheme.{u}}
    (D : AlgebraicGeometry.RatDivisorOp X) (d : ℕ) (α : AlgebraicGeometry.ChowGroupRat X (d + 1)) :
    AlgebraicGeometry.RatDivisorOp.toEnd D (DirectSum.of _ (d + 1) α) = DirectSum.of _ d (D d α) := by
  rw [← DirectSum.lof_eq_of ℚ ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j)
    (d + 1) α]
  change (DirectSum.toModule ℚ ℕ (AlgebraicGeometry.ChowRat X)
      (AlgebraicGeometry.RatDivisorOp.toEndComponent D))
      (DirectSum.lof ℚ ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j) (d + 1) α) = _
  rw [DirectSum.toModule_lof]
  exact DirectSum.lof_eq_of ℚ ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j) d
    ((D d) α)

theorem AlgebraicGeometry.RatDivisorOp.toEnd_of_zero {X : AlgebraicGeometry.Scheme.{u}}
    (D : AlgebraicGeometry.RatDivisorOp X) (α : AlgebraicGeometry.ChowGroupRat X 0) :
    AlgebraicGeometry.RatDivisorOp.toEnd D (DirectSum.of _ 0 α) = 0 := by
  rw [← DirectSum.lof_eq_of ℚ ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j)
    0 α]
  change (DirectSum.toModule ℚ ℕ (AlgebraicGeometry.ChowRat X)
      (AlgebraicGeometry.RatDivisorOp.toEndComponent D))
      (DirectSum.lof ℚ ℕ (fun j => AlgebraicGeometry.ChowGroupRat X j) 0 α) = _
  rw [DirectSum.toModule_lof]
  rfl

theorem AlgebraicGeometry.RatDivisorOp.capPow_eq_pow_toEnd {X : AlgebraicGeometry.Scheme.{u}}
    (D : AlgebraicGeometry.RatDivisorOp X) (e d : ℕ) (α : AlgebraicGeometry.ChowGroupRat X (d + e)) :
    DirectSum.of _ d (AlgebraicGeometry.RatDivisorOp.capPow D e d α)
      = (AlgebraicGeometry.RatDivisorOp.toEnd D ^ e) (DirectSum.of _ (d + e) α) := by
  induction e with
  | zero =>
      simp [AlgebraicGeometry.RatDivisorOp.capPow]
  | succ e ih =>
      rw [pow_succ, Module.End.mul_apply]
      change DirectSum.of _ d
          (AlgebraicGeometry.RatDivisorOp.capPow D e d (D (d + e) α)) =
        (AlgebraicGeometry.RatDivisorOp.toEnd D ^ e)
          ((AlgebraicGeometry.RatDivisorOp.toEnd D)
            (DirectSum.of _ ((d + e) + 1) α))
      rw [AlgebraicGeometry.RatDivisorOp.toEnd_of]
      exact ih (D (d + e) α)

private theorem AlgebraicGeometry.RatDivisorOp.capList_toEnd_rev
    {X : AlgebraicGeometry.Scheme.{u}}
    (l : List (AlgebraicGeometry.RatDivisorOp X)) (d : ℕ)
    (α : AlgebraicGeometry.ChowGroupRat X (d + l.length)) :
    DirectSum.of _ d (AlgebraicGeometry.RatDivisorOp.capList l d α) =
      ((l.reverse.map (fun D => AlgebraicGeometry.RatDivisorOp.toEnd D)).prod)
        (DirectSum.of _ (d + l.length) α) := by
  induction l with
  | nil =>
      simp [AlgebraicGeometry.RatDivisorOp.capList]
  | cons D l ih =>
      simp only [AlgebraicGeometry.RatDivisorOp.capList, LinearMap.comp_apply]
      rw [ih]
      simp only [List.reverse_cons, List.map_append, List.map_singleton,
        List.prod_append, Module.End.mul_apply, List.prod_singleton, mul_one,
        List.length_cons]
      change (List.map (fun D => AlgebraicGeometry.RatDivisorOp.toEnd D) l.reverse).prod
          (DirectSum.of _ (d + l.length) (D (d + l.length) α)) =
        (List.map (fun D => AlgebraicGeometry.RatDivisorOp.toEnd D) l.reverse).prod
          ((AlgebraicGeometry.RatDivisorOp.toEnd D)
            (DirectSum.of _ ((d + l.length) + 1) α))
      exact congrArg
        (fun z => (List.map (fun E => AlgebraicGeometry.RatDivisorOp.toEnd E) l.reverse).prod z)
        (AlgebraicGeometry.RatDivisorOp.toEnd_of D (d + l.length) α).symm

private theorem AlgebraicGeometry.RatDivisorOp.of_congr
    {X : AlgebraicGeometry.Scheme.{u}} {p q : ℕ} (h : p = q)
    (α : AlgebraicGeometry.ChowGroupRat X p) :
    DirectSum.of _ p α =
      DirectSum.of _ q (AlgebraicGeometry.ChowGroupRat.congr X h α) := by
  cases h
  rfl

theorem AlgebraicGeometry.RatDivisorOp.capProd_eq_noncommProd_toEnd
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → AlgebraicGeometry.RatDivisorOp X)
    (hcomm : (Set.univ : Set ι).Pairwise fun i j =>
      Commute (AlgebraicGeometry.RatDivisorOp.toEnd (D i)) (AlgebraicGeometry.RatDivisorOp.toEnd (D j)))
    (d : ℕ) (α : AlgebraicGeometry.ChowGroupRat X (d + Fintype.card ι)) :
    DirectSum.of _ d (AlgebraicGeometry.RatDivisorOp.capProd D d α)
      = (Finset.univ.noncommProd (fun i => AlgebraicGeometry.RatDivisorOp.toEnd (D i))
          (hcomm.mono (by simp))) (DirectSum.of _ (d + Fintype.card ι) α) := by
  let l := (Finset.univ : Finset ι).toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hrev : l.reverse.Nodup := List.nodup_reverse.mpr hl
  have hfin : l.reverse.toFinset = (Finset.univ : Finset ι) := by
    rw [List.toFinset_reverse, Finset.toList_toFinset]
  have hlen : l.length = Fintype.card ι := by
    simp [l]
  have hdim : d + l.length = d + Fintype.card ι := by
    rw [hlen]
  let m : List (AlgebraicGeometry.RatDivisorOp X) := l.map D
  have hm : m.length = Fintype.card ι := by simp [m, l]
  let β : AlgebraicGeometry.ChowGroupRat X (d + m.length) :=
    AlgebraicGeometry.ChowGroupRat.congr X (by simp [hm]) α
  have hcap :
      DirectSum.of _ d (AlgebraicGeometry.RatDivisorOp.capProd D d α) =
        (m.reverse.map (fun E => AlgebraicGeometry.RatDivisorOp.toEnd E)).prod
          (DirectSum.of _ (d + m.length) β) := by
    change DirectSum.of _ d ((AlgebraicGeometry.RatDivisorOp.capList m d) β) = _
    exact AlgebraicGeometry.RatDivisorOp.capList_toEnd_rev m d β
  rw [hcap]
  have hprod :
      (Finset.univ.noncommProd (fun i => AlgebraicGeometry.RatDivisorOp.toEnd (D i))
          (hcomm.mono (by simp))) =
        (m.reverse.map (fun E => AlgebraicGeometry.RatDivisorOp.toEnd E)).prod := by
    have hpair : (l.reverse.toFinset : Set ι).Pairwise
        (fun i j => Commute (AlgebraicGeometry.RatDivisorOp.toEnd (D i))
          (AlgebraicGeometry.RatDivisorOp.toEnd (D j))) := by
      simpa [hfin] using hcomm
    have hp := Finset.noncommProd_toFinset l.reverse
      (fun i => AlgebraicGeometry.RatDivisorOp.toEnd (D i)) hpair hrev
    simpa [m, List.map_reverse, List.map_map, Function.comp_def, hfin] using hp
  rw [hprod]
  have hβ : DirectSum.of _ (d + m.length) β =
      DirectSum.of _ (d + Fintype.card ι) α := by
    simpa [β] using
      (AlgebraicGeometry.RatDivisorOp.of_congr (by simp [hm]) α).symm
  exact congrArg
    (fun z => (m.reverse.map (fun E => AlgebraicGeometry.RatDivisorOp.toEnd E)).prod z) hβ

end
