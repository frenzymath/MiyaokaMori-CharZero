import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.DivisorToOneCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.FiberDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.FiberDivisorSupport
import MiyaokaMori.Paper.S4Completion.FiberOneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrimeDivisorDecomposition

/-! # Decomposition of a fibre divisor

`π_S^*(y) = Σ_i m_i Γ_i` with `m_i ∈ ℤ_{>0}`, where the `Γ_i` are the integral components of the
reduced support of the fibre.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The fibre divisor over a closed point is a positive integral combination of the integral
components of the fibre. -/
theorem fiberDivisor_eq_sum {k : Type u} [Field k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ)
      (Γ : ι → IntegralCurve k S.toScheme),
      (∀ i, 0 < m i) ∧ Function.Injective Γ ∧
      (⋃ i, Set.range (Γ i).ι.base) = π.base ⁻¹' {y} ∧
      fiberCycle π hπ y = ∑ i, (m i : ℤ) • (Γ i).fundamentalClass := by
  classical
  obtain ⟨ι, hι, m, Γ, hm, hΓinj, hcycle⟩ :=
    effective_divisor_eq_sum_prime (fiberDivisor π hπ y)
      (fiberDivisor_effective π hπ y)
  letI : Fintype ι := hι
  have coe_cast_cycleGroup {a b : ℕ} (h : a = b) (c : CycleGroup S.toVariety a) :
      ((cast (congrArg (fun n : ℕ => ↥(CycleGroup S.toVariety n)) h) c :
        CycleGroup S.toVariety b) : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) = c.1 := by
    cases h
    rfl
  let η : ι → S.toScheme := fun i =>
    (Γ i).ι.base (genericPoint (Γ i).carrier)
  have hfund (i : ι) :
      ((Γ i).fundamentalClass : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) =
        Function.locallyFinsuppWithin.single (η i) (1 : ℤ) := by
    unfold IntegralCurve.fundamentalClass
    rw [coe_cast_cycleGroup (Γ i).dimension_eq_one]
    exact ClosedSubvariety.fundamentalClass_eq_single (Γ i).toClosedSubvariety
  have hgeneric (i : ι) :
      IsGenericPoint (η i) (closure (Set.range (Γ i).ι.base)) := by
    simpa [η, Set.image_univ] using
      (genericPoint_spec (Γ i).carrier).image (Γ i).ι.continuous
  have hrange (i : ι) :
      Set.range (Γ i).ι.base = closure ({η i} : Set S.toScheme) := by
    calc
      Set.range (Γ i).ι.base = closure (Set.range (Γ i).ι.base) :=
        (Γ i).ι.isClosedEmbedding.isClosed_range.closure_eq.symm
      _ = closure ({η i} : Set S.toScheme) := (hgeneric i).def.symm
  have hcoeff (z : S.toScheme) :
      ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) z =
        ∑ i, (m i : ℤ) * if η i = z then 1 else 0 := by
    have hz := congrArg
      (fun Z : OneCycle S.toVariety =>
        (Z : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) z) hcycle
    simpa [fiberCycle, hfund, Function.locallyFinsuppWithin.single_apply, Pi.single_apply, eq_comm] using hz
  refine ⟨ι, hι, m, Γ, hm, hΓinj, ?_, hcycle⟩
  rw [fiberDivisor_support π hπ y hy]
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i, hz⟩ := Set.mem_iUnion.mp hz
    have hηnonzero :
        ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) (η i) ≠ 0 := by
      have hpos : 0 < ∑ j, (m j : ℤ) * if η j = η i then 1 else 0 := by
        apply Finset.sum_pos'
        · intro j hj
          by_cases hji : η j = η i <;> simp [hji, hm j]
        · exact ⟨i, Finset.mem_univ _, by simp [hm i]⟩
      intro hzero
      rw [← hcoeff (η i), hzero] at hpos
      exact (lt_irrefl 0 hpos)
    apply Set.mem_iUnion.mpr ⟨η i, ?_⟩
    apply Set.mem_iUnion.mpr ⟨hηnonzero, ?_⟩
    rw [← hrange i]
    exact hz
  · intro z hz
    obtain ⟨η', hzη⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hη', hzη⟩ := Set.mem_iUnion.mp hzη
    have hex : ∃ i, η i = η' := by
      by_contra hnone
      have hzero :
          ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) η' = 0 := by
        rw [hcoeff]
        apply Finset.sum_eq_zero
        intro i hi
        by_cases hii : η i = η'
        · exact (hnone ⟨i, hii⟩).elim
        · simp [hii]
      exact hη' hzero
    obtain ⟨i, hi⟩ := hex
    subst η'
    apply Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [hrange i]
    exact hzη

end
