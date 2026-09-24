import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.DivisorToOneCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycleSumOfIntegralCurves

/-! # Decomposition of an effective divisor on a surface into prime divisors

An effective divisor on a smooth projective surface is a positive integer combination of prime divisors
(integral curves); this is the fibre decomposition `π_S^*(y) = Σ m_i Γ_i` in the proof of Lemma 5.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Auxiliary form of `effective_divisor_eq_sum_prime` for an arbitrary one-cycle `Z` with
non-negative coefficients on a smooth projective variety `X`: `Z = Σ_i m_i [Γ_i]` with `m_i > 0`
and pairwise distinct integral curves `Γ_i`, indexed by `Fin N : Type`.

Proof: `OneCycle.eq_sum_fundamentalClass` writes `Z = Σ_{Γ ∈ s} Z(η_Γ) • [Γ]` over a finite set
`s` of integral curves. Drop the terms with `Z(η_Γ) = 0` (`Finset.sum_filter_of_ne`), enumerate
the remaining set `s'` by `Fin s'.card` (`Finset.equivFin`), and take `m i := (Z(η_{e i})).toNat`,
which is positive because the coefficient is non-zero and `≥ 0` by hypothesis. -/
private theorem oneCycle_nonneg_eq_sum_prime {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} (Z : OneCycle X.toVariety)
    (hZ : ∀ p : X.toScheme, 0 ≤ (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) p) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ)
      (Γ : ι → IntegralCurve k X.toScheme),
      (∀ i, 0 < m i) ∧ Function.Injective Γ ∧
      Z = ∑ i, (m i : ℤ) • (Γ i).fundamentalClass := by
  classical
  obtain ⟨s, hs⟩ := OneCycle.eq_sum_fundamentalClass Z
  let c : IntegralCurve k X.toScheme → ℤ := fun Γ =>
    (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) (Γ.ι.base (genericPoint Γ.carrier))
  let s' : Finset (IntegralCurve k X.toScheme) := s.filter (fun Γ => c Γ ≠ 0)
  let e : Fin s'.card ≃ s' := s'.equivFin.symm
  refine ⟨Fin s'.card, inferInstance, fun i => (c (e i).1).toNat, fun i => (e i).1, ?_, ?_, ?_⟩
  · intro i
    have h0 : c (e i).1 ≠ 0 := (Finset.mem_filter.mp (e i).2).2
    have hnn : 0 ≤ c (e i).1 := hZ _
    have hpos : 0 < c (e i).1 := lt_of_le_of_ne hnn (Ne.symm h0)
    exact Int.lt_toNat.mpr (by exact_mod_cast hpos)
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · have hfilter : ∑ Γ ∈ s', c Γ • Γ.fundamentalClass = ∑ Γ ∈ s, c Γ • Γ.fundamentalClass := by
      apply Finset.sum_filter_of_ne
      intro Γ _ hne hc
      apply hne
      rw [hc, zero_smul]
    have htoNat : ∀ i : Fin s'.card, ((c (e i).1).toNat : ℤ) = c (e i).1 := by
      intro i
      exact Int.toNat_of_nonneg (hZ _)
    calc
      Z = ∑ Γ ∈ s, c Γ • Γ.fundamentalClass := hs
      _ = ∑ Γ ∈ s', c Γ • Γ.fundamentalClass := hfilter.symm
      _ = ∑ x : s', c x.1 • x.1.fundamentalClass := (Finset.sum_coe_sort s' _).symm
      _ = ∑ i : Fin s'.card, c (e i).1 • (e i).1.fundamentalClass :=
          (Equiv.sum_comp e (fun x : s' => c x.1 • x.1.fundamentalClass)).symm
      _ = ∑ i : Fin s'.card, ((c (e i).1).toNat : ℤ) • (e i).1.fundamentalClass := by
          apply Finset.sum_congr rfl
          intro i _
          rw [htoNat i]

/-- An effective Cartier divisor on a smooth projective surface is `Σ_i m_i [Γ_i]` with `m_i > 0` and pairwise
distinct integral curves `Γ_i`. -/
theorem effective_divisor_eq_sum_prime {k : Type u} [Field k]
    {S : SmoothProjectiveSurface k} (D : CartierDivisor S.toVariety)
    (hD : CartierDivisor.Effective D) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ)
      (Γ : ι → IntegralCurve k S.toScheme),
      (∀ i, 0 < m i) ∧ Function.Injective Γ ∧
      (⟨(D.weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ), by
          have hmem := D.weilCycle.2
          generalize (D.weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) = z at hmem ⊢
          have h : S.toVariety.toScheme.dimension - 1 = 1 := by
            rw [← Variety.dim_eq_scheme_dimension, S.dim_eq_two]
          rw [h] at hmem
          exact hmem⟩ : OneCycle S.toVariety)
        = ∑ i, (m i : ℤ) • (Γ i).fundamentalClass := by
  exact oneCycle_nonneg_eq_sum_prime (X := S.toSmoothProjectiveVariety) _ (fun p => hD p)

end
