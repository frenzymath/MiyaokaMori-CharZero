import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.PrincipalDivisorFiniteness
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrder
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrderChartIndependent

/-! # Only finitely many weighted orders are nonzero

Only finitely many `z` have `β_z ≠ 0`: finitely many charts cover, and each coordinate has finitely many zeros and
poles (§3 of the paper: "a finite chart cover and the divisors of the rational coordinates show that only finitely
many `β_z` are nonzero").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem finite_support_weightedOrder {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} {n κ : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0) :
    {z : Ct.toScheme | weightedOrderQ a hne z ≠ 0}.Finite := by
  have : CompactSpace Ct.toScheme :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (Ct.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hcoord (p : Fin (n + 1) × Fin κ) (hp : a p.1 p.2 ≠ 0) :
      {z : Ct.toScheme | Ct.toScheme.ord (a p.1 p.2) z ≠ 0}.Finite := by
    apply (AlgebraicGeometry.Scheme.finite_ord_ne_zero (X := Ct.toScheme) hp).subset
    intro z hz
    by_cases hco : Order.coheight z = 1
    · exact ⟨hco, hz⟩
    · exact False.elim (hz (AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hco _))
  have hfinite : (⋃ p ∈ {p : Fin (n + 1) × Fin κ | a p.1 p.2 ≠ 0},
      {z : Ct.toScheme | Ct.toScheme.ord (a p.1 p.2) z ≠ 0}).Finite :=
    Set.Finite.biUnion (Set.toFinite _) hcoord
  apply hfinite.subset
  intro z hz
  -- the minimum is attained at some nonzero coordinate `p`; `β_z ≠ 0` forces `ord_z(a_p) ≠ 0`
  obtain ⟨p, hp0, hp⟩ := weightedOrder_attained a hne z
  refine Set.mem_biUnion hp0 ?_
  intro ho
  apply hz
  rw [hp, ho]
  simp

end
