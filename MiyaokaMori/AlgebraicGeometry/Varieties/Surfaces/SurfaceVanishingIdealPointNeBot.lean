import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface

/-! # The vanishing ideal of a closed point of a surface is nonzero

On a smooth projective surface the vanishing ideal sheaf of a closed point is not the zero ideal
sheaf (the surface is not a single point); this is the hypothesis of Stacks 02ND (the blowup of an
integral scheme along a nonzero ideal sheaf is integral).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The vanishing ideal sheaf of a closed point of a smooth projective surface is nonzero.

Proof: suppose `vanishingIdeal ⟨{p}, hp⟩ = ⊥`. `S` is reduced, so `I = ⊥ ↔ I.support = ⊤`
(`IdealSheafData.support_eq_top_iff`), and `(vanishingIdeal Z).support = Z`
(`IdealSheafData.coe_support_vanishingIdeal`). Hence `{p} = Set.univ`, `S` has a single point and
`topologicalKrullDim S = 0` (a one-point space has a single irreducible closed subset,
`Order.krullDim_nonpos_of_subsingleton`), contradicting `dim S = 2` (`S.toVariety.dim_spec`,
`S.dim_eq_two`). -/
theorem SmoothProjectiveSurface.vanishingIdeal_closedPoint_ne_bot {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds S.toScheme) ≠ ⊥ := by
  intro hbot
  -- the support of the vanishing ideal is `{p}`; if the ideal is `⊥` the support is everything
  have hsupp : ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds S.toScheme)).support : Set S.toScheme) = Set.univ := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff.mpr hbot]
    rfl
  rw [AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal] at hsupp
  -- hence the underlying space is a single point
  have hsub : Subsingleton S.toScheme := by
    refine ⟨fun a b ↦ ?_⟩
    change (({p} : Set S.toScheme) = Set.univ) at hsupp
    have ha : a ∈ ({p} : Set S.toScheme) := hsupp ▸ Set.mem_univ a
    have hb : b ∈ ({p} : Set S.toScheme) := hsupp ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff] at ha hb
    exact ha.trans hb.symm
  -- dimension bookkeeping: `dim S = 2`
  have hdim : topologicalKrullDim S.toScheme = (2 : WithBot ℕ∞) := by
    have h := S.toVariety.dim_spec
    simpa [SmoothProjectiveSurface.toVariety, S.dim_eq_two] using h
  have hkrull : Order.krullDim S.toScheme = topologicalKrullDim S.toScheme :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints S.toScheme _ _ _ :
        TopologicalSpace.IrreducibleCloseds S.toScheme ≃o S.toScheme)).symm
  have hle : Order.krullDim S.toScheme ≤ 0 := Order.krullDim_nonpos_of_subsingleton
  rw [hkrull, hdim] at hle
  exact absurd hle (by decide)

end
