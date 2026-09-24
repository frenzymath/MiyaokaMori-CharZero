import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface

/-! # Closed subsets of codimension two in a surface are finite

A closed subset of a smooth projective surface containing no point of codimension `≤ 1` is a
finite set of closed points (after extending a rational map over the codimension-one points, only
finitely many closed points of indeterminacy remain).

Sources: Debarre 5.17, last sentence; the second sentence of the proof of Stacks 0C5H.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A closed subset of a smooth projective surface with no point of coheight `≥ 1` is finite. -/
theorem closed_subset_codim_two_finite {k : Type u} [Field k]
    (W : SmoothProjectiveSurface k) (Z : Set W.toScheme) (hZ : IsClosed Z)
    (hcodim : ∀ z ∈ Z, 2 ≤ ringKrullDim (W.toScheme.presheaf.stalk z)) :
    Z.Finite ∧ ∀ z ∈ Z, IsClosed {z} := by
  have hdim : topologicalKrullDim W.toScheme = (2 : WithBot ℕ∞) := by
    have h := W.toVariety.dim_spec
    simpa [SmoothProjectiveSurface.toVariety, W.dim_eq_two] using h
  have hkrull : Order.krullDim W.toScheme = topologicalKrullDim W.toScheme :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints W.toScheme _ _ _ :
        TopologicalSpace.IrreducibleCloseds W.toScheme ≃o W.toScheme)).symm
  have hcoheight (z : W.toScheme) : Order.coheight z ≤ (2 : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    calc
      (Order.coheight z : WithBot ℕ∞) ≤ Order.krullDim W.toScheme :=
        Order.coheight_le_krullDim z
      _ = topologicalKrullDim W.toScheme := hkrull
      _ = ((2 : ℕ∞) : WithBot ℕ∞) := by simpa using hdim
  have hclosed : ∀ z ∈ Z, IsClosed ({z} : Set W.toScheme) := by
    intro z hz
    have hcoheight_ge : (2 : ℕ∞) ≤ Order.coheight z := by
      have h := hcodim z hz
      rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight z] at h
      change ((2 : ℕ∞) : WithBot ℕ∞) ≤
        (Order.coheight z : WithBot ℕ∞) at h
      exact WithBot.coe_le_coe.mp h
    have hcoheight_eq : Order.coheight z = 2 :=
      le_antisymm (hcoheight z) hcoheight_ge
    apply closure_eq_iff_isClosed.mp
    apply Set.Subset.antisymm
    · intro y hy
      have hyz : y ≤ z :=
        AlgebraicGeometry.Scheme.le_iff_specializes.mpr
          (specializes_iff_mem_closure.mpr hy)
      have hzy : z ≤ y := by
        by_contra h
        have hlt : Order.coheight z < Order.coheight y :=
          Order.coheight_strictAnti (lt_of_le_not_ge hyz h)
            (hcoheight_eq.symm ▸ ENat.natCast_lt_top 2)
        rw [hcoheight_eq] at hlt
        exact (not_lt_of_ge (hcoheight y)) hlt
      exact ((AlgebraicGeometry.Scheme.le_iff_specializes.mp hzy).antisymm
        (AlgebraicGeometry.Scheme.le_iff_specializes.mp hyz)).eq
    · exact subset_closure
  have : AlgebraicGeometry.IsNoetherian W.toScheme := W.toVariety.isNoetherian
  obtain ⟨S, hSfinite, hSclosed, hSirreducible, hSsup⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have hcomponent_finite : ∀ T ∈ S, T.Finite := by
    intro T hT
    let η := (hSirreducible T hT).genericPoint
    have hηgeneric : IsGenericPoint η T :=
      (hSirreducible T hT).isGenericPoint_genericPoint (hSclosed T hT)
    have hTZ : T ⊆ Z := by
      intro z hz
      rw [hSsup]
      exact Set.subset_sUnion_of_mem hT hz
    have hηclosed : IsClosed ({η} : Set W.toScheme) := hclosed η (hTZ hηgeneric.mem)
    have hTsingleton : T = {η} := by
      rw [← (hSirreducible T hT).closure_genericPoint (hSclosed T hT),
        hηclosed.closure_eq]
    rw [hTsingleton]
    exact Set.finite_singleton η
  constructor
  · rw [hSsup]
    exact hSfinite.sUnion hcomponent_finite
  · exact hclosed

end
