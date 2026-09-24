import MiyaokaMori.Prelude

/-! # Pullback of a partial map along a morphism

The pullback of a partial map `g : X ⤏ Z` along a morphism `f : X' → X`: the partial map `(f|) ≫ g` defined
on `f⁻¹(dom g)` (which is required to be dense); when `f` is dominant and `X'` is irreducible, density is
automatic.

Reference: Debarre, *Introduction to Mori theory*, 5.17–5.18 (the composite `π ∘ ε`); Stacks Project,
around Tag 01RR (composition of rational maps).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- The pullback of `g` along `f`: domain `f⁻¹(dom g)`, morphism `(f ∣_ dom g) ≫ g.hom`. -/
def AlgebraicGeometry.Scheme.PartialMap.pullbackAlong {X' X Z : Scheme.{u}} (g : X.PartialMap Z)
    (f : X' ⟶ X) (hd : Dense ((f ⁻¹ᵁ g.domain : X'.Opens) : Set X')) : X'.PartialMap Z where
  domain := f ⁻¹ᵁ g.domain
  dense_domain := hd
  hom := (f ∣_ g.domain) ≫ g.hom

/-- If `f` is dominant and `X'` is irreducible, the preimage of a dense open set is dense. -/
theorem AlgebraicGeometry.Scheme.Hom.dense_preimage_of_isDominant {X' X : Scheme.{u}}
    [IrreducibleSpace X'] (f : X' ⟶ X) [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) :
    Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X') := by
  have : Nonempty X := ⟨f (Classical.arbitrary X')⟩
  have hne : (U : Set X).Nonempty := hU.nonempty
  obtain ⟨x', hx'⟩ := f.denseRange.exists_mem_open U.2 hne
  exact (f ⁻¹ᵁ U).2.dense ⟨x', hx'⟩

end
