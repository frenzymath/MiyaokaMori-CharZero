import MiyaokaMori.Prelude

/-! # Transport of short exactness along isomorphisms

Given isomorphisms at the three terms of a short complex satisfying the two commutation relations,
short exactness of the source transports to the target.

Proof: assemble the three isomorphisms and the commutation relations into an isomorphism of short
complexes with `ShortComplex.isoMk`, then apply `ShortComplex.shortExact_of_iso`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem shortExact_transport_of_iso {𝒞 : Type u} [Category 𝒞]
    [HasZeroMorphisms 𝒞] {S T : ShortComplex 𝒞}
    (a₁ : S.X₁ ≅ T.X₁) (a₂ : S.X₂ ≅ T.X₂) (a₃ : S.X₃ ≅ T.X₃)
    (h₁ : a₁.hom ≫ T.f = S.f ≫ a₂.hom)
    (h₂ : a₂.hom ≫ T.g = S.g ≫ a₃.hom)
    (hS : S.ShortExact) : T.ShortExact := by
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk a₁ a₂ a₃ h₁ h₂) hS

end
