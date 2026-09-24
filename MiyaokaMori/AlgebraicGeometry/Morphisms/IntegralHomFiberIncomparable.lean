import MiyaokaMori.Prelude

/-! # Incomparability in the fibers of an integral morphism

The fibers of an integral morphism contain no nontrivial specializations: if `f` is integral,
`x ⤳ x'` and `f x = f x'`, then `x = x'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.IsIntegralHom.eq_of_specializes_of_eq {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsIntegralHom f] {x x' : X} (h : x ⤳ x')
    (hf : f.base x = f.base x') : x = x' := by
  obtain ⟨V, hV, hx'V, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (Opens.mem_top (f.base x'))
  replace hV : AlgebraicGeometry.IsAffineOpen V := hV
  have hU : AlgebraicGeometry.IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hx'U : x' ∈ f ⁻¹ᵁ V := hx'V
  have hxU : x ∈ f ⁻¹ᵁ V := h.mem_open (f ⁻¹ᵁ V).isOpen hx'U
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨p', rfl⟩ : x' ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hx'U
  have hpp' : p ⤳ p' := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h
  have hcomm := AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl
  have hmap : (AlgebraicGeometry.Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)).base p =
      (AlgebraicGeometry.Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)).base p' := by
    apply hV.fromSpec.isOpenEmbedding.injective
    have e : ∀ q, hV.fromSpec.base ((AlgebraicGeometry.Spec.map
        (f.appLE V (f ⁻¹ᵁ V) le_rfl)).base q) = f.base (hU.fromSpec.base q) := fun q => by
      rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, ← AlgebraicGeometry.Scheme.Hom.comp_apply,
        hcomm]
    rw [e, e, hf]
  congr 1
  by_contra hne
  have hint : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.IsIntegral := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE]
    simpa using AlgebraicGeometry.IsIntegralHom.isIntegral_app f V hV
  have hle : p.asIdeal ≤ p'.asIdeal := (PrimeSpectrum.le_iff_specializes p p').mpr hpp'
  have hlt : p.asIdeal < p'.asIdeal :=
    lt_of_le_of_ne hle fun e => hne (PrimeSpectrum.ext e)
  algebraize [(f.appLE V (f ⁻¹ᵁ V) le_rfl).hom]
  have := p.isPrime
  have := Ideal.IsIntegral.comap_lt_comap (R := Γ(Y, V)) hlt
  have e2 := congrArg PrimeSpectrum.asIdeal hmap
  exact this.ne e2

end
