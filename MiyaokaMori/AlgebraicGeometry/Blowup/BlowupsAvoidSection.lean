import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerAvoiding
import MiyaokaMori.AlgebraicGeometry.Blowup.EliminationOfIndeterminacy
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Morphisms.RationalMapPrecomp
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Morphisms.BlowupSequenceIsoOverOpen

/-! # Elimination of indeterminacy avoiding the regular locus

For a rational map `φ : W ⇢ Y` from a smooth projective surface to a projective `k`-scheme, regular on an
open set `U`, the resolving tower `β : S → W` can be chosen with all centres avoiding the successive
inverse images of `U`; then `β` is an isomorphism over `U`, and the resolved morphism `Ψ` agrees with `φ`
on all of `β⁻¹(U)`. This is how the paper resolves `W ⇢ X` while preserving the zero section
(proof of Corollary 4.3, §4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Elimination of indeterminacy for `φ : W ⇢ Y`, regular on `U`: there is a tower of point blowups
`β : S → W` avoiding `U`, an isomorphism over `U`, and a morphism `Ψ : S → Y` resolving `φ` that agrees
with `φ` on `β⁻¹(U)`. -/
theorem elimination_avoiding_regular_locus {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.IsSeparated] (hY : IsProjectiveOver k Y)
    (φ : W.toScheme ⤏ Y) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : W.toScheme.Opens) (hU : IsRegularOn φ U) :
    ∃ (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ W.toScheme)
      (_ : IsBlowupTower β) (_ : IsBlowupTowerAvoiding β (U : Set W.toScheme))
      (hβd : AlgebraicGeometry.IsDominant β) (Ψ : S.toScheme ⟶ Y),
      Ψ.toRationalMap = (haveI := hβd; φ.precomp β) ∧
      CategoryTheory.IsIso (β ∣_ U) ∧
      (β ⁻¹ᵁ U).ι ≫ Ψ = (β ∣_ U) ≫ W.toScheme.homOfLE hU ≫ φ.toPartialMap.hom := by
  obtain ⟨S, β, hβ, havoid, hβd, Ψ, hΨ, hagree⟩ :=
    elimination_of_indeterminacy_agree W Y hY φ U hU
  exact ⟨S, β, hβ, havoid, hβd, Ψ, hΨ,
    MiyaokaMori.Statement.IsPointBlowupSequenceOver.isIso_morphismRestrict U β havoid,
    AlgebraicGeometry.morphismRestrict_agree_of_le β φ.domain U hU Ψ φ.toPartialMap.hom hagree⟩

end
