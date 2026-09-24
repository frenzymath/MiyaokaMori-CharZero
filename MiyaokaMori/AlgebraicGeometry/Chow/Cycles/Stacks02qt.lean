import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk

/-! # Finiteness of the multiplicity at a generic point (Stacks 02QT)

Stacks 02QT: if `X` is locally Noetherian, `Z ⊆ X` a closed subscheme and `ξ` the generic point of an
irreducible component of `Z`, then `length_{O_{X,ξ}} O_{Z,ξ} < ∞` (`O_{Z,ξ}` is a zero-dimensional
Noetherian local ring); for `Z = X` this is `length O_{X,ξ} < ∞`.

Source: Stacks 02QT (finiteness of the multiplicities in the fundamental cycle, Stacks 02QU). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.length_stalk_lt_top_of_coheight_eq_zero {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (ξ : X) (hξ : Order.coheight ξ = 0) :
    Module.length (X.presheaf.stalk ξ) (X.presheaf.stalk ξ) < ⊤ := by
  -- coheight ξ = 0 ⇒ the stalk has Krull dimension ≤ 0; locally Noetherian ⇒ the stalk is Noetherian;
  -- Hopkins–Levitzki ⇒ Artinian ⇒ finite length
  have : Ring.KrullDimLE 0 (X.presheaf.stalk ξ) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le (n := 0) (by simp [hξ])
  have hart : IsArtinian (X.presheaf.stalk ξ) (X.presheaf.stalk ξ) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  rw [lt_top_iff_ne_top, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, hart⟩

end
