import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Sections of an affine open after an affine base change

Let `X' = X ×_{Spec A} Spec A'` and let `V ⊆ X` be an affine open. Then
`Γ(X', g'⁻¹V) = A' ⊗_A Γ(X, V)`, i.e. the square of rings is a pushout in `CommRingCat`.
Proof: `g'⁻¹V ≅ V ×_{Spec A} Spec A'`, and the fibre product of affine schemes is the `Spec` of the
tensor product. References: Stacks Project, Tag 01JQ; Hartshorne II.3.3.

Mathlib already contains this: `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`
(`Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`) gives, for any pullback square
`IsPullback g iY iX f` and affine opens `US, UT, UX`, an isomorphism
`Γ(X, UX) ⊗_{Γ(S, US)} Γ(T, UT) ≅ Γ(Y, g⁻¹UX ⊓ iY⁻¹UT)`, which by `isIso_pushoutSection_iff` is the
pushout square of the `appLE` maps. Here we take `US = UT = ⊤`, `UX = V`, and change the corners
along `ΓSpecIso A`, `ΓSpecIso A'` with `IsPushout.of_iso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **Coordinate rings of an affine fibre product.** Let `X' = X ×_{Spec A} Spec A'`, `V ⊆ X` an
affine open and `V' = g'⁻¹V`. Then the square of rings `A → A'`, `A → Γ(X, V)`, `A' → Γ(X', V')`,
`Γ(X, V) → Γ(X', V')` is a pushout in `CommRingCat`, i.e. `Γ(X', V') = A' ⊗_A Γ(X, V)`.

Mathematical argument: `g'⁻¹V ≅ V ×_{Spec A} Spec A'` (base change of an open immersion,
`AlgebraicGeometry.pullbackRestrictIsoRestrict`); `V ≅ Spec Γ(X, V)` (`hV.isoSpec`), hence
`V ×_{Spec A} Spec A' ≅ Spec Γ(X,V) ×_{Spec A} Spec A' ≅ Spec (Γ(X,V) ⊗_A A')`
(`AlgebraicGeometry.pullbackSpecIso`); take global sections and use `Scheme.ΓSpecIso`. The four edges
agree with the ring homomorphisms in the statement by `pullback.condition` and the naturality of
`ΓSpecIso`. Equivalently: `Spec` is a contravariant equivalence onto affine schemes, so pullback
squares of affine schemes correspond to pushout squares of coordinate rings.
References: Stacks Project, Tag 01JQ; the first step of Hartshorne II.3.3.

Edge cases: for `V = ∅`, `Γ(X, V) = 0`, `V' = ∅` and `0 = A' ⊗_A 0`; for `A' = 0`, `X' = ∅`.

The formal proof uses Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen` and
`isIso_pushoutSection_iff` for the pullback square `IsPullback.of_hasPullback f (Spec.map φ)` with
opens `US = UT = ⊤`, `UX = V`, which gives
`IsPushout (f.appLE ⊤ V) ((Spec.map φ).appLE ⊤ ⊤) (fst.appLE V V') (snd.appLE ⊤ V')`; then `flip`
and `IsPushout.of_iso` along `ΓSpecIso A`, `ΓSpecIso A'` (with `Iso.refl` at the other two corners)
produce the four edges of the statement (`(Spec.map φ).appTop` corresponds to `φ` by
`ΓSpecIso_naturality`). -/
theorem isPushout_sections_of_affine {A A' : CommRingCat.{u}} {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec A) (φ : A ⟶ A') (V : X.Opens)
    (hV : AlgebraicGeometry.IsAffineOpen V)
    (V' : (Limits.pullback f (AlgebraicGeometry.Spec.map φ)).Opens)
    (h : V' ≤ (Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ V)
    (hV' : V' = (Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ V) :
    IsPushout φ
      (((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop) ≫
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op)
      (((AlgebraicGeometry.Scheme.ΓSpecIso A').inv ≫
          (Limits.pullback.snd f (AlgebraicGeometry.Spec.map φ)).appTop) ≫
        (Limits.pullback f (AlgebraicGeometry.Spec.map φ)).presheaf.map
          (homOfLE (le_top : V' ≤ ⊤)).op)
      ((Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)).appLE V V' h) := by
  subst hV'
  have H := IsPullback.of_hasPullback f (AlgebraicGeometry.Spec.map φ)
  have hP := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) le_top le_top
      (UY := (Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ V) (by simp)).mp
    (isIso_pushoutSection_of_isAffineOpen H le_top le_top (by simp)
      (isAffineOpen_top _) (isAffineOpen_top _) hV)
  refine hP.flip.of_iso (AlgebraicGeometry.Scheme.ΓSpecIso A) (AlgebraicGeometry.Scheme.ΓSpecIso A')
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · show (AlgebraicGeometry.Spec.map φ).appLE ⊤ ((AlgebraicGeometry.Spec.map φ) ⁻¹ᵁ ⊤) le_rfl ≫ _ = _
    rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
    exact AlgebraicGeometry.Scheme.ΓSpecIso_naturality φ
  · simp [AlgebraicGeometry.Scheme.Hom.appLE]
  · simp [AlgebraicGeometry.Scheme.Hom.appLE]
  · simp

end AlgebraicGeometry.Scheme.Modules

end
