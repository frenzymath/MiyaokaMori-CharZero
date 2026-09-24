import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismFiniteType
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.RegularScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverField
import MiyaokaMori.RingTheory.RegularLocalRing.SmoothOfRegularLocalizationsOverPerfectField

/-! # Regular schemes of finite type over a perfect field are smooth

A regular scheme of finite type over a perfect field is smooth over that field
(Stacks Project, Tags 00TV, 0B8X).

## Route

The route through "smooth ⇔ geometrically regular" (Stacks 038X; geometric regularity via purely
inseparable base changes, 038V (3)) is avoided, since Mathlib has neither notion. Instead we mirror the
proof of the converse `AlgebraicGeometry.isRegular_of_smoothOver` (`Stacks056s`):

1. `Smooth` is a `HasRingHomProperty` for `RingHom.Smooth`, so (`HasRingHomProperty.of_iSup_eq_top`
   with the cover by all affine opens `V` of `Y`) it suffices to show that
   `Γ(Spec k, ⊤) → Γ(Y, V)` is a smooth ring map for every affine open `V`.
2. Precomposing with the isomorphism `k ≅ Γ(Spec k, ⊤)` (`Scheme.ΓSpecIso`; `RingHom.Smooth`
   respects isomorphisms) this is `Algebra.Smooth k Γ(Y, V)`.
3. `Γ(Y, V)` is of finite type over `k` (`LocallyOfFiniteType` is the `HasRingHomProperty` for
   `RingHom.FiniteType`), and for every prime `q ⊆ Γ(Y, V)` the localization `Γ(Y, V)_q` is the
   stalk of `Y` at the corresponding point (`IsAffineOpen.isLocalization_stalk'`), which is a
   regular local ring by hypothesis.
4. `Algebra.Smooth.of_isRegularLocalRing_localization` (Stacks 00TV / 0B8X, algebraic form,
   `SmoothOfRegularLocalizationsOverPerfectField`) concludes.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

theorem isSmoothOver_of_regular_over_perfectField {k : Type u} [Field k] [PerfectField k]
    (Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hY : AlgebraicGeometry.Scheme.IsRegular Y) : IsSmoothOver k Y := by
  classical
  let pX := Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  show AlgebraicGeometry.Smooth pX
  have hft : AlgebraicGeometry.LocallyOfFiniteType pX := inferInstance
  apply AlgebraicGeometry.HasRingHomProperty.of_iSup_eq_top (P := @AlgebraicGeometry.Smooth)
    (fun V : Y.affineOpens => V) (AlgebraicGeometry.iSup_affineOpens_eq_top Y)
  intro V
  -- the ring map `k → Γ(Y, V)`
  let e := AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)
  let φ := pX.appLE ⊤ V.1 le_top
  rw [← RingHom.Smooth.respectsIso.cancel_left_isIso e.inv φ]
  let ψ : k →+* Γ(Y, V.1) := (e.inv ≫ φ).hom
  let _ : Algebra k Γ(Y, V.1) := ψ.toAlgebra
  have hsm : Algebra.Smooth k Γ(Y, V.1) := by
    -- finite type
    have hft' : RingHom.FiniteType φ.hom :=
      AlgebraicGeometry.HasRingHomProperty.appLE (P := @AlgebraicGeometry.LocallyOfFiniteType) pX hft
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ V le_top
    have hft'' : RingHom.FiniteType ψ :=
      (RingHom.finiteType_respectsIso.cancel_left_isIso e.inv φ).mpr hft'
    have : Algebra.FiniteType k Γ(Y, V.1) := hft''
    -- regular localizations
    refine Algebra.Smooth.of_isRegularLocalRing_localization fun q hq => ?_
    let y : PrimeSpectrum Γ(Y, V.1) := ⟨q, hq⟩
    have hy : V.2.fromSpec y ∈ V.1 := by
      have h := V.2.range_fromSpec
      have hmem : V.2.fromSpec y ∈ Set.range V.2.fromSpec := Set.mem_range_self y
      rw [h] at hmem
      exact hmem
    let _ : Algebra Γ(Y, V.1) (Y.presheaf.stalk (V.2.fromSpec y)) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨V.2.fromSpec y, hy⟩
    have hloc : IsLocalization.AtPrime (Y.presheaf.stalk (V.2.fromSpec y)) q :=
      V.2.isLocalization_stalk' y hy
    have hreg : IsRegularLocalRing (Y.presheaf.stalk (V.2.fromSpec y)) :=
      hY.isRegularLocalRing_stalk _
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (Y.presheaf.stalk (V.2.fromSpec y))
        (Localization.AtPrime q)).toRingEquiv
  exact hsm

end
