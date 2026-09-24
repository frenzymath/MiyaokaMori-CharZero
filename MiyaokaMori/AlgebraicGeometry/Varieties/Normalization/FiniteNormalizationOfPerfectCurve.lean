import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainIntegralClosureFiniteCharP
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.CurveFieldNormalizationFinite

/-! # Finiteness of the normalization of an integral curve over a perfect field

If `Γ` is an integral curve in a smooth projective variety, the canonical morphism from the
relative normalization of `Γ` in its function field to `Γ` is finite.

Proof sketch:
1. `curveFieldNormalizationMap Γ K(Γ)` is by definition
   `(curveExtensionGenericMap Γ K(Γ)).fromNormalization`, the projection of Mathlib's relative
   normalization; it is integral, hence affine, so finiteness can be checked on each affine open
   `U ⊆ Γ`: the section map `Γ(Γ,U) → Γ(Γ^ν, ν⁻¹U)` must be module-finite.
2. `curveFieldNormalizationSectionsFieldIso` identifies `Γ(Γ^ν, ν⁻¹U)` (`U` nonempty affine) with
   the integral closure of `Γ(Γ,U)` in `K(Γ)`, with the section map corresponding to the structure
   map (`curveFieldNormalizationMap_app_sectionsFieldIso`). `IsIntegralClosure.finite` would need
   `Γ(Γ,U)` integrally closed, which fails for a singular curve, so "the integral closure is
   module-finite" is taken as a hypothesis (`curveFieldNormalizationMap_isFinite_of_forall_module_finite`);
   the empty open is trivial.
3. `Γ(Γ,U)` (`U` nonempty affine) is a domain (`Γ` integral) and a finitely generated `k`-algebra
   (the structure morphism `Γ.ι ≫ (X ↘ Spec k)` is locally of finite type: a closed immersion is
   finite and `X` is of finite type), with fraction field `K(Γ)`
   (`functionField_isFractionRing_of_isAffineOpen`). So "the integral closure is module-finite" is
   the purely algebraic statement N-1: **the normalization of a finitely generated domain over a
   perfect field is module-finite** (`Ring.module_finite_integralClosure_of_finiteType_of_perfectField`).
4. N-1 splits by characteristic: in characteristic `0` it is
   `Ring.module_finite_integralClosure_of_finiteType` (Noether normalization and Stacks 032L); in
   characteristic `p > 0` it is `Ring.module_finite_integralClosure_of_finiteType_of_charP` (the
   perfect field case of Stacks 0335 / 032M).

Sources: Stacks 0335 (algebras of finite type over a field are Nagata), 032L, 00OW.

Why the adapters of `Stacks0bxs.lean` do not apply directly: `normalization_isFinite_of_locallyAlgebraic`
requires the source `Y` to be locally of finite type over `k`, and
`normalization_isFinite_of_locallyOfFiniteType` requires `f : Y → X` to be locally of finite type;
here `Y = Spec K(Γ)`, and `K(Γ)` is an extension of `k` of transcendence degree `1`, **not** a
finitely generated `k`-algebra, while `Spec K(Γ) → Γ` (the inclusion of the generic point) is not
locally of finite type either. Likewise `Algebra.finite_integralClosure_of_finiteType_over_field`
(`Stacks035b.lean`) requires `C` to be of finite type over `A`, which `C = K(Γ)` is not.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## (B) Geometric bridge: module-finite integral closures on affine opens give a finite normalization projection -/

/-- On a nonempty affine open `U`, if the integral closure of `Γ(X,U)` in `L` is a finite
`Γ(X,U)`-module, then the section map of the normalization projection over `U` is a finite ring
map. This is `curveFieldNormalizationMap_finite_app` with the hypotheses "`Γ(X,U)` integrally
closed and `L` separable" replaced by module-finiteness of the integral closure. -/
theorem curveFieldNormalizationMap_finite_app_of_module_finite
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (U : X.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U]
    (hfin : letI := AlgebraicGeometry.Scheme.Covers.curveExtensionSectionAlgebra X L U
      Module.Finite Γ(X, U) ↥(integralClosure Γ(X, U) L)) :
    ((AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X L).app U).hom.Finite := by
  let _ := AlgebraicGeometry.Scheme.Covers.curveExtensionSectionAlgebra X L U
  let e := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationSectionsFieldIso X L U hU
  have he : (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X L).app U =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) ≫ e.inv := by
    rw [← AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap_app_sectionsFieldIso X L U hU]
    simp only [Category.assoc, e, Iso.hom_inv_id, Category.comp_id]
  rw [he, CommRingCat.hom_comp]
  exact e.commRingCatIsoToRingEquiv.symm.finite.comp
    (RingHom.finite_algebraMap.mpr hfin)

/-- If on every nonempty affine open `U` the integral closure of `Γ(X,U)` in `L` is a finite
`Γ(X,U)`-module, then the normalization projection `curveFieldNormalizationMap X L` is a finite
morphism (on the empty open the section ring is trivial). -/
theorem curveFieldNormalizationMap_isFinite_of_forall_module_finite
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (hfin : ∀ (U : X.affineOpens) [Nonempty U.1],
      letI := AlgebraicGeometry.Scheme.Covers.curveExtensionSectionAlgebra X L U.1
      Module.Finite Γ(X, U.1) ↥(integralClosure Γ(X, U.1) L)) :
    AlgebraicGeometry.IsFinite (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X L) := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · exact curveFieldNormalizationMap_finite_app_of_module_finite X L U hU (hfin ⟨U, hU⟩)
  · have hUbot : U = ⊥ := (Opens.not_nonempty_iff_eq_bot U).mp
      fun h ↦ hne (Opens.nonempty_coeSort.mpr h)
    subst U
    have : Subsingleton Γ(AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X L,
        AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X L ⁻¹ᵁ (⊥ : X.Opens)) :=
      inferInstanceAs (Subsingleton Γ(AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X L,
        (⊥ : (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X L).Opens)))
    apply RingHom.Finite.of_surjective
    intro a
    exact ⟨0, Subsingleton.elim _ _⟩

/-! ## (C) Section rings of an integral curve are finitely generated `k`-algebras -/

/-- When the structure morphism is locally of finite type, the section ring of an affine open is a
finitely generated `k`-algebra (`k`-structure via `ΓSpecIso` and `appLE ⊤ U`). -/
private theorem finiteType_sections_of_locallyOfFiniteType {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ U le_top).hom).FiniteType := by
  have h1 : ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ U le_top).hom.FiniteType :=
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).finiteType_appLE
      (AlgebraicGeometry.isAffineOpen_top _) hU _
  have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

/-- The structure morphism `Γ.ι ≫ (X ↘ Spec k)` of an integral curve `Γ ⊆ X` is locally of finite
type (a closed immersion is finite and `X` is of finite type). -/
theorem IntegralCurve.locallyOfFiniteType_over {k : Type u} [Field k]
    {X : Variety k} (Γ : IntegralCurve k X.toScheme) :
    AlgebraicGeometry.LocallyOfFiniteType (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  change AlgebraicGeometry.LocallyOfFiniteType
    (Γ.ι ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  infer_instance

/-! ## (D) Main theorem -/

/-- The normalization projection of an integral curve in a smooth projective variety over a perfect
field is a finite morphism. -/
theorem integralCurveNormalizationMap_isFinite {k : Type u} [Field k] [PerfectField k]
    {X : SmoothProjectiveVariety k} (Γ : IntegralCurve k X.toScheme) :
    AlgebraicGeometry.IsFinite
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField) := by
  have := Γ.locallyOfFiniteType_over
  apply curveFieldNormalizationMap_isFinite_of_forall_module_finite
  intro U _
  let φ : k →+* Γ(Γ.carrier, U.1) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ U.1 le_top).hom
  have hφ : φ.FiniteType := finiteType_sections_of_locallyOfFiniteType (k := k) Γ.carrier U.1 U.2
  let _ : Algebra k Γ(Γ.carrier, U.1) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(Γ.carrier, U.1) := hφ
  have : IsFractionRing Γ(Γ.carrier, U.1) Γ.carrier.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen Γ.carrier U.1 U.2
  exact Ring.module_finite_integralClosure_of_finiteType_of_perfectField k
    Γ(Γ.carrier, U.1) Γ.carrier.functionField

end
