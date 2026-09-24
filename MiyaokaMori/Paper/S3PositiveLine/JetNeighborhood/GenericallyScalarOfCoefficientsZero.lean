import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansion
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConeMorphismScaleOfCoordinates
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalar
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.GenericallyScalarOfCoefficientsZeroThickeningRestrict
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningCoefficientNaturality
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates

/-! # A jet whose positive-order coefficients vanish is generically scalar

If every cone coordinate of a based jet has vanishing `ξ`-coefficients in all positive orders `1, …, κ`, the jet
is generically scalar (§3 of the paper, scalar jets; Lemma 4.1).

Proof.
1. Apply `BasedJet.coneCoordinate_finite_xi_expansion` to every cone coordinate; by hypothesis all positive-order
   terms vanish and only the pullback of the seed coordinate remains.
2. In the definition of `BasedJet.IsGenericallyScalar` take the whole open set `⊤` and the unit `1`, whose
   restriction along the zero section is `1`.
3. The coordinatewise equalities of step 1 are the hypothesis of `BasedJet.restrict_eq_scale_of_coneCoordinate`,
   so the jet equals the seed jet times the unit `1` on that open set.

Implementation notes. The bridge `restrictToThickening_eq_thickeningRestrict` is a definitional equality. All
other facts about `restrictToThickening` in this module are derived from that bridge and the variable-level
lemmas about `thickeningRestrict`, so that the kernel only ever compares syntactically identical terms.

The body of `restrictToThickening` (`ThickeningSectionsTruncated.lean`) is literally
`AlgebraicGeometry.Scheme.Modules.restrictSectionAlong i p (g' := p_κ) M.toModules
(congrArg _ (toTotalSpace_proj L κ)) P` (`restrictSectionAlong`: `ThickeningCoefficientNaturality.lean`),
and `restrictSectionAlong` has the same body as `thickeningRestrict`
(`GenericallyScalarOfCoefficientsZeroThickeningRestrict.lean`). The proof is therefore two shallow steps:
1. `restrictToThickening L M κ P = restrictSectionAlong … := rfl`: one delta of the regular constant
   `restrictToThickening` onto the `restrictSectionAlong` head; the kernel then compares arguments
   without unfolding `restrictSectionAlong`;
2. `restrictSectionAlong_eq_thickeningRestrict` (below), the identification at *variable* level, where
   each side unfolds once to the same composite and no K-like reduction of `eqToHom` against concrete
   data is ever attempted.

A direct `rfl` against a body headed by `DFunLike.coe` does not check in the kernel in reasonable time: the
kernel unfolds the abbreviation, gets stuck on projections of a non-constructor instance, reduces to
`eqToHom (proof of i ≫ p = p_κ)` with a concrete proof, and the K-like check
`(pullback p_κ).obj M ≟ (pullback (i ≫ p)).obj M` on `jetNeighborhood.toTotalSpace` never finishes. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `restrictSectionAlong h g M (congrArg (fun q => (pullback q).obj M) e) P = thickeningRestrict h g e M P`:
`restrictSectionAlong` (`ThickeningCoefficientNaturality.lean`) and `thickeningRestrict`
(`GenericallyScalarOfCoefficientsZeroThickeningRestrict.lean`) have *identical bodies*
(`((((pullbackComp _ _).app M).hom ≫ eqToHom …).val.app ⊤).hom (sectionPullbackAlong _ _)`), so this is
`rfl` at variable level: each side unfolds once to the same composite (`h, g, e, M, P` are variables, so
no kernel blow-up). Bridge used by `restrictToThickening_eq_thickeningRestrict`. -/
theorem restrictSectionAlong_eq_thickeningRestrict {T' T X : AlgebraicGeometry.Scheme.{u}}
    (h : T' ⟶ T) (g : T ⟶ X) {g' : T' ⟶ X} (e : h ≫ g = g') (M : X.Modules)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.restrictSectionAlong h g M
        (congrArg (fun q => (AlgebraicGeometry.Scheme.Modules.pullback q).obj M) e) P
      = thickeningRestrict h g e M P := rfl

/-- **Bridge**: `restrictToThickening L M κ P` is, by definition, the instance
`thickeningRestrict (jetNeighborhood.toTotalSpace L κ).left (totalSpace L.toModules).hom
  (jetNeighborhood.toTotalSpace_proj L κ) M.toModules P` of the variable-level map
(`GenericallyScalarOfCoefficientsZeroThickeningRestrict.lean`): the two bodies are the same term up
to the proof inside `eqToHom`.

**Natural-language proof**: unfold both sides once; the bodies coincide (`rfl`).

**Formal route**: step 1 (`h1 := rfl`) is a one-step delta of `restrictToThickening` onto
`restrictSectionAlong`, whose arguments are spelled exactly as in the stored body so that the kernel compares
syntactically identical terms; step 2 is the variable-level identification
`restrictSectionAlong_eq_thickeningRestrict`, instantiated. If the body of `restrictToThickening`
(`ThickeningSectionsTruncated.lean`) is ever changed, re-check this proof first: it is the only place that
depends on the exact shape of that body.
Mathematically (§3–§4 of the paper), restriction from `Tot(L)` to the thickening `C̃_(κ)(L)` is pullback along
the closed immersion `i` followed by `i ≫ p_L = p_κ`. -/
theorem restrictToThickening_eq_thickeningRestrict {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    restrictToThickening L M κ P
      = thickeningRestrict (jetNeighborhood.toTotalSpace L κ).left
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
          (jetNeighborhood.toTotalSpace_proj L κ) M.toModules P := by
  -- Two shallow reductions: `restrictToThickening ⟶(1 delta) restrictSectionAlong …` (`h1`: heads differ, the
  -- kernel unfolds `restrictToThickening` once onto the `restrictSectionAlong` head and compares arguments,
  -- without unfolding `restrictSectionAlong`), then `restrictSectionAlong_eq_thickeningRestrict` (variable-level).
  have h1 : restrictToThickening L M κ P
      = AlgebraicGeometry.Scheme.Modules.restrictSectionAlong (jetNeighborhood.toTotalSpace L κ).left
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (g' := jetNeighborhood.proj L κ)
          M.toModules
          (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj M.toModules)
            (jetNeighborhood.toTotalSpace_proj L κ)) P := rfl
  rw [h1]
  exact restrictSectionAlong_eq_thickeningRestrict (jetNeighborhood.toTotalSpace L κ).left
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (jetNeighborhood.toTotalSpace_proj L κ)
    M.toModules P

/-- `restrictToThickening` is linear: it sends `0` to `0`. -/
theorem restrictToThickening_zero {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (κ : ℕ) :
    restrictToThickening L M κ 0 = 0 :=
  (restrictToThickening_eq_thickeningRestrict L M κ 0).trans (thickeningRestrict_zero _ _ _ _)

/-- Restricting the pullback `p_L^* t` of a section `t ∈ Γ(C̃, M)` from `Tot(L)` to the thickening
`C̃_(κ)(L)` is the pullback `p_κ^* t` (`i ≫ p_L = p_κ`, `jetNeighborhood.toTotalSpace_proj`). -/
theorem restrictToThickening_sectionPullbackAlong {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (t : (M.toModules.val.obj (Opposite.op ⊤) : Type u)) :
    restrictToThickening L M κ
        (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom t)
      = sectionPullbackAlong (jetNeighborhood.proj L κ) t :=
  (restrictToThickening_eq_thickeningRestrict L M κ _).trans
    (thickeningRestrict_sectionPullbackAlong _ _ (jetNeighborhood.toTotalSpace_proj L κ) _ t)

/-- The monomial map is linear: the monomial with coefficient (the image of) `0` is `0`
(variable-level form of `xiMonomial_zero_gsz`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.monomial_hom_zero {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] (q : ℕ) {N : X.Modules}
    (e : N ⟶ AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q) :
    AlgebraicGeometry.Scheme.totalSpace.monomial L M q ((e.val.app (Opposite.op ⊤)).hom 0) = 0 := by
  unfold AlgebraicGeometry.Scheme.totalSpace.monomial
    AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback
  rw [map_zero, map_zero, map_zero]
  exact map_zero _

/-- `c ↦ c·ξ^q` is linear: the monomial with coefficient `0` is `0`. -/
theorem xiMonomial_zero_gsz {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (q : ℕ) :
    xiMonomial L M q 0 = 0 := by
  unfold xiMonomial
  exact AlgebraicGeometry.Scheme.totalSpace.monomial_hom_zero _ _ _ _

/-- If all positive-order coefficients of the `ℓ`-th cone coordinate vanish, the cone coordinate is
the pullback `p_κ^* ρ^* f_ℓ` of the seed coordinate (equation (4.1) of the paper: the expansion
`P_ℓ^{(κ)} = ρ^* f_ℓ + Σ_{q≥1} c_{ℓ,q} ξ^q` with all `c_{ℓ,q} = 0`). -/
theorem BasedJet.coneCoordinate_eq_seedCoordPullback_of_coefficients_eq_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1))
    (hzero : ∀ q : Fin κ, BasedJet.coefficient J ℓ ((q : ℕ) + 1) = 0) :
    BasedJet.coneCoordinate J ℓ
      = sectionPullbackAlong (jetNeighborhood.proj L κ) (seedCoordPullback f ρ (D.coord ℓ)) := by
  have h₁ := BasedJet.coneCoordinate_finite_xi_expansion J ℓ
  have hsum : (∑ q : Fin κ,
      restrictToThickening L
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ
        (xiMonomial L
          (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1)))
          ((q : ℕ) + 1) (BasedJet.coefficient J ℓ ((q : ℕ) + 1)))) = 0 :=
    Finset.sum_eq_zero (fun q _ => by rw [hzero q, xiMonomial_zero_gsz, restrictToThickening_zero])
  rw [hsum, add_zero] at h₁
  refine h₁.trans ((restrictToThickening_sectionPullbackAlong L
    (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ _).trans ?_)
  unfold seedCoordPullback
  exact congrArg (sectionPullbackAlong (jetNeighborhood.proj L κ))
    (sectionPullbackAlong_naturality ρ.hom
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1).symm)) (D.coord ℓ))

theorem BasedJet.isGenericallyScalar_of_coefficients_eq_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hzero : ∀ (ℓ : Fin (X.embDim + 1)) (q : Fin κ),
      BasedJet.coefficient J ℓ ((q : ℕ) + 1) = 0) :
    J.IsGenericallyScalar := by
  refine ⟨⊤, ?_, 1, ?_, ?_⟩
  · have : Nonempty ρ.source.toScheme := ρ.source.connected.toNonempty
    rw [TopologicalSpace.Opens.coe_top]
    exact Set.univ_nonempty
  · rw [Units.val_one]
    exact map_one _
  · refine BasedJet.restrict_eq_scale_of_coneCoordinate J ⊤ 1 (fun ℓ => ?_)
    have h := congrArg
      (sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ (⊤ : ρ.source.toScheme.Opens)).ι)
      (BasedJet.coneCoordinate_eq_seedCoordPullback_of_coefficients_eq_zero J ℓ (hzero ℓ))
    simp only [Units.val_one]
    exact h.trans (one_smul _ _).symm

end
