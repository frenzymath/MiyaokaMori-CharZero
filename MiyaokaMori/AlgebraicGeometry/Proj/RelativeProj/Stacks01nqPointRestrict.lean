import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq

/-! # Points of the charts of a relative Proj under shrinking the affine open

**Points of the charts of the relative Proj under shrinking the affine open** (Stacks 01NQ, second half, on
points). For affine opens `U ≤ U'` of `X` and `y ∈ π⁻¹U ⊆ π⁻¹U'`, the chart images
`φ_U(y) ∈ Proj A(U)` and `φ_{U'}(y) ∈ Proj A(U')` (`relativeProj.affineIso`) are related by the morphism
`Proj.map ρ : Proj A(U) → Proj A(U')` induced by the graded restriction `ρ = sectionsRestrict : A(U') → A(U)`:
`φ_{U'}(y) = (Proj.map ρ) (φ_U(y))`. Since `Proj.map ρ` sends a homogeneous prime `𝔮` to `ρ⁻¹𝔮`
(Mathlib `ProjectiveSpectrum.comap`), the homogeneous prime of `φ_{U'}(y)` is the preimage under `ρ` of that of
`φ_U(y)`; in particular `g ∉ 𝔭_{φ_{U'}(y)}` implies `ρ g ∉ 𝔭_{φ_U(y)}`.

This is the "shrink" step in the computation of the coordinate subspaces in the proof of Proposition 2.4 of the paper, stated for an arbitrary graded quasi-coherent algebra.

Proof: `affineIso_restrict` (`Stacks01nq.lean`): `e_U⁻¹ ≫ (π⁻¹U ⊆ π⁻¹U') ≫ e_{U'} = Proj.map ρ`;
evaluate both sides at the point `e_U(y)`; `e_U⁻¹(e_U(y)) = y`, and the open inclusion is the identity on points
(`Scheme.homOfLE_apply'`). The underlying map of `Proj.map` is `ProjectiveSpectrum.comap` by definition
(`Proj.map`, `Proj.sheafedSpaceMap`), whose homogeneous ideal is `HomogeneousIdeal.comap`, and membership in
`J.comap ρ` is membership of `ρ g` in `J` (`toIdeal_comap`, `Ideal.mem_comap`).

Edge cases: `U = U'` (then `ρ = id`, trivially fine); `U = ⊥` has no `y`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `φ_{U'}(y) = (Proj.map ρ)(φ_U(y))` for affine `U ≤ U'` and `y ∈ π⁻¹U` (Stacks 01NQ on points). -/
theorem AlgebraicGeometry.Scheme.relativeProj.affineIso_hom_apply_eq_map
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (U U' : X.affineOpens) (h : U.1 ≤ U'.1)
    (y : (AlgebraicGeometry.Scheme.relativeProj S).left)
    (hy : y ∈ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U').hom
        ⟨y, (AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono h hy⟩ =
      AlgebraicGeometry.Proj.map (S.sectionsRestrict h) (S.sectionsRestrict_irrelevant U.2 U'.2 h)
        ((AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom ⟨y, hy⟩) := by
  have e := AlgebraicGeometry.Scheme.relativeProj.affineIso_restrict S U U' h
  have e' := congrArg (fun f => f ((AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom ⟨y, hy⟩)) e
  simp only [AlgebraicGeometry.Scheme.Hom.comp_apply] at e'
  have h1 : (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).inv
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom ⟨y, hy⟩) = ⟨y, hy⟩ := by
    have h0 := congrArg (fun f => f ⟨y, hy⟩) (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom_inv_id
    simp only at h0
    exact h0
  rw [h1, AlgebraicGeometry.Scheme.homOfLE_apply'] at e'
  exact e'

/-- The point `Proj.map f hf z` is `ProjectiveSpectrum.comap f hf z` (by definition of `Proj.map`). -/
theorem AlgebraicGeometry.Proj.map_apply {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (z : AlgebraicGeometry.Proj ℬ) :
    AlgebraicGeometry.Proj.map f hf z = ProjectiveSpectrum.comap f hf z := rfl

/-- **Prime transport under shrinking**: `g ∈ A(U')` not in the homogeneous prime of `φ_{U'}(y)` implies
`ρ g ∈ A(U)` not in the homogeneous prime of `φ_U(y)` (`U ≤ U'` affine, `y ∈ π⁻¹U`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.sectionsRestrict_notMem_affineIso_of_notMem
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (U U' : X.affineOpens) (h : U.1 ≤ U'.1)
    (y : (AlgebraicGeometry.Scheme.relativeProj S).left)
    (hy : y ∈ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) (g : S.sectionsRing U'.1)
    (hg : g ∉ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S U').hom
      ⟨y, (AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono h hy⟩).asHomogeneousIdeal) :
    S.sectionsRestrict h g ∉
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom ⟨y, hy⟩).asHomogeneousIdeal := by
  intro hmem
  apply hg
  rw [AlgebraicGeometry.Scheme.relativeProj.affineIso_hom_apply_eq_map S U U' h y hy,
    AlgebraicGeometry.Proj.map_apply]
  exact hmem

end
