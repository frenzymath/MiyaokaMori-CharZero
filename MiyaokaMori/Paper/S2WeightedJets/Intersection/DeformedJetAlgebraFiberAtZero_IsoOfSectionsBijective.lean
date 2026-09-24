import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.IsIsoOfAffineOpensCoverBijective
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullbackId

/-! # A morphism of graded QC algebras bijective on sections over an affine cover is an isomorphism

Used for `reesDeformation_restrictToLambda_zero_iso_weightedSym` (`DeformedJetAlgebraFiberAtZero`): the comparison
`Φ : weightedSymAlgebra V ⟶ s₀^*R` is an isomorphism as soon as each piece `Φ.app m` is bijective on the sections over
the charts `U_i` of an affine cover. Componentwise this is the module-level criterion
`Modules.isIso_of_affineOpens_cover_bijective` (Stacks 01AI and 01I6: an isomorphism of sheaves is checked on stalks;
over an affine open a quasi-coherent module is determined by its global sections), applied to the quasi-coherent
pieces `S.part m`, `T.part m`; a componentwise isomorphism of graded QC algebras is an isomorphism
(`GradedQCAlgebra.isIso_of_isIso_app`).

Source: Stacks 01AI, 01I6.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

/-- **A morphism of graded QC algebras that is bijective on the sections over an affine cover is an isomorphism.**
`Us : ι → X.Opens` is a family of affine opens covering `X`; if every piece `Φ.app m` is bijective on `Γ(Us i, -)` for all `i`,
then `Φ` is an isomorphism (componentwise `Modules.isIso_of_affineOpens_cover_bijective`, then `isIso_of_isIso_app`).
Edge cases: `X = ∅` (`ι` may be empty; then `hcov` is vacuous and every morphism of quasi-coherent modules on `∅` is an
isomorphism, as the criterion checks stalks); `Φ` between zero algebras. -/
theorem isIso_of_affineOpens_cover_bijective {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (Φ : S ⟶ T)
    {ι : Type*} (Us : ι → X.Opens) (haff : ∀ i, AlgebraicGeometry.IsAffineOpen (Us i)) (hcov : ∀ x : X, ∃ i, x ∈ Us i)
    (h : ∀ (m : ℕ) (i : ι), Function.Bijective ((Φ.app m).app (Us i)).hom) : IsIso Φ := by
  have : ∀ m, IsIso (Φ.app m) := fun m =>
    haveI := S.quasicoherent m
    haveI := T.quasicoherent m
    AlgebraicGeometry.Scheme.Modules.isIso_of_affineOpens_cover_bijective (Φ.app m) Us haff hcov (h m)
  exact isIso_of_isIso_app Φ

/-- The same criterion with the cover given as a family of `X.affineOpens`. -/
theorem isIso_of_affineOpens_bijective {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (Φ : S ⟶ T)
    {ι : Type*} (U : ι → X.affineOpens) (hcov : ∀ x : X, ∃ i, x ∈ (U i).1)
    (h : ∀ (m : ℕ) (i : ι), Function.Bijective ((Φ.app m).app (U i).1).hom) : IsIso Φ :=
  isIso_of_affineOpens_cover_bijective Φ (fun i => (U i).1) (fun i => (U i).2) hcov h

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
