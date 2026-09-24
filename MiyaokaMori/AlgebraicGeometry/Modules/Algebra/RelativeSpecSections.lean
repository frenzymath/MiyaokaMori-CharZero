import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AffineAlgebra

/-! # Functions on the relative Spec over an affine open

The function ring of the relative Spec over an affine open `U` **is** the section ring of the algebra
on `U`: `AffineAlgebra.sectionsPreimageEquiv : Γ(π⁻¹U, ⊤) ≃+* A(U)`, obtained by taking global sections
of the isomorphism of schemes `AffineAlgebra.preimageIsoSpec : (π⁻¹U).toScheme ≅ Spec A(U)`.

`A.relativeSpec` is glued over the affine site; the chart `A.chart U : Spec A(U) ⟶ Spec_X A` is an open
immersion with `π⁻¹U = range (chart U)` (`AffineAlgebra.preimage_eq_opensRange`), so this isomorphism is
part of the gluing data: `eqToIso` + `Scheme.Hom.isoOpensRange` + `ΓSpecIso`, with no proof obligation
and no grading involved.

Reference: Stacks 01LQ (the relative Spec over an affine open is the Spec of the section ring).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.AffineAlgebra

variable {X : Scheme.{u}} (A : X.AffineAlgebra)

/-- The part of the relative Spec over an affine open `U` is `Spec A(U)` (the chart is an open immersion
with image exactly `π⁻¹U`). -/
def preimageIsoSpec (U : X.AffineZariskiSite) :
    (A.relativeSpec.hom ⁻¹ᵁ U.toOpens).toScheme ≅ Spec (A.sections U) :=
  eqToIso (congrArg Scheme.Opens.toScheme (A.preimage_eq_opensRange U)) ≪≫
    (A.chart U).isoOpensRange.symm

/-- **`Γ(π⁻¹U, ⊤) ≃+* A(U)`**: the function ring of the relative Spec over an affine open is the section ring
of the algebra. -/
def sectionsPreimageEquiv (U : X.AffineZariskiSite) :
    Γ((A.relativeSpec.hom ⁻¹ᵁ U.toOpens).toScheme, ⊤) ≃+* A.sections U :=
  ((Scheme.Γ.mapIso (A.preimageIsoSpec U).op).symm ≪≫
    Scheme.ΓSpecIso (A.sections U)).commRingCatIsoToRingEquiv

end AlgebraicGeometry.Scheme.AffineAlgebra

end
