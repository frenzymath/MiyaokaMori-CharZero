import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame

/-! # Frames as bases, and `A(U) ≃ₐ Γ(π⁻¹U, O)`

Glue for `totalSpace_exists_coordinate_of_isFrame` (module `…MonomialRingEquivCoordinate`).
Everything here is at the variable level.

* `IsFrame.basisUnit`: a frame `e` of `M` on `W` is a basis (indexed by `Unit`) of the `Γ(X, W)`-module
  `Γ(M, W)`; `basisUnit_apply : basisUnit () = e`.
* `relativeSpec.sectionsAlgEquiv`: for a quasi-coherent algebra `A` and an affine open `U`, the ring
  isomorphism `sectionsIso A U : A(U) ≅ Γ(Spec_X A, π⁻¹U)` is an isomorphism of `Γ(X, U)`-algebras
  (structure maps `sectionsUnit U` and `π^♯ = π.app U`; `sectionsUnit_comp_sectionsToFunctions`).
  `sectionsAlgEquiv_apply_eq_structureHom_app`: it is the structure map `structureHom A` on sections
  (`structureHom_app_affine`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A frame `e` of `M` on `W`, as a basis of the free rank-one `Γ(X, W)`-module `Γ(M, W)`
(the singleton basis of `Γ(X, W)` transported along `r ↦ r • e`, the inverse of `coordEquiv`). -/
def IsFrame.basisUnit {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    Module.Basis Unit Γ(X, W) Γ(M, W) :=
  (Module.Basis.singleton Unit Γ(X, W)).map (hf.coordEquiv le_rfl).symm

theorem IsFrame.basisUnit_apply {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    hf.basisUnit () = e := by
  unfold IsFrame.basisUnit
  rw [Module.Basis.map_apply, Module.Basis.singleton_apply, LinearEquiv.symm_apply_eq]
  have h := hf.coord_frame le_rfl
  rw [res_self] at h
  exact h.symm

end AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The ring isomorphism `sectionsIso A U : A(U) ≅ Γ(Spec_X A, π⁻¹U)` (affine `U`) as an isomorphism of
`Γ(X, U)`-algebras, the structure maps being `sectionsUnit U` on the left and `π.app U` on the right
(`sectionsUnit_comp_sectionsToFunctions`). -/
def AlgebraicGeometry.Scheme.relativeSpec.sectionsAlgEquiv (A : X.QCAlgebra) (U : X.affineOpens) :
    letI := (A.sectionsUnit U.1).toAlgebra
    letI : Algebra Γ(X, U.1)
        Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1) :=
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom.app U.1).hom.toAlgebra
    A.sectionsRing U.1 ≃ₐ[Γ(X, U.1)]
      Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1) :=
  letI := (A.sectionsUnit U.1).toAlgebra
  letI : Algebra Γ(X, U.1)
      Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1) :=
    ((AlgebraicGeometry.Scheme.relativeSpec A).hom.app U.1).hom.toAlgebra
  AlgEquiv.ofRingEquiv
    (f := ((AlgebraicGeometry.Scheme.relativeSpec.sectionsIso A U).commRingCatIsoToRingEquiv :
      A.sectionsRing U.1 ≃+*
        Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1)))
    (fun r => congrArg (fun φ : CommRingCat.of Γ(X, U.1) ⟶ _ => φ.hom r)
      (AlgebraicGeometry.Scheme.relativeSpec.sectionsUnit_comp_sectionsToFunctions A U))

/-- `sectionsAlgEquiv` is the structure map `structureHom A : A → π_*O` on sections over `U`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.sectionsAlgEquiv_apply_eq_structureHom_app
    (A : X.QCAlgebra) (U : X.affineOpens) (c : A.sectionsRing U.1) :
    letI := (A.sectionsUnit U.1).toAlgebra
    letI : Algebra Γ(X, U.1)
        Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1) :=
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom.app U.1).hom.toAlgebra
    AlgebraicGeometry.Scheme.relativeSpec.sectionsAlgEquiv A U c =
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U.1 c := by
  refine Eq.trans ?_ (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_affine A U c).symm
  rfl

end
