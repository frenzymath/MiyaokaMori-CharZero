import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AffineAlgebraPullback

/-! # Geometric half of Stacks 01S5: `Spec_T (p_*O_W) ≅ W` over `T`

For an affine morphism `p : W ⟶ T`, the relative Spec of the direct-image algebra
`AffineAlgebra.ofAffineHom p` (`U ↦ Γ(W, p⁻¹U)` on the small affine Zariski site of `T`)
is isomorphic to `W` over `T`.

Source: Stacks 01S5 (morphisms-lemma-affine-equivalence-algebras), 01SA.
The construction of the comparison morphism `ofAffineHom.toSourceHom : Spec_T(p_*O_W) ⟶ W`
(gluing `IsAffineOpen.fromSpec` over the charts), the proof that it lies over `T`
(`toSourceHom_comp`) and that it is an isomorphism (`toSourceHom_isIso`: Zariski-local on the
target, and over `p⁻¹U` it is `isoSpec.inv` by pasting `chart_isPullback` with
`isPullback_morphismRestrict`) live upstream in `AffineAlgebraPullback.lean`
(`ofAffineHom_relativeSpec_iso`). This file packages the data form `ofAffineHom.relativeSpecIso`.

Also: a morphism `φ : A ⟶ B` of affine algebras whose components are isomorphisms induces an
isomorphism `Spec_X B ≅ Spec_X A` over `X` (`relativeSpec.map` is `colimMap` of a natural iso).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.AffineAlgebra

variable {T W : Scheme.{u}} (p : W ⟶ T) [IsAffineHom p]

/-- **Stacks 01S5, geometric half**: `Spec_T (p_*O_W) ≅ W` over `T` for an affine `p : W ⟶ T`. -/
def ofAffineHom.relativeSpecIso : (ofAffineHom p).relativeSpec ≅ Over.mk p :=
  have := ofAffineHom.toSourceHom_isIso p
  Over.isoMk (asIso (ofAffineHom.toSourceHom p)) (ofAffineHom.toSourceHom_comp p)

theorem ofAffineHom_relativeSpec_iso' : Nonempty ((ofAffineHom p).relativeSpec ≅ Over.mk p) :=
  ofAffineHom_relativeSpec_iso p

/-! ## `relativeSpec.map` of a componentwise isomorphism -/

variable {X : Scheme.{u}}

instance specNatTrans_isIso {A B : X.AffineAlgebra} (φ : Hom A B) [IsIso φ.app] :
    IsIso (specNatTrans φ) := by
  have : ∀ U, IsIso ((specNatTrans φ).app U) := fun U => by
    rw [specNatTrans_app]; infer_instance
  exact NatIso.isIso_of_isIso_app _

instance relativeSpec.map_isIso {A B : X.AffineAlgebra} (φ : Hom A B) [IsIso φ.app] :
    IsIso (relativeSpec.map φ) := by
  have h : relativeSpec.map φ = (HasColimit.isoOfNatIso (asIso (specNatTrans φ))).hom := by
    refine colimit.hom_ext fun U => ?_
    rw [HasColimit.isoOfNatIso_ι_hom]
    exact ι_colimMap _ _
  rw [h]
  infer_instance

/-- A morphism of affine algebras that is an isomorphism on the ring presheaves induces an
isomorphism of relative Specs over `X` (contravariant). -/
def relativeSpec.mapIso {A B : X.AffineAlgebra} (φ : Hom A B) [IsIso φ.app] :
    B.relativeSpec ≅ A.relativeSpec :=
  Over.isoMk (asIso (relativeSpec.map φ)) (relativeSpec.map_hom φ)

end AlgebraicGeometry.Scheme.AffineAlgebra

end
