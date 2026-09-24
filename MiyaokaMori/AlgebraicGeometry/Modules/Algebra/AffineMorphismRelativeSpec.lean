import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfAffineHomRelativeSpecIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetSpecIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec

/-! # Affine morphisms are relative Specs (Stacks 01SA)

Affine morphisms and quasi-coherent algebras are anti-equivalent (Stacks 01SA): for `f : T → X` affine,
`f_*O_T` is a quasi-coherent `O_X`-algebra and `T ≅ Spec_X(f_*O_T)` as `X`-schemes.

References: Stacks 01S5 / 01SA.

Route:
1. The witness is `A := QCAlgebra.pushforwardStructureSheaf f`.
2. On every open `U`, the ring `A.sectionsRing U` is literally `Γ(T, f⁻¹U)`: the multiplication
   `QCAlgebra.presheafMul` of `A` is the presheaf multiplication `pushforwardStructureSheaf.presheafMul f`
   (unwind `mul f = (e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m) ≫ e` through the sheafification adjunction),
   whose value on `a ⊗ b` is `a * b`. These lemmas (`qcPresheafMul_eq`, `sectionsRing_mul`,
   `sectionsRing_one`) are in `JetSpecIso.lean`.
3. Hence `A.toAffineAlgebra ≅ AffineAlgebra.ofAffineHom f` as affine algebras on the small affine
   Zariski site (`toAffineAlgebraHom`, componentwise a ring isomorphism), so
   `Spec_X A ≅ Spec_X (ofAffineHom f)` over `X` (`AffineAlgebra.relativeSpec.mapIso`).
4. `Spec_X (ofAffineHom f) ≅ T` over `X` is the geometric half of Stacks 01S5
   (`AffineAlgebra.ofAffineHom.relativeSpecIso`, `OfAffineHomRelativeSpecIso.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf

variable {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) [AlgebraicGeometry.IsAffineHom f]

set_option backward.isDefEq.respectTransparency false in
/-- `A.sectionsRing U ≃+* Γ(T, f⁻¹U)` for `A = f_*O_T` (the identity on underlying sets). -/
def sectionsRingEquiv (U : X.Opens) :
    (pushforwardStructureSheaf f).sectionsRing U ≃+* Γ(T, f ⁻¹ᵁ U) where
  toFun a := (show Γ(T, f ⁻¹ᵁ U) from a)
  invFun b := (show (pushforwardStructureSheaf f).sectionsRing U from b)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := sectionsRing_mul f U a b
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The affine-algebra morphism `ofAffineHom f ⟶ (f_*O_T).toAffineAlgebra`, componentwise the
ring isomorphism `Γ(T, f⁻¹U) ≃+* A.sectionsRing U`. -/
def toAffineAlgebraHom :
    AffineAlgebra.Hom (AffineAlgebra.ofAffineHom f) (pushforwardStructureSheaf f).toAffineAlgebra where
  app :=
    { app := fun U => ((sectionsRingEquiv f U.unop.toOpens).symm.toCommRingCatIso).hom
      naturality := fun U V g => by
        ext a
        rfl }
  unit_app := by
    ext U r
    rfl

instance toAffineAlgebraHom_app_isIso : IsIso (toAffineAlgebraHom f).app := by
  have : ∀ U, IsIso ((toAffineAlgebraHom f).app.app U) := fun U => by
    change IsIso ((sectionsRingEquiv f U.unop.toOpens).symm.toCommRingCatIso).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf

/-- **Stacks 01S5 / 01SA**: an affine morphism `f : T ⟶ X` is the relative Spec of the quasi-coherent
`O_X`-algebra `f_*O_T`, as schemes over `X`. -/
theorem AlgebraicGeometry.Scheme.exists_relativeSpec_iso_of_isAffineHom {X T : AlgebraicGeometry.Scheme.{u}}
    (f : T ⟶ X) [AlgebraicGeometry.IsAffineHom f] :
    ∃ (A : X.QCAlgebra),
      Nonempty (AlgebraicGeometry.Scheme.relativeSpec A ≅ CategoryTheory.Over.mk f) :=
  ⟨AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf f,
    ⟨AlgebraicGeometry.Scheme.AffineAlgebra.relativeSpec.mapIso
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.toAffineAlgebraHom f) ≪≫
      AlgebraicGeometry.Scheme.AffineAlgebra.ofAffineHom.relativeSpecIso f⟩⟩

end
