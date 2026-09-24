import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechBaseChangeLeaves
import MiyaokaMori.RingTheory.Localization.BaseChangeTransitivePushout
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffinePreimageSectionsPushout
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange

/-! # Pullback of sections along an affine base change

Let `X' = X ×_{Spec A} Spec A'`, `g' : X' → X`, `V ⊆ X` an affine open, and `M` quasi-coherent.
Then the pullback of sections `Γ(M, V) → Γ(g'^*M, g'⁻¹V)` is the base change along `A → A'`:
the adjoint transpose `A' ⊗_A Γ(M, V) → Γ(g'^*M, g'⁻¹V)` is an isomorphism.

Proof (second paragraph of the proof of Stacks 02KH / proof of Hartshorne III.9.3), in three steps:
(i) the square of rings `A → A'`, `A → Γ(X, V)`, `A' → Γ(X', g'⁻¹V)`, `Γ(X, V) → Γ(X', g'⁻¹V)`
is a pushout (affine fibre product, `isPushout_sections_of_affine`);
(ii) Stacks 01I9: for affine `V`, `V'` the pullback of sections is the base change along
`Γ(X, V) → Γ(X', V')` (`isIso_transpose_pullbackSectionsNative`);
(iii) transitivity of base change along a pushout square (`isIso_transpose_of_isPushout`, pure
algebra).

References: Stacks 02KH, 01I9, 01JQ; Hartshorne III.9.3 (p. 255), II.5.2(e).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **Geometric core (assembled from (i), (ii), (iii))**: the pullback of sections
`Γ(M, V) → Γ(g'^*M, g'⁻¹V)` is the base change along `A → A'`. -/
theorem isIso_transpose_pullbackSectionsLinear_of_affine {A A' : CommRingCat.{u}}
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) (φ : A ⟶ A')
    (M : X.Modules) [M.IsQuasicoherent] (V : X.Opens) (hV : AlgebraicGeometry.IsAffineOpen V)
    (V' : (Limits.pullback f (AlgebraicGeometry.Spec.map φ)).Opens)
    (h : V' ≤ (Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ V)
    (hV' : V' = (Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ V) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
      (pullbackSectionsLinear (Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ))
        ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso A').inv ≫
          (Limits.pullback.snd f (AlgebraicGeometry.Spec.map φ)).appTop).hom
        φ.hom (appTop_comp_structure_eq f φ) M V V' h)) := by
  have haff' : AlgebraicGeometry.IsAffineOpen V' := by
    have := isAffineHom_pullback_fst_spec f φ
    rw [hV']
    exact hV.preimage _
  exact isIso_transpose_of_isPushout φ _ _ _ (isPushout_sections_of_affine f φ V hV V' h hV')
    (AddEquiv.refl _) (fun _ _ => rfl) (AddEquiv.refl _) (fun _ _ => rfl) _
    (pullbackSectionsNative (Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) M V V' h)
    (fun _ => rfl)
    (isIso_transpose_pullbackSectionsNative _ M V hV V' haff' h)

end AlgebraicGeometry.Scheme.Modules

end
