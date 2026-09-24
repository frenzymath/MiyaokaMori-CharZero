import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Base change of the Čech complex: the isomorphism of complexes

Notation as in `CechPullbackMap.lean`. If for every strictly increasing index tuple `σ` the pullback
of sections `Γ(M, U_σ) → Γ(g^*M, g⁻¹U_σ)` is a base change (i.e. its adjoint transpose
`A' ⊗_A Γ(M, U_σ) → Γ(g^*M, g⁻¹U_σ)` is an isomorphism), then there is an isomorphism of complexes of
`A'`-modules `A' ⊗_A Č(U, M) ≅ Č(g⁻¹U, g^*M)`.

Proof: take the chain map `cechPullbackMap`; its degreewise transpose is an isomorphism (both sides
vanish in negative degrees, and in nonnegative degrees they are finite products, so componentwise
isomorphisms suffice: `isIso_transpose_liftThrough`); conclude with `nonempty_iso_of_isIso_transpose`.

Source: the second paragraph of the proof of Stacks 02KH; the proof of Hartshorne III.9.3 (p. 255).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)
  {A A' : Type u} [CommRing A] [CommRing A'] (a : A →+* Γ(X, ⊤)) (a' : A' →+* Γ(Y, ⊤))
  (φ : A →+* A') {n : ℕ} (U : Fin n → X.Opens)

theorem cechBaseChange_complex_iso (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules)
    (hbc : ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin n),
      IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm
        (pullbackSectionsLinear g a a' φ hcomm M (⨅ k, U (σ k)) (⨅ k, g ⁻¹ᵁ U (σ k))
          (le_of_eq (preimage_iInf_eq g fun k => U (σ k)).symm)))) :
    Nonempty (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj
        (((ModuleCat.restrictScalars a).mapHomologicalComplex _).obj (cechComplexAlt U M)) ≅
      ((ModuleCat.restrictScalars a').mapHomologicalComplex _).obj
        (cechComplexAlt (fun i => g ⁻¹ᵁ U i)
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M))) := by
  haveI : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  refine AdjointComplexIso.nonempty_iso_of_isIso_transpose (ModuleCat.extendRestrictScalarsAdj φ)
    (cechPullbackMap g a a' φ U hcomm M) fun i => ?_
  cases i with
  | ofNat p =>
    exact AdjointComplexIso.isIso_transpose_liftThrough (ModuleCat.extendRestrictScalarsAdj φ)
      (ModuleCat.restrictScalars a')
      (fun σ : Fin (p + 1) ↪o Fin n =>
        (ModuleCat.restrictScalars a).obj (M.sectionsOverTop (⨅ k, U (σ k))))
      (fun σ : Fin (p + 1) ↪o Fin n =>
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).sectionsOverTop (⨅ k, g ⁻¹ᵁ U (σ k)))
      (fun σ => (ModuleCat.restrictScalars a).map
        (Pi.π (fun σ : Fin (p + 1) ↪o Fin n => M.sectionsOverTop (⨅ k, U (σ k))) σ))
      (isLimitFanMkObjOfIsLimit (ModuleCat.restrictScalars a) _ _ (productIsProduct _))
      (fun σ => pullbackSectionsLinear g a a' φ hcomm M (⨅ k, U (σ k)) (⨅ k, g ⁻¹ᵁ U (σ k))
        (le_of_eq (preimage_iInf_eq g fun k => U (σ k)).symm))
      (hbc p)
  | negSucc k =>
    have hX : IsZero ((ModuleCat.extendScalars.{u, u, u} φ).obj
        ((ModuleCat.restrictScalars a).obj (ModuleCat.of Γ(X, ⊤) PUnit))) :=
      Functor.map_isZero _ (Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _))
    have hY : IsZero ((ModuleCat.restrictScalars a').obj (ModuleCat.of Γ(Y, ⊤) PUnit)) :=
      Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _)
    exact ⟨⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩

end AlgebraicGeometry.Scheme.Modules

end
