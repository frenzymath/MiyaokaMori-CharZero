import MiyaokaMori.Prelude
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.FinitePresentation

/-! # Invertible modules from local freeness of rank one

A finitely presented module whose localization at every prime ideal is free of rank one is an
invertible module (finite locally free of rank one ⟺ invertible).

Reference: Stacks 00NX (finitely presented + locally free ⇒ finite locally free) and
Stacks 0B8I, (1) ⇒ (2).

Proof (fully formalized). `Module.Invertible A M` means the contraction
`ev : Dual A M ⊗[A] M → A` is bijective. Bijectivity is checked after localizing at every
maximal ideal `P` (`bijective_of_isLocalized_maximal`), where we are free to choose the model
of the localized modules: for the source we take `Dual Aₚ Mₚ ⊗[Aₚ] Mₚ`, which is a localization
of `Dual A M ⊗[A] M` because Hom out of a finitely presented module commutes with localization
(`Module.FinitePresentation.isLocalizedModule_mapExtendScalars`), tensor products of localizations
are localizations (`IsLocalization` instance for `TensorProduct.map`), and `⊗[A]` may be replaced by
`⊗[Aₚ]` (`IsLocalization.moduleTensorEquiv`). Under these identifications the localized `ev` is the
contraction of `Mₚ` over `Aₚ`, which is bijective since `Mₚ ≃ Aₚ` (hypothesis) and `Aₚ` is
invertible over itself. The zero ring (no maximal ideals) is covered vacuously.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-- A finitely presented module whose localization at every prime is free of rank one is an
invertible module (Stacks 00NX + 0B8I (1) ⇒ (2)). The contraction `Dual A M ⊗ M → A` is checked
to be bijective locally at each maximal ideal, where it becomes the contraction of `Mₚ ≃ Aₚ`. -/
theorem Module.Invertible.of_localization_free_rank_one {A M : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] [Module.FinitePresentation A M]
    (h : ∀ (p : Ideal A) [p.IsPrime],
      Nonempty (LocalizedModule p.primeCompl M ≃ₗ[Localization.AtPrime p] Localization.AtPrime p)) :
    Module.Invertible A M := by
  classical
  constructor
  -- the localization map on `Dual A M ⊗[A] M` towards `Dual Aₚ Mₚ ⊗[Aₚ] Mₚ`
  let loc : ∀ (P : Ideal A) [P.IsMaximal],
      Module.Dual A M ⊗[A] M →ₗ[A]
        Module.Dual (Localization.AtPrime P) (LocalizedModule P.primeCompl M)
          ⊗[Localization.AtPrime P] LocalizedModule P.primeCompl M :=
    fun P _ =>
      ((IsLocalization.moduleTensorEquiv P.primeCompl (Localization.AtPrime P)
          (Module.Dual (Localization.AtPrime P) (LocalizedModule P.primeCompl M))
          (LocalizedModule P.primeCompl M)).symm.restrictScalars A).toLinearMap ∘ₗ
        TensorProduct.map
          (IsLocalizedModule.mapExtendScalars P.primeCompl
            (LocalizedModule.mkLinearMap P.primeCompl M)
            (Algebra.linearMap A (Localization.AtPrime P)) (Localization.AtPrime P))
          (LocalizedModule.mkLinearMap P.primeCompl M)
  have hloc : ∀ (P : Ideal A) [P.IsMaximal], IsLocalizedModule P.primeCompl (loc P) :=
    fun P _ => inferInstance
  refine bijective_of_isLocalized_maximal _ loc _
    (fun P _ => Algebra.linearMap A (Localization.AtPrime P)) (contractLeft A M) ?_
  intro P _
  obtain ⟨e⟩ := h P
  have : Module.Invertible (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.Invertible.congr e.symm
  have key : IsLocalizedModule.map P.primeCompl (loc P) (Algebra.linearMap A (Localization.AtPrime P))
      (contractLeft A M) =
      (contractLeft (Localization.AtPrime P) (LocalizedModule P.primeCompl M)).restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext P.primeCompl (loc P)
      (Algebra.linearMap A (Localization.AtPrime P))
    rw [IsLocalizedModule.map_comp]
    apply TensorProduct.ext'
    intro φ m
    simp only [loc, IsLocalization.moduleTensorEquiv, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.map_tmul, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
      LinearMap.coe_restrictScalars, contractLeft_apply,
      Algebra.linearMap_apply]
    rw [show ∀ (x : Module.Dual (Localization.AtPrime P) (LocalizedModule P.primeCompl M))
        (y : LocalizedModule P.primeCompl M),
        (TensorProduct.equivOfCompatibleSMul A (Localization.AtPrime P) (Localization.AtPrime P)
          (Module.Dual (Localization.AtPrime P) (LocalizedModule P.primeCompl M))
          (LocalizedModule P.primeCompl M)).symm (x ⊗ₜ[A] y) = x ⊗ₜ[Localization.AtPrime P] y
        from fun _ _ => rfl]
    rw [contractLeft_apply, IsLocalizedModule.mapExtendScalars_apply_apply]
    exact (IsLocalizedModule.map_apply P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M)
      (Algebra.linearMap A (Localization.AtPrime P)) φ m).symm
  rw [key]
  exact Module.Invertible.bijective

end
