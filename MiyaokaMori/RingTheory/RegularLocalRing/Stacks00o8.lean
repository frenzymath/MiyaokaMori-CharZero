import MiyaokaMori.Prelude
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-! # Stacks 00O8: localization does not increase projective or global dimension

Stacks 00O8: `pd_R M ≤ n ⇒ pd_{S^{-1}R} S^{-1}M ≤ n`; if `R` has global dimension `≤ n` then so does `S^{-1}R`
(the statement asserts the latter).

Reference: Stacks 00O8 (algebra-lemma-localize-finite-gl-dim).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem Localization.forall_hasProjectiveDimensionLE_of_forall {R : Type u} [CommRing R]
    (S : Submonoid R) (n : ℕ) (h : ∀ M : ModuleCat.{u} R, CategoryTheory.HasProjectiveDimensionLE M n) :
    ∀ N : ModuleCat.{u} (Localization S), CategoryTheory.HasProjectiveDimensionLE N n := by
  letI : Small.{u} R := small_of_surjective Function.surjective_id
  letI : Small.{u} (Localization S) :=
    small_of_surjective (Localization.mkHom_surjective (S := S))
  intro N
  letI : Module R (N : Type u) := Module.compHom (N : Type u) (algebraMap R (Localization S))
  letI : IsScalarTower R (Localization S) (N : Type u) :=
    IsScalarTower.of_compHom R (Localization S) (N : Type u)
  let M : ModuleCat.{u} R := ModuleCat.of R N
  letI : CategoryTheory.HasProjectiveDimensionLE M n := h M
  have hloc : CategoryTheory.HasProjectiveDimensionLE (M.localizedModule S) n :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE n S M
  let g : (M : Type u) →ₗ[R] (N : Type u) := LinearMap.id
  letI : IsLocalizedModule S g := by
    simpa [g, M] using (isLocalizedModule_id S (N : Type u) (Localization S))
  let e0 : (M : Type u) ≃ₗ[R] (N : Type u) := LinearEquiv.refl R (N : Type u)
  let e : (M.localizedModule S : Type u) ≃ₗ[Localization S] (N : Type u) :=
    IsLocalizedModule.mapEquiv S (M.localizedModuleMkLinearMap S) g (Localization S) e0
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv e n

end
