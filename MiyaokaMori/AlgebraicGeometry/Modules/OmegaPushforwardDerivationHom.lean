import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.InverseImagePresheafSections

/-! # The pushforward of the universal derivation as a linear map

The universal derivation `d : O_T → Ω_{T/B}` of `p : T ⟶ B`, pushed forward to `B`, is an
`O_B`-linear map `p_* O_T ⟶ p_* Ω_{T/B}` (`Omega.pushforwardDerivationHom`): on an open `U ⊆ B`
it is `d_{p⁻¹U} : Γ(T, p⁻¹U) → Γ(Ω_{T/B}, p⁻¹U)`. It is additive and compatible with restriction
because `d` is, and `O_B(U)`-linear because `d` kills the image of `p^♯`
(`d(p^♯ r · a) = p^♯ r · d a + a · d(p^♯ r)` and `d(p^♯ r) = 0`, `Omega.derivation_appLE`).

Reference: Stacks 01UR/01UV (the universal derivation is `f⁻¹O_S`-linear; here used through
`Omega.universalDerivation`, `Omega.derivation_appLE`). Composing with the degree-one inclusion
`V^∨ ⟶ p_* O_{Tot(V)}` (`totalSpace.linearFunctionHom`) gives `V^∨ ⟶ p_* Ω_{Tot(V)/B}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {T B : Scheme.{u}} (p : T ⟶ B)

/-- `d(p^♯ r) = 0` for `r ∈ Γ(B, U)`, `p^♯ r ∈ Γ(T, p⁻¹U)`. -/
theorem Omega.universalDerivation_app (U : B.Opens) (r : Γ(B, U)) :
    (Omega.universalDerivation p).d (X := op (p ⁻¹ᵁ U)) ((p.app U).hom r) = 0 := by
  rw [Scheme.Hom.app_eq_appLE]
  exact Omega.derivation_appLE p (Omega.universalDerivation p) U (p ⁻¹ᵁ U) le_rfl r

/-- `p_*(d) : p_* O_T ⟶ p_* Ω_{T/B}`, the `O_B`-linear map given on `U ⊆ B` by the universal
derivation `d_{p⁻¹U} : Γ(T, p⁻¹U) → Γ(Ω_{T/B}, p⁻¹U)`. -/
def Omega.pushforwardDerivationHom :
    (Scheme.Modules.pushforward p).obj (SheafOfModules.unit T.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward p).obj (Omega p) :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom ((Omega.universalDerivation p).d (X := op (p ⁻¹ᵁ U.unop)))
      naturality := fun {U V} i => by
        ext a
        exact (Omega.universalDerivation p).d_map ((Opens.map p.base).map i.unop).op a }
    (fun U r a => by
      have h := (Omega.universalDerivation p).d_mul (X := op (p ⁻¹ᵁ U.unop)) ((p.app U.unop).hom r) a
      erw [Omega.universalDerivation_app p U.unop r, smul_zero, add_zero] at h
      exact h)⟩

theorem Omega.pushforwardDerivationHom_app (U : B.Opens) (a : Γ(T, p ⁻¹ᵁ U)) :
    (Omega.pushforwardDerivationHom p).app U a =
      (Omega.universalDerivation p).d (X := op (p ⁻¹ᵁ U)) a := rfl

end AlgebraicGeometry

end
