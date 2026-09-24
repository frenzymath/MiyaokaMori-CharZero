import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionGenericGermZero
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleStalkFree

/-! # Nonzero sections of a line bundle on an integral scheme are regular

A nonzero global section of a line bundle on an integral scheme has a regular germ at every point (a
nonzero section on a curve is a regular section).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- A nonzero global section of a line bundle on an integral scheme is regular (the same formulation as the
   hypothesis `hσ` of the effective Cartier divisor of a section). -/

open AlgebraicGeometry in

theorem isRegular_germ_of_ne_zero {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (L : X.Modules) [L.IsLineBundle]
    (σ : Γ(L, ⊤)) (hσ : σ ≠ 0) :
    ∀ U : X.Opens, Function.Injective (fun r : Γ(X, U) =>
        r • ((L.presheaf.map (CategoryTheory.homOfLE (le_top : U ≤ ⊤)).op).hom σ : Γ(L, U))) := by
  intro U
  by_cases hU : Nonempty U
  · let hη : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
    let s : Γ(L, U) :=
      (L.presheaf.map (CategoryTheory.homOfLE (le_top : U ≤ ⊤)).op).hom σ
    have hs : L.presheaf.germ U (genericPoint X) hη s ≠ 0 := by
      intro hs
      apply hσ
      apply lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero L σ
      simpa [s] using
        (TopCat.Presheaf.germ_res_apply L.presheaf
          (CategoryTheory.homOfLE (le_top : U ≤ ⊤)) (genericPoint X) hη σ).symm.trans hs
    let := AlgebraicGeometry.Scheme.Modules.free_stalk_of_isLineBundle L (genericPoint X)
    intro r₁ r₂ h
    apply AlgebraicGeometry.germ_injective_of_isIntegral (X := X) (genericPoint X) hη
    apply smul_left_injective (X.presheaf.stalk (genericPoint X)) hs
    have h' := congrArg (fun m => L.presheaf.germ U (genericPoint X) hη m) h
    erw [PresheafOfModules.germ_smul (R := X.presheaf) L.val,
      PresheafOfModules.germ_smul (R := X.presheaf) L.val] at h'
    exact h'
  · intro r₁ r₂ _
    apply TopCat.Presheaf.section_ext X.sheaf U r₁ r₂
    intro x hx
    exact (hU ⟨⟨x, hx⟩⟩).elim

end
