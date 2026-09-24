import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.Stacks01xkHPrimeExt
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.OpenImmersionFreeSheafExtendByZero

/-! # Cohomology of an open, computed on the open subscheme

**Cohomology of an open, computed on the open subscheme** (Stacks 01E1 / the TODO in Mathlib
`Sites/SheafCohomology/Basic.lean`): for a module `M` on a scheme `X` and an open `Y ⊆ X`,
`H'^q(Y, M) := Ext(ℤ[h_Y]^#, M, q)` (cohomology of the open `Y` with values in the abelian sheaf
underlying `M`, computed on `X`) is isomorphic to `H^q(Y, M|_Y) = sheafCohomology Y (M.restrict Y.ι) q`
(cohomology of the open subscheme with values in the restricted module), `Γ(X, ⊤)`-linearly, where
`Γ(X, ⊤)` acts on the right-hand side through the restriction `Γ(X, ⊤) → Γ(Y, ⊤)`.

**Proof (fully formalized; the "extension by zero" route of Stacks 01E1 / 03F3).** Write
`F := M.toAddCommGrpSheaf`, `G := Y.ι.opensFunctor : Y.Opens ⥤ X.Opens` (`V ↦ Y.ι ''ᵁ V`),
`j^* := G.sheafPushforwardContinuous` (restriction of abelian sheaves to `Y`; on `F` it is
*definitionally* `(M.restrict Y.ι).toAddCommGrpSheaf`) and `j_! := G.sheafPullback` (extension by
zero, the left adjoint of `j^*`; Mathlib's sheafified left Kan extension along `G.op`).
1. `j_!` is exact (`Scheme.Opens.preservesFiniteLimits_sheafPullback_opensFunctor`): pointwise, the Kan extension
   along `G.op` at `W` is `0` if `W ⊄ Y` and evaluation at `Y.ι ⁻¹ᵁ W` if `W ≤ Y`, both of which
   preserve finite limits, and sheafification is exact. `j^*` is exact (it also has a right adjoint
   `j_*`, `G` being cocontinuous).
2. `ℤ[h_Y]^# ≅ j_! ℤ_Y` (`Scheme.Opens.freeSheafIsoExtendConstant`): both corepresent `F ↦ F(Y)`
   (`Hom(ℤ[h_Y]^#, F) ≃ F(Y)` by evaluation at the canonical generator;
   `Hom(j_! ℤ_Y, F) ≃ Hom(ℤ_Y, j^* F) ≃ (j^* F)(⊤) = F(Y)`).
3. `Ext_X(ℤ[h_Y]^#, F, q) ≃+ Ext_X(j_! ℤ_Y, F, q) ≃+ Ext_Y(ℤ_Y, j^* F, q) = H^q(Y, M|_Y)`
   (`extAddEquivOfIsoLeft`; `Adjunction.extAddEquiv`, which needs step 1). Both equivalences are natural in the second variable, so for `r : Γ(X, ⊤)` the action
   `x ↦ x ∘ mk₀ (M.smulEnd r)` on the left corresponds to `y ↦ y ∘ mk₀ (j^*.map (M.smulEnd r))` on the
   right, and `j^*.map (M.smulEnd r) = (M.restrict Y.ι).smulEnd (Y.ι.appTop r)` (`restrict_smulEnd`:
   on `V ≤ Y`, both multiply by `r|_{Y.ι ''ᵁ V}`, Mathlib `appLE_appIso_inv`). This is exactly
   `Γ(X, ⊤)`-linearity for `Module.compHom` along `Y.ι.appTop` on the right
   (`Adjunction.extLinearEquivOfIsoLeft`).

Source: Stacks 01E1 (cohomology-lemma-cohomology-of-open), 03F3 (`j_! ⊣ j^{-1}`), Hartshorne II
Ex. 1.19 / III.2.4, Mathlib `Sites/SheafCohomology/Basic.lean` TODO. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian CategoryTheory.Abelian.Ext

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)

attribute [local instance] smulEndAction ExtAction.module

/-- Restricting a global function `r` to `Y` and then to `V ≤ Y` (transported to `Γ(X, Y.ι ''ᵁ V)`
by `appIso`) is restricting it to `Y.ι ''ᵁ V` (Mathlib `appLE_appIso_inv`). -/
theorem appIso_inv_map_appTop (Y : X.Opens) (V : (Y : AlgebraicGeometry.Scheme.{u}).Opens)
    (r : Γ(X, ⊤)) :
    (Y.ι.appIso V).inv.hom
        ((Y : AlgebraicGeometry.Scheme.{u}).presheaf.map (homOfLE le_top).op (Y.ι.appTop.hom r)) =
      X.presheaf.map (homOfLE le_top).op r := by
  have h := Y.ι.appLE_appIso_inv (U := ⊤) (V := V) le_top
  have h' := congrArg (fun φ => φ.hom r) h
  simp only [Scheme.Hom.appLE] at h'
  exact h'

/-- Restriction to the open `Y` of "multiplication by the global function `r`" is multiplication by
`r|_Y` on `M|_Y`. -/
theorem restrict_smulEnd (Y : X.Opens) (r : Γ(X, ⊤)) :
    (Y.restrictAb).map (M.smulEnd r) = (M.restrict Y.ι).smulEnd (Y.ι.appTop.hom r) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  ext m
  change (ModuleCat.smul (M.val.obj (op (Y.ι ''ᵁ V.unop)))
      (X.presheaf.map (homOfLE le_top).op r)).hom m =
    (ModuleCat.smul ((M.restrict Y.ι).val.obj V)
      ((Y : AlgebraicGeometry.Scheme.{u}).presheaf.map (homOfLE le_top).op (Y.ι.appTop.hom r))).hom m
  have e : ModuleCat.smul ((M.restrict Y.ι).val.obj V)
      ((Y : AlgebraicGeometry.Scheme.{u}).presheaf.map (homOfLE le_top).op (Y.ι.appTop.hom r)) =
    ModuleCat.smul (M.val.obj (op (Y.ι ''ᵁ V.unop)))
      ((Y.ι.appIso V.unop).inv.hom
        ((Y : AlgebraicGeometry.Scheme.{u}).presheaf.map (homOfLE le_top).op
          (Y.ι.appTop.hom r))) := rfl
  rw [e, appIso_inv_map_appTop]
  rfl

/-- **Cohomology of an open equals cohomology of the open subscheme** (Stacks 01E1):
`H'^q(Y, M) ≃ₗ[Γ(X,⊤)] H^q(Y, M|_Y)`, where `Γ(X, ⊤)` acts on the right through `Γ(X, ⊤) → Γ(Y, ⊤)`.
Proof: `Ext` along the exact adjunction `j_! ⊣ j^*` and `ℤ[h_Y]^# ≅ j_! ℤ_Y`, see the module
docstring. -/
theorem nonempty_E_linearEquiv_sheafCohomology_restrict (Y : X.Opens) (q : ℕ) :
    letI : Module Γ(X, ⊤) (AlgebraicGeometry.sheafCohomology Y (M.restrict Y.ι) q) :=
      Module.compHom _ Y.ι.appTop.hom
    Nonempty (E M Y q ≃ₗ[Γ(X, ⊤)] AlgebraicGeometry.sheafCohomology Y (M.restrict Y.ι) q) := by
  let m₂ : Module Γ(X, ⊤) (AlgebraicGeometry.sheafCohomology Y (M.restrict Y.ι) q) :=
    Module.compHom _ Y.ι.appTop.hom
  have := Y.preservesFiniteLimits_extendAb
  have := Y.preservesFiniteColimits_restrictAb
  exact ⟨(Y.extendRestrictAdjunction).extLinearEquivOfIsoLeft (A := (freeSheafFunctor X).obj Y)
    (B := Y.constantZ) (Y.freeSheafIsoExtendConstant) M.toAddCommGrpSheaf q
    (ExtAction.module Γ(X, ⊤) M.toAddCommGrpSheaf _ q) m₂
    M.smulEnd (fun r => (M.restrict Y.ι).smulEnd (Y.ι.appTop.hom r))
    (fun _ _ => rfl) (fun _ _ => rfl) (restrict_smulEnd M Y)⟩

/-- **Stacks 01E1, additive form**: `H'^q(U, M) ≃+ H^q(U, M|_U)`, the underlying additive
equivalence of `nonempty_E_linearEquiv_sheafCohomology_restrict` (`E M U q` is definitionally
`M.toAddCommGrpSheaf.H' q U`). -/
theorem hPrime_addEquiv_H_restrict (U : X.Opens) (q : ℕ) :
    Nonempty ((M.toAddCommGrpSheaf.H' q U : AddCommGrpCat.{u}) ≃+
      CategoryTheory.Sheaf.H (AlgebraicGeometry.Scheme.Modules.restrict M U.ι).toAddCommGrpSheaf q) := by
  let _ : Module Γ(X, ⊤) (AlgebraicGeometry.sheafCohomology U (M.restrict U.ι) q) :=
    Module.compHom _ U.ι.appTop.hom
  obtain ⟨e⟩ := nonempty_E_linearEquiv_sheafCohomology_restrict M U q
  exact ⟨e.toAddEquiv⟩

end AlgebraicGeometry.Scheme.Modules

end
