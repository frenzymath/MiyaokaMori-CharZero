import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackIso
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor

/-! # Pullback of the relative tangent sheaf along open immersions

* `relativeTangent_congr`: if `p = p'` then `T_p ≅ T_{p'}` (`eqToIso`);
* `relativeTangent_restrict_open`: for `U ⊆ Z` open, `U.ι^* T_{Z/C} ≅ T_{U/C}` (where `T_{U/C}`
  is the relative tangent sheaf of `U.ι ≫ p`);
* `relativeTangent_pullback_of_isIso`: for an isomorphism `g : W ≅ T`, `g^* T_{T/B} ≅ T_{W/B}`
  (with `W → B` taken to be `g ≫ r`).

References: Stacks 01US (`Ω` is compatible with open subschemes; here `Omega.restrictIso`);
§2.1 of the paper (`E = s^*T_{Z/C}` only sees `Z^×`, and the first term of the tangent sequence
(2.2) is transported along `Z^× ≅ Tot(L)^×`).

Proof: `T_p = (Ω_p)^∨`. Pullback along an open immersion `g` is restriction
(`restrictFunctorIsoPullback`); `Omega.restrictIso` gives `(Ω_p).restrict g ≅ Ω_{g ≫ p}` (for the
square `(g ≫ p) ≫ 𝟙 = g ≫ p`; both `𝟙` and isomorphisms are open immersions); the dual commutes
with pullback along `U.ι` and along isomorphisms (`dual_restrict` / `dual_pullback_of_isIso`), and
the functoriality of the dual (`moduleSheafDualIso`) transports the isomorphism of `Ω` to the dual.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Relative tangent sheaves of equal morphisms are isomorphic (`eqToIso`). -/
def AlgebraicGeometry.relativeTangent_congr {Z C : AlgebraicGeometry.Scheme.{u}} {p p' : Z ⟶ C}
    (h : p = p') : AlgebraicGeometry.relativeTangent p ≅ AlgebraicGeometry.relativeTangent p' :=
  CategoryTheory.eqToIso (by rw [h])

/-- Pullback of `Ω` along an open immersion `g`: `g^*Ω_{T/B} ≅ Ω_{W/B}`, where `W → B` is `g ≫ r`
(Stacks 01US, for the square with base `𝟙_B`). -/
def AlgebraicGeometry.Omega.pullbackIsoOfIsOpenImmersion {W T B : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ T) [AlgebraicGeometry.IsOpenImmersion g] (r : T ⟶ B) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.Omega r) ≅
      AlgebraicGeometry.Omega (g ≫ r) :=
  ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback g).app (AlgebraicGeometry.Omega r)).symm ≪≫
    AlgebraicGeometry.Omega.restrictIso r (g ≫ r) g (CategoryTheory.CategoryStruct.id B)
      (CategoryTheory.Category.comp_id _)

/-- The relative tangent sheaf on an open subscheme: `U.ι^* T_{Z/C} ≅ T_{U/C}`. -/
theorem AlgebraicGeometry.relativeTangent_restrict_open {Z C : AlgebraicGeometry.Scheme.{u}}
    (U : Z.Opens) (p : Z ⟶ C) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (AlgebraicGeometry.relativeTangent p) ≅
      AlgebraicGeometry.relativeTangent (U.ι ≫ p)) := by
  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.Modules.dual_restrict (AlgebraicGeometry.Omega p) U
  exact ⟨d ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso
    (AlgebraicGeometry.Omega.pullbackIsoOfIsOpenImmersion U.ι p).symm⟩

/-- The relative tangent sheaf along an isomorphism `g : W ⟶ T`: `g^* T_{T/B} ≅ T_{W/B}` (with
`W → B` taken to be `g ≫ r`). -/
theorem AlgebraicGeometry.relativeTangent_pullback_of_isIso {W T B : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ T) [IsIso g] (r : T ⟶ B) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.relativeTangent r) ≅
      AlgebraicGeometry.relativeTangent (g ≫ r)) := by
  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.Modules.dual_pullback_of_isIso g (AlgebraicGeometry.Omega r)
  exact ⟨d ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso
    (AlgebraicGeometry.Omega.pullbackIsoOfIsOpenImmersion g r).symm⟩

end
