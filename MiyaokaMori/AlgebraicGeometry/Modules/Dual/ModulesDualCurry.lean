import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualEv

/-! # Currying into the dual, spelled with `dual`

The currying `dualCurry F V : (F ⊗ V ⟶ O_X) ≃ (F ⟶ V^∨)` spelled with `dual V` (its body is
`tensorObjHomEquiv F V O_X`) and its two basic lemmas `dualCurry_symm_apply`,
`dualCurry_naturality_left`. See the header of `ModulesDualEv` for why this bridge is needed.

Proof method: first prove the lemmas at the **variable level** — for an arbitrary object `D` with
`e : D = 𝓗om(V, O_X)`, an arbitrary `c : (F ⊗ V ⟶ O_X) ≃ (F ⟶ D)` heterogeneously equal to
`tensorObjHomEquiv`, and an arbitrary `ev : D ⊗ V ⟶ O_X` heterogeneously equal to `internalHomEval`;
after `subst e` everything is the same term and the `internalHom` lemmas apply directly. Then
substitute `D := dual V`, `c := dualCurry F V`, `ev := dualEv V` (`dualCurry_heq`, `dualEv_heq`
each perform the expensive defeq check once). The resulting `dual`-world lemmas have statements
syntactically identical to the body of `dualMap`, so `rw` applies directly.

Reference: Stacks 01CM (tensor–Hom adjunction and its naturality); this file is only a bridge
between spellings.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The currying `(F ⊗ V ⟶ O_X) ≃ (F ⟶ V^∨)`, spelled with `dual V`; its body is
`tensorObjHomEquiv F V O_X`. -/
def dualCurry {X : AlgebraicGeometry.Scheme.{u}} (F V : X.Modules) :
    (F ⊗ V ⟶ SheafOfModules.unit X.ringCatSheaf) ≃ (F ⟶ dual V) := by
  apply tensorObjHomEquiv F V (SheafOfModules.unit X.ringCatSheaf)

/-- `dualCurry F V` and `tensorObjHomEquiv F V O_X` are heterogeneously equal (the same term, two
spellings of its type). -/
theorem dualCurry_heq {X : AlgebraicGeometry.Scheme.{u}} (F V : X.Modules) :
    HEq (dualCurry F V) (tensorObjHomEquiv F V (SheafOfModules.unit X.ringCatSheaf)) := by
  apply HEq.refl

/-- Variable level: `tensorObjHomEquiv_symm_apply` transferred along `e : D = 𝓗om(V, O_X)` to any
heterogeneously equal `c`, `ev`. -/
theorem curry_symm_apply_of_heq {X : AlgebraicGeometry.Scheme.{u}} (F V : X.Modules) {D : X.Modules}
    (e : D = internalHom V (SheafOfModules.unit X.ringCatSheaf))
    (c : (F ⊗ V ⟶ SheafOfModules.unit X.ringCatSheaf) ≃ (F ⟶ D))
    (hc : HEq c (tensorObjHomEquiv F V (SheafOfModules.unit X.ringCatSheaf)))
    (ev : D ⊗ V ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hev : HEq ev (internalHomEval V (SheafOfModules.unit X.ringCatSheaf))) (ψ : F ⟶ D) :
    c.symm ψ = (ψ ▷ V) ≫ ev := by
  subst e
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hev
  exact tensorObjHomEquiv_symm_apply F V (SheafOfModules.unit X.ringCatSheaf) ψ

/-- Variable level: `tensorObjHomEquiv_naturality_left` transferred along `e : D = 𝓗om(V, O_X)`. -/
theorem curry_naturality_left_of_heq {X : AlgebraicGeometry.Scheme.{u}} {F' F : X.Modules} (V : X.Modules)
    {D : X.Modules} (e : D = internalHom V (SheafOfModules.unit X.ringCatSheaf))
    (c : (F ⊗ V ⟶ SheafOfModules.unit X.ringCatSheaf) ≃ (F ⟶ D))
    (hc : HEq c (tensorObjHomEquiv F V (SheafOfModules.unit X.ringCatSheaf)))
    (c' : (F' ⊗ V ⟶ SheafOfModules.unit X.ringCatSheaf) ≃ (F' ⟶ D))
    (hc' : HEq c' (tensorObjHomEquiv F' V (SheafOfModules.unit X.ringCatSheaf)))
    (a : F' ⟶ F) (f : F ⊗ V ⟶ SheafOfModules.unit X.ringCatSheaf) :
    a ≫ c f = c' ((a ▷ V) ≫ f) := by
  subst e
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hc'
  exact tensorObjHomEquiv_naturality_left V (SheafOfModules.unit X.ringCatSheaf) a f

/-- The inverse of `dualCurry` is `ψ ↦ (ψ ▷ V) ≫ dualEv V`. -/
theorem dualCurry_symm_apply {X : AlgebraicGeometry.Scheme.{u}} (F V : X.Modules) (ψ : F ⟶ dual V) :
    (dualCurry F V).symm ψ = (ψ ▷ V) ≫ dualEv V :=
  curry_symm_apply_of_heq F V (dual_eq_internalHom V) (dualCurry F V) (dualCurry_heq F V)
    (dualEv V) (dualEv_heq V) ψ

/-- `dualCurry` is natural in the first variable: `a ≫ dualCurry f = dualCurry ((a ▷ V) ≫ f)`. -/
theorem dualCurry_naturality_left {X : AlgebraicGeometry.Scheme.{u}} {F' F : X.Modules} (V : X.Modules)
    (a : F' ⟶ F) (f : F ⊗ V ⟶ SheafOfModules.unit X.ringCatSheaf) :
    a ≫ dualCurry F V f = dualCurry F' V ((a ▷ V) ≫ f) :=
  curry_naturality_left_of_heq V (dual_eq_internalHom V) (dualCurry F V) (dualCurry_heq F V)
    (dualCurry F' V) (dualCurry_heq F' V) a f

/-- Currying `(ψ ▷ V) ≫ dualEv V` gives back `ψ` (another reading of `dualCurry_symm_apply`). -/
theorem dualCurry_whiskerRight_ev {X : AlgebraicGeometry.Scheme.{u}} (F V : X.Modules) (ψ : F ⟶ dual V) :
    dualCurry F V ((ψ ▷ V) ≫ dualEv V) = ψ := by
  rw [← dualCurry_symm_apply, Equiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Modules

end
