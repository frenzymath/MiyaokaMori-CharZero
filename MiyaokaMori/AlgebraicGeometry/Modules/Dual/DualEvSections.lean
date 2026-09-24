import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualEv
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesCoevaluation
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # Evaluation on section pairs in the `dual` spelling

**Evaluation on section pairs, in the `dual` spelling.** For a compatible family of local functionals
`ψ : LH V W` (= `LocalDualSections X V W`) and `t ∈ Γ(V, W)`,
`dualEv V (dualUnit ψ ⊗ t) = ψ(t)` (`dualEv_app_tensorSections_dualUnit`).

This is `internalHomEval_tensorSections_unit` (`Stacks01cmTensorHom`) transported from the
`internalHom V O_X` spelling to the `dual V = moduleSheafDual V` spelling. The two are definitionally
equal but the check is expensive (~7 s, see `ModulesDualEv`), so it
is done **here, exactly twice** (`moduleDualPresheaf_eq_internalHomPresheaf`, and the `HEq` of the two
evaluation functions inside `dualEv_app_tensorSections_dualUnit`), through the variable-level lemma
`ev_tensorSections_unit_of_eq` (everything `subst`-ed to the `internalHom` world). Downstream files
(`DualCoevZigzag`) then stay in the `dual` world and only do syntactic rewriting.

Source: Stacks 01CM (tensor–Hom adjunction; evaluation is the counit on section pairs); no new mathematics.
Used for the correspondence between sections and functionals on the total space of a line bundle.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.DualZigzag

/-- The dual presheaf and the internal-Hom presheaf into `O_X` are the same construction
(definitional equality; expensive, done once here). -/
theorem moduleDualPresheaf_eq_internalHomPresheaf {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf V =
      AlgebraicGeometry.Scheme.Modules.internalHomPresheaf V (SheafOfModules.unit X.ringCatSheaf) := by
  rfl

/-- Variable-level form of `internalHomEval_tensorSections_unit`: for any presheaf `P` equal to the
internal-Hom presheaf, any `ev` heterogeneously equal to `internalHomEval`, and any evaluation function
`val` heterogeneously equal to `χ ↦ χ.1 (Over.mk 𝟙)`, evaluation on `(unit χ) ⊗ t` is `val χ t`. -/
theorem ev_tensorSections_unit_of_eq {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules)
    (P : X.PresheafOfModules)
    (hP : P = AlgebraicGeometry.Scheme.Modules.internalHomPresheaf V (SheafOfModules.unit X.ringCatSheaf))
    (ev : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) V ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hev : HEq ev (AlgebraicGeometry.Scheme.Modules.internalHomEval V (SheafOfModules.unit X.ringCatSheaf)))
    (val : ∀ W : X.Opens, P.obj (op W) → Γ(V, W) → Γ(SheafOfModules.unit X.ringCatSheaf, W))
    (hval : HEq val (fun (W : X.Opens)
      (χ : (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf V
        (SheafOfModules.unit X.ringCatSheaf)).obj (op W)) (t : Γ(V, W)) => (χ.1 (Over.mk (𝟙 W))) t))
    (W : X.Opens) (χ : P.obj (op W)) (t : Γ(V, W)) :
    ev.app W (AlgebraicGeometry.Scheme.Modules.tensorSections
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) V W
      (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
        (op W) χ) t) = val W χ t := by
  subst hP
  obtain rfl := eq_of_heq hev
  obtain rfl := eq_of_heq hval
  exact AlgebraicGeometry.Scheme.Modules.internalHomEval_tensorSections_unit V
    (SheafOfModules.unit X.ringCatSheaf) W χ t

/-- **Evaluation on section pairs, `dual` spelling**: `dualEv V (dualUnit ψ ⊗ t) = ψ (t)`. -/
theorem dualEv_app_tensorSections_dualUnit {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules)
    (W : X.Opens) (ψ : AlgebraicGeometry.Scheme.Modules.Frame.LH V W) (t : Γ(V, W)) :
    (AlgebraicGeometry.Scheme.Modules.dualEv V).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual V) V W
          (AlgebraicGeometry.Scheme.Modules.Frame.dualUnit V W ψ) t) =
      ψ.1 (AlgebraicGeometry.Scheme.Modules.Frame.topZ W) t :=
  ev_tensorSections_unit_of_eq V (AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf V)
    (moduleDualPresheaf_eq_internalHomPresheaf V) (AlgebraicGeometry.Scheme.Modules.dualEv V)
    (AlgebraicGeometry.Scheme.Modules.dualEv_heq V)
    (fun W (ψ : AlgebraicGeometry.Scheme.Modules.Frame.LH V W) t =>
      ψ.1 (AlgebraicGeometry.Scheme.Modules.Frame.topZ W) t)
    (by apply HEq.refl) W ψ t

end AlgebraicGeometry.Scheme.Modules.DualZigzag

end
