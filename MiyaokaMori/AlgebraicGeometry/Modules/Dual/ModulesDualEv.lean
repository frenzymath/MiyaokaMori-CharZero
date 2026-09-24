import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra

/-! # The evaluation morphism of the dual, spelled with `dual`

The dual sheaf `V^∨ = dual V` (`moduleSheafDual V`) and the internal Hom `internalHom V O_X` are
written by the same construction and are **definitionally equal** (`dual_eq_internalHom`), but this
defeq check is expensive (about 6.5 s in the elaborator and 1.7 s in the kernel per occurrence: the
`map` components of the two presheaf structures `moduleDualPresheaf` / `internalHomPresheaf` are
compared field by field, and `Γ(O_X, W)` has to be unfolded to `Γ(X, W)` to match the linear map
structures). The body of `ModulesDualMap.dualMap` mixes the two spellings, so rewriting it directly
with lemmas spelled with `internalHom` repeats this check at every implicit argument (a single
lemma exceeds 60 s).

This file and `ModulesDualCurry` perform the crossing only a few times (once per declaration, with
`by rfl` / `by apply` rather than `:= rfl` / `by exact`, which would do the check twice); afterwards
all statements live in the `dual` world and use purely syntactic `rw`. This file contains the
equality `dual_eq_internalHom`, the evaluation morphism `dualEv V : V^∨ ⊗ V ⟶ O_X` spelled with
`dual V`, and its heterogeneous equality `dualEv_heq` with `internalHomEval V O_X`.

Reference: Stacks 01CM (tensor–Hom adjunction); this file is only a bridge between spellings.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The dual sheaf and the internal Hom into the structure sheaf are definitionally equal
(`moduleSheafDual` and `internalHom · O_X` are written by the same construction). Downstream, always
transfer along this equality (`subst`); do not cross the two spellings with `rfl`/`show` (about 6.5 s
each time). -/
theorem dual_eq_internalHom {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) :
    dual V = internalHom V (SheafOfModules.unit X.ringCatSheaf) := by
  rfl

/-- The evaluation morphism `V^∨ ⊗ V ⟶ O_X`, spelled with `dual V`; its body is `internalHomEval V O_X`
(`apply` makes the defeq check happen only once). -/
def dualEv {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) :
    dual V ⊗ V ⟶ SheafOfModules.unit X.ringCatSheaf := by
  apply internalHomEval V (SheafOfModules.unit X.ringCatSheaf)

/-- `dualEv V` and `internalHomEval V O_X` are heterogeneously equal (the same term, two spellings of
its type). -/
theorem dualEv_heq {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) :
    HEq (dualEv V) (internalHomEval V (SheafOfModules.unit X.ringCatSheaf)) := by
  apply HEq.refl

end AlgebraicGeometry.Scheme.Modules

end
