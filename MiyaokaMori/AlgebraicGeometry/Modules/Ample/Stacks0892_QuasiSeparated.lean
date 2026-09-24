import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1

/-! # Quasi-compactness and quasi-separatedness in Stacks 0892

The quasi-compact / quasi-separated part of the first paragraph of the proof of Stacks 0892
("quasi-separated" replaces the "separated" of the original, since Stacks 01PW only needs `X`
quasi-compact and quasi-separated):
* `L` relatively ample for `f` (ample on the preimage of every affine open `V`) ⇒ `f`
  quasi-separated: ample ⇒ quasi-separated (Stacks 01PY, `IsAmple.quasiSeparatedSpace`), and
  quasi-separatedness is local on the target (`HasAffineProperty @QuasiSeparated`).
* Quasi-affine preimages of affine opens ⇒ `f` quasi-compact and quasi-separated (a quasi-affine
  scheme is quasi-compact and separated; `IsQuasiAffine`).
Then `quasiSeparatedSpace_of_quasiSeparated` and `QuasiCompact.compactSpace_of_compactSpace` make
`X` quasi-compact and quasi-separated.

References: Stacks 0892, first paragraph of the proof; Stacks 01PY.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- Relatively ample ⇒ quasi-separated morphism (the local form of Stacks 01PY). -/
theorem AlgebraicGeometry.quasiSeparated_of_forall_isAmple_pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (L : X.Modules) [L.IsLineBundle]
    (hL : ∀ V : Y.affineOpens,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L)) :
    AlgebraicGeometry.QuasiSeparated f := by
  refine AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top (P := @AlgebraicGeometry.QuasiSeparated)
    (Q := fun Z _ _ _ => QuasiSeparatedSpace Z)
    (fun V : Y.affineOpens => V) (AlgebraicGeometry.iSup_affineOpens_eq_top Y) (fun V => ?_)
  exact AlgebraicGeometry.IsAmple.quasiSeparatedSpace _ (hL V)

set_option backward.isDefEq.respectTransparency.types false in
/-- Quasi-affine preimages of affine opens ⇒ quasi-compact morphism. -/
theorem AlgebraicGeometry.quasiCompact_of_forall_isQuasiAffine {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (hf : ∀ V : Y.affineOpens, AlgebraicGeometry.Scheme.IsQuasiAffine (f ⁻¹ᵁ V.1)) :
    AlgebraicGeometry.QuasiCompact f := by
  refine AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top (P := @AlgebraicGeometry.QuasiCompact)
    (Q := fun Z _ _ _ => CompactSpace Z)
    (fun V : Y.affineOpens => V) (AlgebraicGeometry.iSup_affineOpens_eq_top Y) (fun V => ?_)
  have := hf V
  exact inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- Quasi-affine preimages of affine opens ⇒ quasi-separated morphism (a quasi-affine scheme is
separated, hence quasi-separated). -/
theorem AlgebraicGeometry.quasiSeparated_of_forall_isQuasiAffine {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (hf : ∀ V : Y.affineOpens, AlgebraicGeometry.Scheme.IsQuasiAffine (f ⁻¹ᵁ V.1)) :
    AlgebraicGeometry.QuasiSeparated f := by
  refine AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top (P := @AlgebraicGeometry.QuasiSeparated)
    (Q := fun Z _ _ _ => QuasiSeparatedSpace Z)
    (fun V : Y.affineOpens => V) (AlgebraicGeometry.iSup_affineOpens_eq_top Y) (fun V => ?_)
  have := hf V
  exact inferInstance

end
