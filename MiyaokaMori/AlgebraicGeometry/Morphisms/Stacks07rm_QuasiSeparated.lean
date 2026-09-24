import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1

/-! # Quasi-projective morphisms are quasi-separated

A quasi-projective morphism is quasi-separated (Stacks 01VW/01VX: quasi-projective morphisms are of finite type
and have a relatively ample invertible sheaf; a scheme with an ample invertible sheaf is quasi-separated,
Stacks 01Q1 / `IsAmple.quasiSeparatedSpace`).

Proof. `QuasiSeparated` is Zariski-local on the target
(`IsZariskiLocalAtTarget.of_iSup_eq_top` over the affine opens `V` of `S`, `iSup_affineOpens_eq_top`). Over an
affine `V` the target is quasi-separated, so `f ∣_ V` is quasi-separated iff its source `f⁻¹V` is a quasi-separated
space (`quasiSeparated_iff_quasiSeparatedSpace`), and `f⁻¹V` carries the ample line bundle `L|_{f⁻¹V}` provided
by `IsQuasiProjectiveMorphism.exists_relativelyAmple`, whence `IsAmple.quasiSeparatedSpace`.

Used in Stacks 07RM, Step 3: `f_*M` is quasi-coherent because `f` is quasi-compact and quasi-separated. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- A quasi-projective morphism is quasi-separated. (The `set_option` mirrors Mathlib's own
`Morphisms/QuasiSeparated.lean`: without it the instance `HasAffineProperty @QuasiSeparated _` is not found.) -/
theorem AlgebraicGeometry.IsQuasiProjectiveMorphism.quasiSeparated {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) [AlgebraicGeometry.IsQuasiProjectiveMorphism f] : AlgebraicGeometry.QuasiSeparated f := by
  obtain ⟨L, hL, hample⟩ := AlgebraicGeometry.IsQuasiProjectiveMorphism.exists_relativelyAmple (f := f)
  rw [AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top (P := @AlgebraicGeometry.QuasiSeparated)
    (fun V : S.affineOpens => V) (AlgebraicGeometry.iSup_affineOpens_eq_top S)]
  intro V
  show QuasiSeparatedSpace (f ⁻¹ᵁ V.1).toScheme
  exact AlgebraicGeometry.IsAmple.quasiSeparatedSpace _ (hample V)

end
