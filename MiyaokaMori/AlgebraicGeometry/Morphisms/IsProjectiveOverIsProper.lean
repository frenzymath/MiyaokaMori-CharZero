import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism

/-! # Projective over a field implies proper

A scheme projective over a field `k` has proper structure morphism. This is used for the standing
conventions of §1 of the paper (all varieties are projective over `k`, hence proper);
Stacks Project, Tag 01WC.

Proof: `IsProjectiveOver k X` provides a closed immersion `i : X ⟶ P^N_k` with
`i ≫ (P^N_k ↘ Spec k) = X ↘ Spec k`. Closed immersions are proper (Mathlib instance),
`P^N_k ↘ Spec k` is proper (`ProjectiveSpace.isProper_toSpecBase`), and properness is closed under
composition, so `X ↘ Spec k` is proper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Projective implies proper structure morphism (Stacks Project, Tag 01WC): the closed immersion
`i : X ⟶ P^N_k` is proper, `P^N_k ↘ Spec k` is proper, and so is the composite
`i ≫ (P^N_k ↘ Spec k) = X ↘ Spec k`. Usable in dot notation as `hproj.isProper`,
`C.projective.isProper`. -/
theorem IsProjectiveOver.isProper {k : Type u} [Field k] {Γ : AlgebraicGeometry.Scheme.{u}}
    [Γ.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hproj : IsProjectiveOver k Γ) :
    AlgebraicGeometry.IsProper (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  obtain ⟨N, i, hi, ho⟩ := hproj
  have : AlgebraicGeometry.IsClosedImmersion i := hi
  have : AlgebraicGeometry.IsProper
      (i ≫ ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstance
  rwa [ho.1] at this

end
