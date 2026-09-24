import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.AmpleGivesImmersionProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceTwistAmple
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks01pu

/-! # Projective schemes over a field

A scheme `X` over a field `k` is projective if there are `N` and a `k`-morphism `X ↪ P^N_k` which is a
closed immersion (`IsProjectiveOver`). Equivalently, `X ↘ Spec k` is proper and `X` carries an ample
invertible sheaf (`isProjectiveOver_iff_isProper_and_isAmple`). This is the notion of projective
variety used in the standing conventions of §1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `X` is projective over the field `k`: there are `N` and a closed immersion `X ↪ P^N_k` over `k`. -/
def IsProjectiveOver (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] : Prop :=
  ∃ (N : ℕ) (i : X ⟶ ProjectiveSpace N k),
    AlgebraicGeometry.IsClosedImmersion i ∧ i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))

/-- `X` is projective over `k` if and only if `X ↘ Spec k` is proper and `X` carries an ample line
bundle. Forward direction: a closed immersion into `P^N_k` is proper, hence so is `X ↘ Spec k`, and the
pullback of `O(1)` is ample. Converse: an ample line bundle on the proper `k`-scheme `X` gives an
immersion into some `P^N_k` over `k` (`exists_immersion_projectiveSpace_of_isAmple`), which is proper
(`IsProper.of_comp`) and hence a closed immersion (`IsClosedImmersion.iff_isProper_and_mono`). -/
theorem isProjectiveOver_iff_isProper_and_isAmple (k : Type u) [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    IsProjectiveOver k X ↔
      AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      ∃ (L : X.Modules) (_ : L.IsLineBundle), AlgebraicGeometry.IsAmple L := by
  constructor
  · rintro ⟨N, i, hi, hiOver⟩
    letI : AlgebraicGeometry.IsClosedImmersion i := hi
    constructor
    · have hproper : AlgebraicGeometry.IsProper
          (i ≫ ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
        infer_instance
      rw [hiOver.1] at hproper
      exact hproper
    · let L := (AlgebraicGeometry.Scheme.Modules.pullback i).obj
          (projectiveSpaceTwist k N 1)
      letI : L.IsLineBundle := inferInstance
      refine ⟨L, inferInstance, ?_⟩
      exact AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion i
        (projectiveSpaceTwist k N 1) (projectiveSpaceTwist_one_isAmple k N)
  · rintro ⟨hproper, L, hLLine, hL⟩
    letI : AlgebraicGeometry.IsProper
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hproper
    letI : L.IsLineBundle := hLLine
    letI : CompactSpace X := hL.1
    obtain ⟨N, i, hi, hiOver⟩ :=
      AlgebraicGeometry.exists_immersion_projectiveSpace_of_isAmple k X L hL
    letI : AlgebraicGeometry.IsImmersion i := hi
    haveI : AlgebraicGeometry.IsProper
        (i ≫ ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      rw [hiOver.1]
      infer_instance
    letI : AlgebraicGeometry.IsProper i :=
      AlgebraicGeometry.IsProper.of_comp i
        (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    refine ⟨N, i, ?_, hiOver⟩
    exact (AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono i).2
      ⟨inferInstance, inferInstance⟩

end
