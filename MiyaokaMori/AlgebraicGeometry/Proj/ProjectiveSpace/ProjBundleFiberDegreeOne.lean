import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.ProjBundleFiberDegreeOne_Step
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjBundleFiberDegreeOne_ProjectiveSpaceBasics
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjBundleFiberDegreeOne_HyperplaneIso
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjBundleFiberDegreeOne_BaseCase

/-! # The fiber of a projective bundle has `O(1)`-degree one

`v_1 = 1`: the fiber of `P(E)` is `P^n`, and the top self-intersection of `O(1)` is
`deg(c_1(O_{P^n}(1))^n ∩ [P^n]) = 1`.

Source: Lemma 2.2 of the paper, formula (2.6) (the case `k = 1`).

## Route

Induction on `n` (Stacks 02TW proof / Fulton Ex. 2.5.2, cutting by coordinate hyperplanes); the top
level is assembled from the following lemmas.
* `n = 0`: `deg [P^0] = 1` (`projectiveSpace_zero_topSelfIntersection_one`, module
  `ProjBundleFiberDegreeOne_BaseCase`: `P^0 ≅ Spec K` over `K`).
* `n = m + 1`: `P^{m+1}` is integral of dimension `m + 1` and `x_{m+1} ≠ 0`
  (`ProjBundleFiberDegreeOne_ProjectiveSpaceBasics`), so by Stacks 02SQ and the
  projection formula `(O(1)^{m+1})_{P^{m+1}} = ((O(1)|_H)^m)_H` for the hyperplane `H = Z(x_{m+1})`
  (`topSelfIntersection_eq_zeroScheme`, module `ProjBundleFiberDegreeOne_Step`);
  `H ≅ P^m` over `K` with `O(1)|_H ≅ O_{P^m}(1)` (`projectiveSpace_hyperplane_iso`, module
  `ProjBundleFiberDegreeOne_HyperplaneIso`), and top self-intersection is invariant under `K`-isomorphisms
  (`topSelfIntersection_eq_of_iso_over`), so the induction hypothesis applies.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace ProjBundleFiberDegreeOne

open AlgebraicGeometry

/-- `(O_{P^n}(1)^n) = 1` for every `n`, by induction on `n` (see the module docstring). -/
theorem projectiveSpace_top_selfIntersection_one_aux (K : Type u) [Field K] :
    ∀ (n : ℕ) (hP : IsProperOver K (ProjectiveSpace n K)),
      topSelfIntersection (ProjectiveSpace n K) hP (projectiveSpaceTwist K n 1) = 1
  | 0, hP => projectiveSpace_zero_topSelfIntersection_one K hP
  | m + 1, hP => by
    haveI := projectiveSpace_isIntegral K (m + 1)
    haveI : IsProper (ProjectiveSpace (m + 1) K ↘ Spec (CommRingCat.of K)) := hP
    haveI : IsLocallyNoetherian (ProjectiveSpace (m + 1) K) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveSpace (m + 1) K ↘ Spec (CommRingCat.of K))
    obtain ⟨e, he, ⟨φ⟩⟩ := projectiveSpace_hyperplane_iso K m
    letI : (hyperplaneIdeal K m).subscheme.Over (Spec (CommRingCat.of K)) :=
      ⟨(hyperplaneIdeal K m).subschemeι ≫ (ProjectiveSpace (m + 1) K ↘ Spec (CommRingCat.of K))⟩
    haveI : (hyperplaneIdeal K m).subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    have hZ : IsProperOver K (hyperplaneIdeal K m).subscheme :=
      inferInstanceAs (IsProper ((hyperplaneIdeal K m).subschemeι ≫
        (ProjectiveSpace (m + 1) K ↘ Spec (CommRingCat.of K))))
    haveI : e.hom.IsOver (Spec (CommRingCat.of K)) := ⟨he⟩
    have hdZ : (hyperplaneIdeal K m).subscheme.dimension = m := by
      rw [← Scheme.dimension_eq_of_iso e, projectiveSpace_dimension]
    rw [topSelfIntersection_eq_zeroScheme (k := K) hP (projectiveSpaceTwist K (m + 1) 1)
      (projectiveSpaceCoordinate K (m + 1) (Fin.last (m + 1)))
      (projectiveSpaceCoordinate_ne_zero K (m + 1) _) m (projectiveSpace_dimension K (m + 1)) hZ hdZ]
    have hPm : IsProperOver K (ProjectiveSpace m K) := inferInstance
    rw [← topSelfIntersection_eq_of_iso_over e hPm hZ _ (projectiveSpaceTwist K m 1)
      ⟨φ ≪≫ ((Scheme.Modules.pullbackComp e.hom (hyperplaneIdeal K m).subschemeι).app _).symm⟩]
    exact projectiveSpace_top_selfIntersection_one_aux K m hPm

end ProjBundleFiberDegreeOne

theorem projectiveSpace_top_selfIntersection_one {K : Type u} [Field K]
    (n : ℕ) (hP : IsProperOver K (ProjectiveSpace n K))
    [(projectiveSpaceTwist K n 1).IsLineBundle] :
    AlgebraicGeometry.topSelfIntersection (ProjectiveSpace n K) hP
      (projectiveSpaceTwist K n 1) = 1 :=
  ProjBundleFiberDegreeOne.projectiveSpace_top_selfIntersection_one_aux K n hP

end
