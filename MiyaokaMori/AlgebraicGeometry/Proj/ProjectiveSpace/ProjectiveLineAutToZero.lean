import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineLinearAutomorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineRationalPointCoords

/-! # An automorphism of `P¹` over `k` moving a closed point to `0`

For every closed point `q` of `P¹_k` (`k = k̄`) there is a `k`-automorphism of `P¹_k` sending `q` to
the marked point `0 = [0 : 1]` (the point `V₊(x₀)` missed by the standard chart).

Source: linear automorphisms of `P¹` act transitively on closed points (used in the ruled-surface
realization, Corollary 4.3 of the paper). This is `exists_p1_automorphism`
strengthened by the compatibility with the structure morphism to `Spec k`, which
`ProjectiveLine.exists_aut_of_matrix` already provides; the proof is the same case split on the
coordinates of `q` (`ProjectiveLine.exists_coords_of_isClosed`), followed by inverting the
automorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Transitivity of the automorphisms of `P¹` on closed points, compatibly with the structure morphism: for a closed point `p` there is a
`k`-automorphism `g` of `P¹_k` with `g 0 = p` (a linear automorphism, `exists_aut_of_matrix`, given by
the matrix `!![0, v 0; 1, v 1]` if `v 0 ≠ 0` and `!![1, 0; 0, v 1]` otherwise, where `p = [v]`). -/
theorem ProjectiveLine.exists_aut_over_zero_eq {k : Type u} [Field k] [IsAlgClosed k]
    (p : ProjectiveLine k) (hp : IsClosed ({p} : Set (ProjectiveLine k))) :
    ∃ g : ProjectiveLine k ≅ ProjectiveLine k,
      g.hom ≫ ProjectiveSpace.toSpecBase 1 k = ProjectiveSpace.toSpecBase 1 k ∧
      g.hom (ProjectiveLine.zero k) = p := by
  obtain ⟨v, hv, hpv⟩ := ProjectiveLine.exists_coords_of_isClosed p hp
  by_cases hv0 : v 0 ≠ 0
  · let M : Matrix (Fin 2) (Fin 2) k := !![0, v 0; 1, v 1]
    have hdet : IsUnit M.det := by
      rw [show M = !![0, v 0; 1, v 1] by rfl, Matrix.det_fin_two_of]
      apply isUnit_iff_ne_zero.mpr
      simp [hv0]
    obtain ⟨g, hgbase, hgcoord⟩ := ProjectiveLine.exists_aut_of_matrix M hdet
    refine ⟨g, hgbase, ?_⟩
    obtain ⟨hMv, hh⟩ := hgcoord ![0, 1] (by simp)
    rw [ProjectiveLine.ofCoords_zero] at hh
    have hMv_eq : M.mulVec ![0, 1] = v := by
      ext i
      fin_cases i <;> simp [M]
    rw [hpv]
    simpa [hMv_eq] using hh
  · have hv0' : v 0 = 0 := not_ne_iff.mp hv0
    have hv1 : v 1 ≠ 0 := by
      intro h
      apply hv
      funext i
      fin_cases i <;> simp [hv0', h]
    let M : Matrix (Fin 2) (Fin 2) k := !![1, 0; 0, v 1]
    have hdet : IsUnit M.det := by
      rw [show M = !![1, 0; 0, v 1] by rfl, Matrix.det_fin_two_of]
      apply isUnit_iff_ne_zero.mpr
      simpa using hv1
    obtain ⟨g, hgbase, hgcoord⟩ := ProjectiveLine.exists_aut_of_matrix M hdet
    refine ⟨g, hgbase, ?_⟩
    obtain ⟨hMv, hh⟩ := hgcoord ![0, 1] (by simp)
    rw [ProjectiveLine.ofCoords_zero] at hh
    have hMv_eq : M.mulVec ![0, 1] = v := by
      ext i
      fin_cases i <;> simp [M, hv0']
    rw [hpv]
    simpa [hMv_eq] using hh

/-- **Leaf.** For a closed point `q` of `P¹_k` there is a `k`-automorphism `g` of `P¹_k` with
`g q = 0 = [0 : 1]`: the inverse of the automorphism of `exists_aut_over_zero_eq`. -/
theorem ProjectiveLine.exists_aut_over_map_eq_zero {k : Type u} [Field k] [IsAlgClosed k]
    (q : ProjectiveLine k) (hq : IsClosed ({q} : Set (ProjectiveLine k))) :
    ∃ g : ProjectiveLine k ≅ ProjectiveLine k,
      g.hom ≫ ProjectiveSpace.toSpecBase 1 k = ProjectiveSpace.toSpecBase 1 k ∧
      g.hom q = ProjectiveLine.zero k := by
  obtain ⟨g, hg, hgq⟩ := ProjectiveLine.exists_aut_over_zero_eq q hq
  refine ⟨g.symm, ?_, ?_⟩
  · calc g.inv ≫ ProjectiveSpace.toSpecBase 1 k
        = g.inv ≫ (g.hom ≫ ProjectiveSpace.toSpecBase 1 k) := by rw [hg]
      _ = ProjectiveSpace.toSpecBase 1 k := by simp
  · rw [← hgq, ← AlgebraicGeometry.Scheme.Hom.comp_apply, Iso.symm_hom, Iso.hom_inv_id]
    rfl

end
