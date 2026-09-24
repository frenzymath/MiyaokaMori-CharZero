import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # The charts of a relative Proj form a locally directed cover

Statement (Stacks 01NQ, set-theoretic part of the gluing): two points `y ∈ Proj S(U)`, `z ∈ Proj S(V)` of
two charts of the relative Proj `Proj_X S` with the same image `ι_U y = ι_V z` come from a common
refinement: there is `W ≤ U`, `W ≤ V` in the small affine Zariski site and `w ∈ Proj S(W)` with
`ρ_{W≤U} w = y` and `ρ_{W≤V} w = z`, where `ρ_h = S.projFunctor.map (homOfLE h) = Proj.map (S.restrictGraded h)`.

Proof. Let `x := ι_U y = ι_V z` and `π := S.relativeProj.hom`. Since `ι_U ≫ π = projToOpen U ≫ U.ι`
(`projChart_hom`), `π x ∈ U`; likewise `π x ∈ V`. By `exists_basicOpen_le_affine_inter` there are
`f ∈ Γ(X, U)`, `g ∈ Γ(X, V)` with `X.basicOpen f = X.basicOpen g ∋ π x`. Put `W := U.basicOpen f`; then
`W ≤ U` (witness `f`) and `W ≤ V` (witness `g`). Now `x ∈ π⁻¹ W = im ι_W` (`proj_preimage_eq_opensRange`),
so `x = ι_W w` for some `w`. Since `ρ_{W≤U} ≫ ι_U = ι_W` (`map_projChart`), `ι_U (ρ_{W≤U} w) = ι_W w = x = ι_U y`,
and `ι_U` is injective (open immersion), so `ρ_{W≤U} w = y`; the same for `V`.

Source: Stacks 01NQ / 01LI (the charts `Proj S(U)` form a locally directed open cover of `Proj_X S`).
Used for the gluing of `O(m)` (Stacks 01LI) on `Y_k^GG` (Lemma 2.2 of the paper).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- The structure map sends the chart `Proj S(U)` into `U`. -/
theorem relativeProj_hom_projChart_mem (U : X.AffineZariskiSite) (y : Proj (S.grading U)) :
    S.relativeProj.hom (S.projChart U y) ∈ U.toOpens := by
  rw [← Scheme.Hom.comp_apply, S.projChart_hom, Scheme.Hom.comp_apply]
  exact (S.projToOpen U y).2

/-- Two chart points with the same image in `Proj_X S` come from a common refinement chart. -/
theorem exists_projFunctor_map_eq_of_projChart_eq {U V : X.AffineZariskiSite}
    (y : Proj (S.grading U)) (z : Proj (S.grading V)) (h : S.projChart U y = S.projChart V z) :
    ∃ (W : X.AffineZariskiSite) (hWU : W ≤ U) (hWV : W ≤ V) (w : Proj (S.grading W)),
      S.projFunctor.map (homOfLE hWU) w = y ∧ S.projFunctor.map (homOfLE hWV) w = z := by
  have hxU : S.relativeProj.hom (S.projChart U y) ∈ U.toOpens :=
    S.relativeProj_hom_projChart_mem U y
  have hxV : S.relativeProj.hom (S.projChart U y) ∈ V.toOpens := by
    rw [h]; exact S.relativeProj_hom_projChart_mem V z
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 _ ⟨hxU, hxV⟩
  refine ⟨U.basicOpen f, U.basicOpen_le f, ⟨g, hfg.symm⟩, ?_⟩
  have hxW : S.projChart U y ∈ S.relativeProj.hom ⁻¹ᵁ (U.basicOpen f).toOpens := hxf
  rw [S.proj_preimage_eq_opensRange] at hxW
  obtain ⟨w, hw⟩ := hxW
  have hU' := congrArg (fun φ => φ w) (S.map_projChart (U.basicOpen_le f))
  have hV' := congrArg (fun φ => φ w) (S.map_projChart (show U.basicOpen f ≤ V from ⟨g, hfg.symm⟩))
  simp only at hU' hV'
  refine ⟨w, ?_, ?_⟩
  · exact (S.projChart U).isOpenEmbedding.injective (hU'.trans hw)
  · exact (S.projChart V).isOpenEmbedding.injective (hV'.trans (hw.trans h))

/-- A chart point of `Proj S(V)` lying (in `Proj_X S`) over the chart `Proj S(U)` comes from a common
refinement `W ≤ U`, `W ≤ V`. -/
theorem exists_le_le_of_projChart_mem_opensRange {U V : X.AffineZariskiSite}
    (z : Proj (S.grading V)) (hz : S.projChart V z ∈ (S.projChart U).opensRange) :
    ∃ (W : X.AffineZariskiSite) (_hWU : W ≤ U) (hWV : W ≤ V) (w : Proj (S.grading W)),
      S.projFunctor.map (homOfLE hWV) w = z := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨W, hWU, hWV, w, -, hw⟩ := S.exists_projFunctor_map_eq_of_projChart_eq y z hy
  exact ⟨W, hWU, hWV, w, hw⟩

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
