import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraLocalGenerators

/-! # The coordinates do not all vanish at a point

All coordinates cannot vanish simultaneously at a point of `Y^sp`: for every point `y` there is some `p` with
`σ_p = x_p^{m/q}` nonzero at `y` (locally `Y^sp` is the Proj of a weighted polynomial algebra, the coordinates
generate the algebra over `A_0`, and their basic open sets cover Proj). This is the step "all coordinates cannot
vanish at a projective point" in the proof of Proposition 2.4 of the paper (eq. (2.10)).

## Route

1. `y ∉ supp Z(σ_p)` is `y ∈ nonvanishingLocus σ_p` (`idealSheafOfSection_support_compl_eq_nonvanishingLocus`,
   proved; Stacks 01WX/01CY). So everything is `exists_mem_nonvanishingLocus_coordPowSection` below.
2. Take an affine open `V ∋ π(y)` (`iSup_affineOpens_eq_top`), so `y ∈ π⁻¹V ≅ Proj A(V)` (Stacks 01NQ,
   `relativeProj.affineIso`; `A(V) = ⊕_m Γ(V, S^sp_m)` is `GradedQCAlgebra.sectionsGrading`).
3. The local generators `c_p(φ) ∈ A(V)_q` (`splitCoordGen`, `φ ∈ Γ(V, Q_i^∨)`) generate the irrelevant ideal
   (`splitWeightedAlgebra_irrelevant_le_span_splitCoordGen`), so their basic opens cover `Proj A(V)`
   (Mathlib `Proj.iSup_basicOpen_eq_top`): some `c_p(φ) ∉ 𝔭_{φ_V(y)}`.
4. `c_p(φ) ∉ 𝔭_{φ_V(y)}` forces `y ∈ nonvanishingLocus σ_p`
   (`mem_nonvanishingLocus_coordPowSection_of_splitCoordGen_not_mem`: locally `σ_p` is `x_p^{m/q}/1 ⊗ (frame)`).

The frames of the `Q_i` are used only inside the proofs of the two lemmas: the statements only mention sections of
`Q_i^∨` over an affine `V`, and no identification `A(V) ≅ O(V)[x]` is needed in any statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Every point of `Y^sp` lies in the nonvanishing locus of some coordinate power `σ_p = x_p^{m/q}`
(steps 2–4 of the module docstring). -/
theorem exists_mem_nonvanishingLocus_coordPowSection {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m)
    (y : (splitWeightedProjectivization F kk).left) :
    ∃ p : Fin (n + 1) × Fin kk,
      haveI := coordPowSection_isLineBundle F m hm hdiv p
      y ∈ AlgebraicGeometry.Scheme.Modules.nonvanishingLocus
      ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1)))))
      (coordPowSection F m hdiv p) := by
  -- an affine open `V ∋ π(y)`
  obtain ⟨V, hV⟩ : ∃ V : C.toScheme.affineOpens, (splitWeightedProjectivization F kk).hom y ∈ V.1 := by
    have hmem : (splitWeightedProjectivization F kk).hom y ∈ (⊤ : C.toScheme.Opens) := trivial
    rw [← AlgebraicGeometry.iSup_affineOpens_eq_top C.toScheme] at hmem
    exact Opens.mem_iSup.mp hmem
  have hy : y ∈ (splitWeightedProjectivization F kk).hom ⁻¹ᵁ V.1 := hV
  -- the basic opens of the local generators cover `Proj A(V)`
  have hcov := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
    ((splitWeightedAlgebraOf F kk).sectionsGrading V.1) _
    (splitWeightedAlgebra_irrelevant_le_span_splitCoordGen F V)
  have hy' : (AlgebraicGeometry.Scheme.relativeProj.affineIso (splitWeightedAlgebraOf F kk) V).hom ⟨y, hy⟩ ∈
      (⊤ : (AlgebraicGeometry.Proj ((splitWeightedAlgebraOf F kk).sectionsGrading V.1)).Opens) := trivial
  rw [← hcov] at hy'
  obtain ⟨⟨p, φ⟩, hpφ⟩ := Opens.mem_iSup.mp hy'
  rw [AlgebraicGeometry.Proj.mem_basicOpen] at hpφ
  exact ⟨p, mem_nonvanishingLocus_coordPowSection_of_splitCoordGen_not_mem F m hm hdiv p V φ y hy hpφ⟩

theorem splitWeightedCoord_not_all_vanish {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ} (hkk : 1 ≤ kk) {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m)
    (y : (splitWeightedProjectivization F kk).left) :
    ∃ p : Fin (n + 1) × Fin kk,
      haveI := coordPowSection_isLineBundle F m hm hdiv p
      y ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection _
        (coordPowSection F m hdiv p)).support := by
  obtain ⟨p, hp⟩ := exists_mem_nonvanishingLocus_coordPowSection F m hm hdiv y
  refine ⟨p, ?_⟩
  have := coordPowSection_isLineBundle F m hm hdiv p
  have h := AlgebraicGeometry.Scheme.idealSheafOfSection_support_compl_eq_nonvanishingLocus _
    (coordPowSection F m hdiv p)
  have hmem : y ∈ (SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection _
      (coordPowSection F m hdiv p)).support)ᶜ := by
    rw [h]; exact hp
  exact hmem

end
