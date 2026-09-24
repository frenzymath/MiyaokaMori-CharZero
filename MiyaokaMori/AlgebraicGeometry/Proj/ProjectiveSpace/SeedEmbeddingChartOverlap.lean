import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedEmbeddingIdealCharts

/-!
# Scheme-theoretic overlap of projective embedding charts

For the standard opens `D₊(Xᵢ)` and `D₊(Xⱼ)` of the projective target `P^N_k`, this file records the
affine product chart `D₊(Xᵢ Xⱼ)`. The kernel ideal of a closed immersion `emb : X ⟶ P^N_k` restricts
to that overlap by the actual ideal-sheaf restriction map.  Transporting the same equality through
Mathlib's canonical `basicOpenIsoAway` identifies the corresponding ideals in the degree-zero
homogeneous localization rings.

No homogeneous equation ideal or Proj recovery statement is asserted here.

The chart data are keyed by `(k) (N)` and the kernel data by `(emb : X ⟶ ProjectiveSpace N k)`; see
`SeedEmbeddingIdealCharts`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

namespace ProjectiveEmbedding

/-- The standard projective overlap `D₊(Xᵢ Xⱼ)`. -/
def overlapOpen (N : ℕ) (i j : Fin (N + 1)) : (ProjectiveSpace N k).Opens :=
  Proj.basicOpen (projectiveGrading k N) (MvPolynomial.X i * MvPolynomial.X j)

/-- The product coordinate is homogeneous of positive degree. -/
lemma overlapCoordinate_mem (N : ℕ) (i j : Fin (N + 1)) :
    MvPolynomial.X i * MvPolynomial.X j ∈ projectiveGrading k N 2 := by
  have hi : MvPolynomial.X i ∈ projectiveGrading k N 1 :=
    MvPolynomial.isHomogeneous_X k i
  have hj : MvPolynomial.X j ∈ projectiveGrading k N 1 :=
    MvPolynomial.isHomogeneous_X k j
  simpa [projectiveGrading] using
    (SetLike.mul_mem_graded hi hj)

/-- The product chart packaged as an affine open. -/
def overlapAffineOpen (N : ℕ) (i j : Fin (N + 1)) : (ProjectiveSpace N k).affineOpens :=
  ⟨overlapOpen k N i j,
    Proj.isAffineOpen_basicOpen (projectiveGrading k N)
      (MvPolynomial.X i * MvPolynomial.X j) (overlapCoordinate_mem k N i j) (by decide)⟩

/-- The canonical Away-to-sections isomorphism on the product chart. -/
def overlapIso (N : ℕ) (i j : Fin (N + 1)) :
    CommRingCat.of
        (HomogeneousLocalization.Away (projectiveGrading k N)
          (MvPolynomial.X i * MvPolynomial.X j)) ≅
      Γ(ProjectiveSpace N k, overlapAffineOpen k N i j) := by
  change CommRingCat.of
        (HomogeneousLocalization.Away (projectiveGrading k N)
          (MvPolynomial.X i * MvPolynomial.X j)) ≅
      Γ(Proj (projectiveGrading k N),
        Proj.basicOpen (projectiveGrading k N)
          (MvPolynomial.X i * MvPolynomial.X j))
  exact Proj.basicOpenIsoAway (projectiveGrading k N)
    (MvPolynomial.X i * MvPolynomial.X j) (overlapCoordinate_mem k N i j) (by decide)

/-- The product chart is contained in the `i`th standard chart. -/
lemma overlap_le_standard (N : ℕ) (i j : Fin (N + 1)) :
    overlapOpen k N i j ≤ ProjectiveSpaceOver.chart N k i := by
  exact Proj.basicOpen_mono (projectiveGrading k N)
    (MvPolynomial.X i) (MvPolynomial.X i * MvPolynomial.X j) ⟨MvPolynomial.X j, rfl⟩

/-- The corresponding inclusion of affine-open packages. -/
lemma overlapAffineOpen_le_standardAffineOpen (N : ℕ) (i j : Fin (N + 1)) :
    overlapAffineOpen k N i j ≤ standardAffineOpen k N i := by
  exact overlap_le_standard k N i j

/-- Restriction of sections from the `i`th chart to the product overlap. -/
def chartRestrictionGamma (N : ℕ) (i j : Fin (N + 1)) :
    Γ(ProjectiveSpace N k, standardAffineOpen k N i) →+*
      Γ(ProjectiveSpace N k, overlapAffineOpen k N i j) :=
  ((ProjectiveSpace N k).presheaf.map
    (homOfLE (overlapAffineOpen_le_standardAffineOpen k N i j)).op).hom

/-- The actual chart map from the `i`th Away ring to the overlap Away ring. -/
def chartRestrictionAway (N : ℕ) (i j : Fin (N + 1)) : chartRing k N i →+*
      HomogeneousLocalization.Away (projectiveGrading k N)
        (MvPolynomial.X i * MvPolynomial.X j) :=
  (overlapIso k N i j).inv.hom.comp
    ((chartRestrictionGamma k N i j).comp (chartIso k N i).hom.hom)

variable {k} {X : Scheme.{u}} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k)

/-- The scheme-theoretic kernel ideal on the product chart's section ring. -/
def overlapKernelGamma (i j : Fin (N + 1)) :
    Ideal Γ(ProjectiveSpace N k, overlapAffineOpen k N i j) :=
  emb.ker.ideal (overlapAffineOpen k N i j)

/-- The same overlap kernel transported to the product Away ring. -/
def overlapKernelAway (i j : Fin (N + 1)) :
    Ideal (HomogeneousLocalization.Away (projectiveGrading k N)
      (MvPolynomial.X i * MvPolynomial.X j)) :=
  (overlapKernelGamma emb i j).comap (overlapIso k N i j).hom.hom

/-- The kernel ideal restricts exactly to the product overlap on section rings. -/
theorem chartKernelGamma_restriction (i j : Fin (N + 1)) :
    Ideal.map (chartRestrictionGamma k N i j) (chartKernelGamma emb i) =
      overlapKernelGamma emb i j := by
  change Ideal.map
      ((ProjectiveSpace N k).presheaf.map
        (homOfLE (overlapAffineOpen_le_standardAffineOpen k N i j)).op).hom
      (emb.ker.ideal (standardAffineOpen k N i)) =
    emb.ker.ideal (overlapAffineOpen k N i j)
  exact emb.ker.map_ideal (overlapAffineOpen_le_standardAffineOpen k N i j)

/-- The same compatibility after transport to the canonical Away chart rings. -/
theorem map_comp_ringEquiv_restriction
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R ≃+* S) (r : S →+* T) (g : T ≃+* U) (I : Ideal S) :
    Ideal.map (g.toRingHom.comp (r.comp f.toRingHom)) (I.comap f.toRingHom) =
      (I.map r).comap g.symm.toRingHom := by
  rw [← Ideal.map_map, ← Ideal.map_map]
  rw [Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact Ideal.map_comap_of_equiv (I := I.map r) g

theorem chartKernelAway_restriction (i j : Fin (N + 1)) :
    Ideal.map (chartRestrictionAway k N i j) (chartKernelAway emb i) =
      overlapKernelAway emb i j := by
  unfold chartRestrictionAway chartKernelAway overlapKernelAway
  rw [← chartKernelGamma_restriction emb]
  exact map_comp_ringEquiv_restriction
    (chartIso k N i).commRingCatIsoToRingEquiv
    (chartRestrictionGamma k N i j)
    (overlapIso k N i j).symm.commRingCatIsoToRingEquiv
    (chartKernelGamma emb i)

end ProjectiveEmbedding

end AlgebraicGeometry.Proj
