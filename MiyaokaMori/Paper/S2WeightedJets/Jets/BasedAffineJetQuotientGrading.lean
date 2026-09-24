import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The grading on the quotient of a graded algebra by a homogeneous ideal

`HomogeneousQuotient.grading 𝒜 J hJ : GradedAlgebra (HomogeneousQuotient.component 𝒜 J)`:
the degree-`i` piece of `A ⧸ J` is the image of `𝒜 i` under the quotient map, and the
direct-sum decomposition is descended from the decomposition of `A` using homogeneity of
`J`. Its inverse is the canonical finite sum of homogeneous pieces. No grading or
decomposition of the quotient is supplied as an input or selected from an unproved
existence statement. It is used to build the grading of the one based jet algebra,
`BasedJetAlgebra.grading` (`JetAlgebraGrading`).

Sources: §2 of the paper (the grading of the jet coordinate algebra by parameter rescaling); Ein–Mustață,
*Jet Schemes and Singularities*, §2, Proposition 2.2, the affine coefficient-equation construction.
-/

noncomputable section

namespace MiyaokaMori.BasedAffineJetQuotientGrading

open scoped DirectSum

namespace HomogeneousQuotient

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : Ideal A)

/-- A quotient homogeneous piece is the image of the corresponding original piece. -/
def component (i : ℕ) : Submodule R (A ⧸ J) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R J).toLinearMap

/-- The canonical quotient map restricted to one homogeneous piece. -/
def componentMap (i : ℕ) : 𝒜 i →ₗ[R] component 𝒜 J i :=
  (Ideal.Quotient.mkₐ R J).toLinearMap.submoduleMap (𝒜 i)

private def mapDirectSum : (⨁ i, 𝒜 i) →+ ⨁ i, component 𝒜 J i :=
  DirectSum.map fun i ↦ (componentMap 𝒜 J i).toAddMonoidHom

private def mappedDecomposition : A →+ ⨁ i, component 𝒜 J i :=
  (mapDirectSum 𝒜 J).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

private theorem mappedDecomposition_eq_zero (hJ : J.IsHomogeneous 𝒜)
    (a : A) (ha : a ∈ J) : mappedDecomposition 𝒜 J a = 0 := by
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change Ideal.Quotient.mk J (DirectSum.decompose 𝒜 a i : A) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJ i ha)

/-- The explicit decomposition map on the quotient, obtained by descending the
original decomposition followed by the quotient maps on all components. -/
def decompositionMap (hJ : J.IsHomogeneous 𝒜) : (A ⧸ J) →+ ⨁ i, component 𝒜 J i :=
  QuotientAddGroup.lift J.toAddSubgroup (mappedDecomposition 𝒜 J)
    (mappedDecomposition_eq_zero 𝒜 J hJ)

/-- The descended decomposition on a polynomial class is its original decomposition
followed componentwise by the actual quotient map. -/
theorem decompositionMap_mk (hJ : J.IsHomogeneous 𝒜) (a : A) :
    decompositionMap 𝒜 J hJ (Ideal.Quotient.mk J a) =
      DirectSum.map (fun i ↦ (componentMap 𝒜 J i).toAddMonoidHom)
        (DirectSum.decompose 𝒜 a) := rfl

private theorem recompose_mapDirectSum :
    (DirectSum.coeAddMonoidHom (component 𝒜 J)).comp (mapDirectSum 𝒜 J) =
      (Ideal.Quotient.mk J).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
  apply DirectSum.addHom_ext
  intro i a
  simp only [AddMonoidHom.comp_apply, mapDirectSum, DirectSum.map_of,
    DirectSum.coeAddMonoidHom_of]
  rfl

private theorem recompose_decompositionMap (hJ : J.IsHomogeneous 𝒜) :
    (DirectSum.coeAddMonoidHom (component 𝒜 J)).comp (decompositionMap 𝒜 J hJ) =
      AddMonoidHom.id (A ⧸ J) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change DirectSum.coeAddMonoidHom (component 𝒜 J)
      (mapDirectSum 𝒜 J (DirectSum.decompose 𝒜 a)) = Ideal.Quotient.mk J a
  rw [← AddMonoidHom.comp_apply, recompose_mapDirectSum, AddMonoidHom.comp_apply]
  change Ideal.Quotient.mk J ((DirectSum.decompose 𝒜).symm
      (DirectSum.decompose 𝒜 a)) = Ideal.Quotient.mk J a
  rw [Equiv.symm_apply_apply]

private theorem decompositionMap_homogeneous (hJ : J.IsHomogeneous 𝒜)
    (i : ℕ) (x : component 𝒜 J i) :
    decompositionMap 𝒜 J hJ (x : A ⧸ J) =
      DirectSum.of (fun j ↦ component 𝒜 J j) i x := by
  rcases x with ⟨x, hx⟩
  rcases Submodule.mem_map.mp hx with ⟨a, ha, rfl⟩
  change decompositionMap 𝒜 J hJ (Ideal.Quotient.mk J a) = _
  rw [decompositionMap_mk, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl

/-- A genuine decomposition of the quotient as the direct sum of the images of the
homogeneous pieces, with both inverse laws proved from the descended map. -/
def decomposition (hJ : J.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (component 𝒜 J) :=
  DirectSum.Decomposition.ofAddHom (component 𝒜 J) (decompositionMap 𝒜 J hJ)
    (recompose_decompositionMap 𝒜 J hJ) (by
      apply DirectSum.addHom_ext
      intro i x
      simpa only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply] using decompositionMap_homogeneous 𝒜 J hJ i x)

private def componentGradedMonoid : SetLike.GradedMonoid (component 𝒜 J) where
  one_mem := Submodule.mem_map.mpr
    ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mkₐ R J)⟩
  mul_mem := by
    intro i j x y hx hy
    rcases Submodule.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨b, hb, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mkₐ R J) a b⟩

/-- The quotient by a homogeneous ideal is graded by the actual images of its
homogeneous submodules. This constructor includes the explicit decomposition. -/
def grading (hJ : J.IsHomogeneous 𝒜) : GradedAlgebra (component 𝒜 J) where
  toGradedMonoid := componentGradedMonoid 𝒜 J
  toDecomposition := decomposition 𝒜 J hJ

end HomogeneousQuotient

end MiyaokaMori.BasedAffineJetQuotientGrading
