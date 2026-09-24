import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIsoSectionsHom
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # Isomorphic graded algebras have isomorphic relative Proj, step 2: chart-level isomorphisms

For an isomorphism `φ : S ≅ T` of graded quasi-coherent algebras and an affine open `U`,
the sections-level graded ring homomorphisms `toHom φ U : A_S(U) → A_T(U)` and
`invHom φ U : A_T(U) → A_S(U)` (from step 1) are mutually inverse, hence satisfy the
irrelevant-ideal hypothesis of Mathlib's `Proj.map`, and `Proj.map (invHom φ U)` is an isomorphism
`Proj A_S(U) ≅ Proj A_T(U)` (`chartIso φ U`; inverse `Proj.map (toHom φ U)`, by `Proj.map_comp` /
`Proj.map_id`). These isomorphisms are natural in `U` (`chartIso_naturality`: both composites are
`Proj.map` of the same graded ring homomorphism, by the naturality of `sectionsGradedHom` with respect
to restriction) and compatible with the structure morphisms `Proj A(U) → U`
(`chartIso_hom_projToOpen`: `AlgebraicGeometry.Proj.proj_map_toSpecZero` plus the compatibility of
`sectionsGradedHom` with the unit `Γ(X,U) → A(U)_0`).

Source: Stacks 01NP (functoriality of relative Proj), 01MX (`Proj.map`); the paper uses
"S ≅ T ⇒ Proj_X S ≅ Proj_X T" without comment.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A graded ring homomorphism with a left inverse satisfies the irrelevant-ideal hypothesis of
`Proj.map`: if `f ∘ g = id` then `ℬ₊ ⊆ f(𝒜₊)·ℬ` (every homogeneous `x ∈ ℬ_d`, `d > 0`, is
`f (g x)` with `g x ∈ 𝒜_d ⊆ 𝒜₊`). -/
theorem HomogeneousIdeal.irrelevant_le_map_of_leftInverse {A B σ τ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : ∀ x, f (g x) = x) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro d hd x hx
  show x ∈ Ideal.map f (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  have hgx : g x ∈ HomogeneousIdeal.irrelevant 𝒜 :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd (g.map_mem hx)
  rw [← hfg x]
  exact Ideal.mem_map_of_mem _ hgx

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra}

/-- The restriction maps of the new-foundation algebra `S.toGradedAffineAlgebra` are the
sections-level restrictions `sectionsRestrict` (definitional). -/
theorem toGradedAffineAlgebra_restrictGraded (S : X.GradedQCAlgebra) {U V : X.AffineZariskiSite}
    (h : U ≤ V) :
    S.toGradedAffineAlgebra.restrictGraded h
      = S.sectionsRestrict (AffineZariskiSite.toOpens_mono h) :=
  GradedRingHom.ext fun _ => rfl

/-- The unit of `S.toGradedAffineAlgebra` is `sectionsUnit` (definitional). -/
theorem toGradedAffineAlgebra_unitHom (S : X.GradedQCAlgebra) (U : X.AffineZariskiSite)
    (r : Γ(X, U.toOpens)) :
    S.toGradedAffineAlgebra.toAffineAlgebra.unitHom U r
      = (S.sectionsUnit U.toOpens r : S.sectionsRing U.toOpens) := rfl

namespace projIsoOfIso

variable (φ : S ≅ T) (U : X.AffineZariskiSite)

/-- `A_S(U) → A_T(U)` induced by `φ.hom`. -/
def toHom : S.toGradedAffineAlgebra.grading U →+*ᵍ T.toGradedAffineAlgebra.grading U :=
  φ.hom.sectionsGradedHom U.toOpens

/-- `A_T(U) → A_S(U)` induced by `φ.inv`. -/
def invHom : T.toGradedAffineAlgebra.grading U →+*ᵍ S.toGradedAffineAlgebra.grading U :=
  φ.inv.sectionsGradedHom U.toOpens

theorem invHom_comp_toHom : (invHom φ U).comp (toHom φ U) = GradedRingHom.id _ := by
  have h := Hom.sectionsGradedHom_comp φ.hom φ.inv U.toOpens
  rw [φ.hom_inv_id, Hom.sectionsGradedHom_id] at h
  exact h.symm

theorem toHom_comp_invHom : (toHom φ U).comp (invHom φ U) = GradedRingHom.id _ := by
  have h := Hom.sectionsGradedHom_comp φ.inv φ.hom U.toOpens
  rw [φ.inv_hom_id, Hom.sectionsGradedHom_id] at h
  exact h.symm

theorem invHom_toHom (x : S.toGradedAffineAlgebra.toAffineAlgebra.sections U) :
    invHom φ U (toHom φ U x) = x :=
  DFunLike.congr_fun (invHom_comp_toHom φ U) x

theorem toHom_invHom (x : T.toGradedAffineAlgebra.toAffineAlgebra.sections U) :
    toHom φ U (invHom φ U x) = x :=
  DFunLike.congr_fun (toHom_comp_invHom φ U) x

theorem irrelevant_le_map_toHom :
    HomogeneousIdeal.irrelevant (T.toGradedAffineAlgebra.grading U) ≤
      (HomogeneousIdeal.irrelevant (S.toGradedAffineAlgebra.grading U)).map (toHom φ U) :=
  HomogeneousIdeal.irrelevant_le_map_of_leftInverse _ _ (toHom_invHom φ U)

theorem irrelevant_le_map_invHom :
    HomogeneousIdeal.irrelevant (S.toGradedAffineAlgebra.grading U) ≤
      (HomogeneousIdeal.irrelevant (T.toGradedAffineAlgebra.grading U)).map (invHom φ U) :=
  HomogeneousIdeal.irrelevant_le_map_of_leftInverse _ _ (invHom_toHom φ U)

private theorem proj_map_congr {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
    {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    AlgebraicGeometry.Proj.map f hf = AlgebraicGeometry.Proj.map g hg := by
  subst e; rfl

/-- The chart isomorphism `Proj A_S(U) ≅ Proj A_T(U)` (`Proj.map` of `invHom`, inverse `Proj.map`
of `toHom`). -/
def chartIso : AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading U) ≅
    AlgebraicGeometry.Proj (T.toGradedAffineAlgebra.grading U) where
  hom := AlgebraicGeometry.Proj.map (invHom φ U) (irrelevant_le_map_invHom φ U)
  inv := AlgebraicGeometry.Proj.map (toHom φ U) (irrelevant_le_map_toHom φ U)
  hom_inv_id := by
    have h := AlgebraicGeometry.Proj.map_comp (toHom φ U) (invHom φ U)
      (irrelevant_le_map_toHom φ U) (irrelevant_le_map_invHom φ U)
    rw [← h, proj_map_congr (invHom_comp_toHom φ U) _ (by simp)]
    exact AlgebraicGeometry.Proj.map_id
  inv_hom_id := by
    have h := AlgebraicGeometry.Proj.map_comp (invHom φ U) (toHom φ U)
      (irrelevant_le_map_invHom φ U) (irrelevant_le_map_toHom φ U)
    rw [← h, proj_map_congr (toHom_comp_invHom φ U) _ (by simp)]
    exact AlgebraicGeometry.Proj.map_id

theorem chartIso_hom :
    (chartIso φ U).hom = AlgebraicGeometry.Proj.map (invHom φ U) (irrelevant_le_map_invHom φ U) :=
  rfl

/-- `invHom` commutes with restriction. -/
theorem restrictGraded_comp_invHom {U V : X.AffineZariskiSite} (h : U ≤ V) :
    (S.toGradedAffineAlgebra.restrictGraded h).comp (invHom φ V)
      = (invHom φ U).comp (T.toGradedAffineAlgebra.restrictGraded h) := by
  rw [toGradedAffineAlgebra_restrictGraded, toGradedAffineAlgebra_restrictGraded]
  exact (φ.inv.sectionsGradedHom_restrict (AffineZariskiSite.toOpens_mono h)).symm

/-- Naturality of the chart isomorphisms in `U`. -/
theorem chartIso_naturality {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    S.toGradedAffineAlgebra.projFunctor.map f ≫ (chartIso φ V).hom =
      (chartIso φ U).hom ≫ T.toGradedAffineAlgebra.projFunctor.map f := by
  have h1 := AlgebraicGeometry.Proj.map_comp (invHom φ V)
    (S.toGradedAffineAlgebra.restrictGraded (leOfHom f))
    (irrelevant_le_map_invHom φ V) (S.toGradedAffineAlgebra.restrict_irrelevant_le (leOfHom f))
  have h2 := AlgebraicGeometry.Proj.map_comp (T.toGradedAffineAlgebra.restrictGraded (leOfHom f))
    (invHom φ U)
    (T.toGradedAffineAlgebra.restrict_irrelevant_le (leOfHom f)) (irrelevant_le_map_invHom φ U)
  show AlgebraicGeometry.Proj.map (S.toGradedAffineAlgebra.restrictGraded (leOfHom f))
      (S.toGradedAffineAlgebra.restrict_irrelevant_le (leOfHom f)) ≫
      AlgebraicGeometry.Proj.map (invHom φ V) (irrelevant_le_map_invHom φ V) =
    AlgebraicGeometry.Proj.map (invHom φ U) (irrelevant_le_map_invHom φ U) ≫
      AlgebraicGeometry.Proj.map (T.toGradedAffineAlgebra.restrictGraded (leOfHom f))
        (T.toGradedAffineAlgebra.restrict_irrelevant_le (leOfHom f))
  rw [← h1, ← h2]
  exact proj_map_congr (restrictGraded_comp_invHom φ (leOfHom f)) _ _

/-- `invHom` commutes with the units `Γ(X,U) → A(U)_0`. -/
theorem invHom_unitHom (r : Γ(X, U.toOpens)) :
    invHom φ U (T.toGradedAffineAlgebra.toAffineAlgebra.unitHom U r)
      = S.toGradedAffineAlgebra.toAffineAlgebra.unitHom U r :=
  φ.inv.sectionsGradedHom_sectionsUnit U.toOpens r

/-- The chart isomorphisms are compatible with the structure morphisms `Proj A(U) → U`. -/
theorem chartIso_hom_projToOpen :
    (chartIso φ U).hom ≫ T.toGradedAffineAlgebra.projToOpen U
      = S.toGradedAffineAlgebra.projToOpen U := by
  have h1 := AlgebraicGeometry.Proj.proj_map_toSpecZero (invHom φ U) (irrelevant_le_map_invHom φ U)
  have h2 : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (invHom φ U).gradedZeroRingHom) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (T.toGradedAffineAlgebra.unitZero U)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero U)) := by
    rw [← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext r
    exact invHom_unitHom φ U r
  show AlgebraicGeometry.Proj.map (invHom φ U) (irrelevant_le_map_invHom φ U) ≫
      (AlgebraicGeometry.Proj.toSpecZero (T.toGradedAffineAlgebra.grading U) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (T.toGradedAffineAlgebra.unitZero U)) ≫
        U.2.isoSpec.inv) =
    AlgebraicGeometry.Proj.toSpecZero (S.toGradedAffineAlgebra.grading U) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero U)) ≫
      U.2.isoSpec.inv
  rw [reassoc_of% h1, reassoc_of% h2]

end projIsoOfIso

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
