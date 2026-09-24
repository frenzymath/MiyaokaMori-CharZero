import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbeddingChartFactorization
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Global factorization through the original projective embedding

For a morphism to the same projective space, pull back the original standard
charts and their actual scheme-theoretic kernel ideals. Annihilation of these
kernels constructs local lifts by surjective ring-map descent. The original
closed immersion is a monomorphism, so the lifts agree on overlaps and glue to
a unique morphism into the original target, over the original field.

Everything is keyed on `{X T : Scheme} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k) (F : T ⟶ ProjectiveSpace N k)`:
the chart pullback data (`sourceOpen F i`, `restrictedMap`, `chartPullback F i`, `sourceCover F`) depends only on
`F`; from `descendedSections` on, `[IsClosedImmersion emb]` is a section variable; the over-base statements
(`globalMap_over_base`, `existsUnique_factor`) take `[X.Over (Spec k)] [T.Over (Spec k)]` and the equation
`hemb : emb ≫ (P^N ↘ Spec k) = X ↘ Spec k`. The standard open `D₊(Xᵢ)` is `ProjectiveSpaceOver.chart N k i`,
and the cover is `ProjectiveSpaceOver.iSup_chart N k`.

Source: Theorem 4.2 of the paper (§4). The chart-kernel condition is a hypothesis of this
statement; in the realization theorem it follows from the equations of `X` and their proved vanishing.
Neither local lifts nor their existence, overlap agreement, a cover, or a replacement quotient target are
input data here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Proj.ProjectiveEmbeddingGlobalFactorization

open ProjectiveEmbeddingChartFactorization

universe u

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {X T : Scheme.{u}} {N : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

variable (emb : X ⟶ ProjectiveSpace N k) (F : T ⟶ ProjectiveSpace N k)

/-- The actual inverse image of a standard target chart under the given morphism. -/
def sourceOpen (i : Fin (N + 1)) : T.Opens :=
  F ⁻¹ᵁ ProjectiveSpaceOver.chart N k i

/-- The original scheme morphism restricted to its corresponding source and target
charts. The source open is its actual inverse image. -/
def restrictedMap (i : Fin (N + 1)) :
    (sourceOpen F i).toScheme ⟶ (ProjectiveSpaceOver.chart N k i).toScheme :=
  F.resLE (ProjectiveSpaceOver.chart N k i) (sourceOpen F i) le_rfl

/-- Pull back the original chart ring through this actual restricted morphism.
The `topIso` is the canonical transport from ambient-open sections to global
sections of that same open subscheme. -/
def chartPullback (i : Fin (N + 1)) :
    ProjectiveEmbedding.chartRing k N i →+* Γ((sourceOpen F i).toScheme, ⊤) :=
  (restrictedMap F i).appTop.hom.comp
    ((ProjectiveSpaceOver.chart N k i).topIso.inv.hom.comp (ProjectiveEmbedding.chartIso k N i).hom.hom)

/-- Taking actual inverse images gives a cover of the original source. -/
theorem sourceOpens_cover : (⨆ i, sourceOpen F i) = ⊤ := by
  simp only [sourceOpen, ← Scheme.Hom.preimage_iSup, ProjectiveSpaceOver.iSup_chart N k,
    Scheme.Hom.preimage_top]

/-- The open cover used for gluing; it is derived from the given morphism. -/
def sourceCover : T.OpenCover :=
  T.openCoverOfIsOpenCover (sourceOpen F) (sourceOpens_cover F)

variable (H : ∀ i, ProjectiveEmbedding.chartKernelAway emb i ≤ RingHom.ker (chartPullback F i))
  [IsClosedImmersion emb]

/-- Descend the actual restricted pullback along the original embedding's
surjective section map. No local lift is assumed. -/
def descendedSections (i : Fin (N + 1)) :
    Γ(X, emb ⁻¹ᵁ ProjectiveSpaceOver.chart N k i) →+*
      Γ((sourceOpen F i).toScheme, ⊤) :=
  (sectionMap emb i).liftOfSurjective (sectionMap_surjective emb i)
    ⟨chartPullback F i, by rw [ker_sectionMap]; exact H i⟩

/-- Descent recovers the original restricted pullback on every chart-ring element. -/
theorem descendedSections_comp (i : Fin (N + 1)) :
    (descendedSections emb F H i).comp (sectionMap emb i) = chartPullback F i := by
  exact RingHom.liftOfSurjective_comp (sectionMap emb i) (sectionMap_surjective emb i) _

private theorem descendedSections_app (i : Fin (N + 1)) :
    emb.app (ProjectiveSpaceOver.chart N k i) ≫
        CommRingCat.ofHom (descendedSections emb F H i) =
      (ProjectiveSpaceOver.chart N k i).topIso.inv ≫ (restrictedMap F i).appTop := by
  apply (cancel_epi (ProjectiveEmbedding.chartIso k N i).hom).mp
  change CommRingCat.ofHom ((descendedSections emb F H i).comp (sectionMap emb i)) =
    CommRingCat.ofHom (chartPullback F i)
  exact congrArg CommRingCat.ofHom (descendedSections_comp emb F H i)

/-- The local scheme lift into the actual inverse-image open of the original target. -/
def localLift (i : Fin (N + 1)) :
    (sourceOpen F i).toScheme ⟶ (emb ⁻¹ᵁ ProjectiveSpaceOver.chart N k i).toScheme :=
  (sourceOpen F i).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (descendedSections emb F H i)) ≫
      (preimage_isAffineOpen emb i).isoSpec.inv

/-- The local lift has the same composite with the original restricted embedding
as the original restricted morphism, including the structure sheaf. -/
theorem localLift_restrict (i : Fin (N + 1)) :
    localLift emb F H i ≫ emb ∣_ ProjectiveSpaceOver.chart N k i = restrictedMap F i := by
  apply (cancel_mono (ProjectiveEmbedding.standardAffineOpen k N i).2.isoSpec.hom).mp
  change (localLift emb F H i ≫ emb ∣_ ProjectiveSpaceOver.chart N k i) ≫
      (ProjectiveSpaceOver.chart N k i).toSpecΓ =
    restrictedMap F i ≫ (ProjectiveSpaceOver.chart N k i).toSpecΓ
  rw [Category.assoc]
  calc
    _ = (sourceOpen F i).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (descendedSections emb F H i)) ≫
          Spec.map (emb.app (ProjectiveSpaceOver.chart N k i)) := by
      rw [← Scheme.Opens.toSpecΓ_naturality emb (ProjectiveSpaceOver.chart N k i)]
      simp only [localLift, Category.assoc, IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]
    _ = (sourceOpen F i).toScheme.toSpecΓ ≫
        Spec.map (emb.app (ProjectiveSpaceOver.chart N k i) ≫
          CommRingCat.ofHom (descendedSections emb F H i)) := by rw [Spec.map_comp]
    _ = (sourceOpen F i).toScheme.toSpecΓ ≫
        Spec.map ((ProjectiveSpaceOver.chart N k i).topIso.inv ≫ (restrictedMap F i).appTop) := by
      rw [descendedSections_app]
    _ = _ := by
      simpa only [Scheme.Opens.toSpecΓ, Spec.map_comp, Category.assoc] using
        congrArg (fun m ↦ m ≫ Spec.map (ProjectiveSpaceOver.chart N k i).topIso.inv)
          (Scheme.toSpecΓ_naturality (restrictedMap F i)).symm

/-- The local factor map into the original target scheme. -/
def localMap (i : Fin (N + 1)) : (sourceOpen F i).toScheme ⟶ X :=
  localLift emb F H i ≫ (emb ⁻¹ᵁ ProjectiveSpaceOver.chart N k i).ι

/-- Every local factor recovers the restriction of the given projective morphism. -/
theorem localMap_embedding (i : Fin (N + 1)) :
    localMap emb F H i ≫ emb = (sourceOpen F i).ι ≫ F := by
  rw [localMap, Category.assoc,
    ← morphismRestrict_ι emb (ProjectiveSpaceOver.chart N k i), ← Category.assoc,
    localLift_restrict]
  exact Scheme.Hom.resLE_comp_ι F le_rfl

private theorem localMap_pullback_compatible (i j : Fin (N + 1)) :
    pullback.fst ((sourceCover F).f i) ((sourceCover F).f j) ≫ localMap emb F H i =
      pullback.snd ((sourceCover F).f i) ((sourceCover F).f j) ≫ localMap emb F H j := by
  apply (cancel_mono emb).mp
  simp only [Category.assoc, localMap_embedding]
  exact pullback.condition_assoc F

/-- Glue the locally constructed factors on the actual source preimage cover. -/
def globalMap : T ⟶ X :=
  (sourceCover F).glueMorphisms (localMap emb F H) (localMap_pullback_compatible emb F H)

/-- The global construction restricts to each local factor. -/
theorem globalMap_restrict (i : Fin (N + 1)) :
    (sourceOpen F i).ι ≫ globalMap emb F H = localMap emb F H i := by
  exact (sourceCover F).ι_glueMorphisms (localMap emb F H)
    (localMap_pullback_compatible emb F H) i

/-- The constructed global map factors the original morphism through the original
closed embedding, as an equality of scheme morphisms. -/
theorem globalMap_embedding : globalMap emb F H ≫ emb = F := by
  apply (sourceCover F).hom_ext
  intro i
  change (sourceOpen F i).ι ≫ (globalMap emb F H ≫ emb) =
    (sourceOpen F i).ι ≫ F
  rw [← Category.assoc, globalMap_restrict, localMap_embedding]

/-- Compatibility with the original field structure is derived from the global
factorization and the two original morphisms over that field. -/
theorem globalMap_over_base [X.Over (Spec (CommRingCat.of k))] [T.Over (Spec (CommRingCat.of k))]
    (hemb : emb ≫ (ProjectiveSpace N k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (hF : F ≫ (ProjectiveSpace N k ↘ Spec (CommRingCat.of k)) = T ↘ Spec (CommRingCat.of k)) :
    globalMap emb F H ≫ (X ↘ Spec (CommRingCat.of k)) = T ↘ Spec (CommRingCat.of k) := by
  rw [← hemb, ← Category.assoc, globalMap_embedding]
  exact hF

/-- Closed-immersion monicity gives uniqueness among all morphisms factoring `F` through the
embedding (the factor is `globalMap`; no over-base hypothesis on `b` is needed for uniqueness). -/
theorem factor_unique (b : T ⟶ X) (hb : b ≫ emb = F) :
    b = globalMap emb F H := by
  apply (cancel_mono emb).mp
  exact hb.trans (globalMap_embedding emb F H).symm

include H in
/-- Annihilation of the original standard-chart kernels yields a unique global
factor through the original projective embedding. The local kernel conditions
remain intermediate hypotheses to be derived from the paper's original equations.

Formerly `∃! b : Morphism T X, b.comp e.embedding = F`; the bundled morphism over the field is now
spelled as a scheme morphism together with its over-base equation (same content). -/
theorem existsUnique_factor [X.Over (Spec (CommRingCat.of k))] [T.Over (Spec (CommRingCat.of k))]
    (hemb : emb ≫ (ProjectiveSpace N k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (hF : F ≫ (ProjectiveSpace N k ↘ Spec (CommRingCat.of k)) = T ↘ Spec (CommRingCat.of k)) :
    ∃! b : T ⟶ X, b ≫ (X ↘ Spec (CommRingCat.of k)) = T ↘ Spec (CommRingCat.of k) ∧ b ≫ emb = F := by
  exact ⟨globalMap emb F H, ⟨globalMap_over_base emb F H hemb hF, globalMap_embedding emb F H⟩,
    fun b hb ↦ factor_unique emb F H b hb.2⟩

end AlgebraicGeometry.Proj.ProjectiveEmbeddingGlobalFactorization
