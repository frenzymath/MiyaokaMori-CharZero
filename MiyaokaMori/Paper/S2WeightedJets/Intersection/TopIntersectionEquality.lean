import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationNonlinear
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationToSplit
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S2WeightedJets.Ygg.FlatFamilyProj
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.RelativeDimensionAdd
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalClass
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopIntersectionDeformationInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGenerationMultiple
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjNormal
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjProperLocal
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopIntersectionRationalFibers
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # Equality of the top intersection numbers

The two deformations together give `(H^sp)^{s_k} = H_k^{s_k}` (Lemma 2.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem proper_relativeProj_of_localProduct_candidate
    {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}}
    (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsProper pX]
    (S : X.GradedQCAlgebra)
    {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) :
    AlgebraicGeometry.IsProper (AlgebraicGeometry.Scheme.relativeProj S).hom := by
  obtain ⟨𝒰, h𝒰⟩ := relativeProj_locallyWeighted_localProduct.{u, u} pX S w hw hS
  letI : AlgebraicGeometry.IsProper
      (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    unfold weightedProjectiveSpace
    exact MiyaokaMori.WeightedJets.local_weightedProjToSpec_isProper
      (R := k) (ι := σ) (w := fun i => (⟨w i, hw i⟩ : ℕ+))
  rw [AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover (P := @AlgebraicGeometry.IsProper)
    𝒰]
  intro i
  obtain ⟨φ, hφ, _⟩ := h𝒰 i
  change AlgebraicGeometry.IsProper
    (CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Scheme.relativeProj S).hom
      (𝒰.f i))
  rw [← hφ]
  infer_instance

private theorem weighted_bundle_proper_candidate {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {C : SmoothProjectiveCurve k} {n r : ℕ}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1) (hr : 1 ≤ r) :
    let V : Fin r → C.toScheme.Modules := fun _ => E.toModules
    let S := @AlgebraicGeometry.Scheme.weightedSymAlgebra _ r V
      (fun _ => E.locallyFree) (fun _ => E.isFiniteType)
    letI : (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
      (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
      (fun _ => E.isFiniteType)).left.Over
        (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(@AlgebraicGeometry.Scheme.weightedProjBundle _ r
        (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
        (fun _ => E.isFiniteType)).hom ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    IsProperOver k (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
      (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
      (fun _ => E.isFiniteType)).left := by
  let V : Fin r → C.toScheme.Modules := fun _ => E.toModules
  let S := @AlgebraicGeometry.Scheme.weightedSymAlgebra _ r
    (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)
  have hrank : ∀ (q : Fin r) (x : C.toScheme), (V q).rankAtStalk x = n + 1 := by
    intro q x
    dsimp [V]
    exact (E.rankAtStalk_eq x).trans hE
  obtain ⟨hS, _⟩ := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    _ r (n + 1) V (fun _ => E.locallyFree) (fun _ => E.isFiniteType) hrank
  let σ := ULift.{u} (Fin (n + 1) × Fin r)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  let hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  letI : Fintype σ := inferInstance
  letI : Nonempty σ := ⟨ULift.up ⟨⟨0, Nat.zero_lt_succ n⟩,
    ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩⟩
  have hS' : S.IsLocallyWeightedPolynomial w hw := by
    simpa [S, V, w, hw] using hS
  let pC : C.toScheme ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  letI : AlgebraicGeometry.IsProper pC := by
    exact IsProjectiveOver.isProper C.projective
  letI : AlgebraicGeometry.IsProper (AlgebraicGeometry.Scheme.relativeProj S).hom :=
    proper_relativeProj_of_localProduct_candidate pC S w hw hS'
  change AlgebraicGeometry.IsProper ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫ pC)
  infer_instance

private theorem weighted_bundle_dimension_candidate {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {n r : ℕ}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1) (hr : 1 ≤ r) :
    (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
      (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
      (fun _ => E.isFiniteType)).left.dimension =
      (n + 1) * r := by
  let V : Fin r → C.toScheme.Modules := fun _ => E.toModules
  let S := @AlgebraicGeometry.Scheme.weightedSymAlgebra _ r V
    (fun _ => E.locallyFree) (fun _ => E.isFiniteType)
  have hrank : ∀ (q : Fin r) (x : C.toScheme), (V q).rankAtStalk x = n + 1 := by
    intro q x
    dsimp [V]
    exact (E.rankAtStalk_eq x).trans hE
  obtain ⟨hS, _⟩ := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    _ r (n + 1) V (fun _ => E.locallyFree) (fun _ => E.isFiniteType) hrank
  let σ := ULift.{u} (Fin (n + 1) × Fin r)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  let hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  letI : Fintype σ := inferInstance
  letI : Nonempty σ := ⟨ULift.up ⟨⟨0, Nat.zero_lt_succ n⟩,
    ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩⟩
  have hS' : S.IsLocallyWeightedPolynomial w hw := by
    simpa [S, V, w, hw] using hS
  have hkw := relativeProj_locallyWeighted_krullDim
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) S w hw hS'
  have hraw : topologicalKrullDim (AlgebraicGeometry.Scheme.relativeProj S).left =
      ((1 : WithBot ℕ∞) + ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞)) := by
    simpa [AlgebraicGeometry.Scheme.weightedProjBundle, S] using hkw.trans (by rw [C.dim_one])
  have hprod : 1 ≤ (n + 1) * r := by
    calc
      1 ≤ r := hr
      _ ≤ (n + 1) * r := Nat.le_mul_of_pos_left r (Nat.succ_pos n)
  have hcardσ : Fintype.card σ = (n + 1) * r := by simp [σ]
  have hraw' : topologicalKrullDim (AlgebraicGeometry.Scheme.relativeProj S).left =
      (((n + 1) * r : ℕ) : WithBot ℕ∞) := by
    rw [hraw, hcardσ, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hprod]
  have hbot : topologicalKrullDim (AlgebraicGeometry.Scheme.relativeProj S).left ≠ ⊥ := by
    rw [hraw']
    exact WithBot.coe_ne_bot
  have htop : topologicalKrullDim (AlgebraicGeometry.Scheme.relativeProj S).left ≠ ⊤ := by
    rw [hraw']
    intro h
    apply ENat.natCast_ne_top ((n + 1) * r)
    exact WithBot.coe_eq_top.mp h
  have hs := AlgebraicGeometry.Scheme.dimension_spec (AlgebraicGeometry.Scheme.relativeProj S).left hbot htop
  exact_mod_cast hs.symm.trans hraw'

private lemma biproduct_rank_candidate {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) :
    ∀ x : C.toScheme,
      AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (CategoryTheory.Limits.biproduct
          (fun i : Fin (n + 1) => (F.lineQuotient i).toModules)) x = n + 1 := by
  intro x
  let Q : Fin (n + 1) → C.toScheme.Modules :=
    fun i => (F.lineQuotient i).toModules
  have hQlf : ∀ i, (Q i).IsLocallyFree := fun i => (F.lineQuotient i).locallyFree
  have hQft : ∀ i, (Q i).IsFiniteType := fun i => (F.lineQuotient i).isFiniteType
  let P : Fin (n + 1) → C.toScheme.Opens → Prop := fun i U =>
    ∃ I : Type u, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (Q i) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
  have hmono : ∀ (i : Fin (n + 1)) (V U : C.toScheme.Opens), V ≤ U → P i U → P i V := by
    intro i V U hVU h
    obtain ⟨I, ⟨e⟩⟩ := h
    exact ⟨I, AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le (Q i) hVU I e⟩
  have hex : ∀ i, ∃ U : C.toScheme.Opens, x ∈ U ∧ P i U := by
    intro i
    obtain ⟨U, I, hxU, e⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree (Q i) x
    exact ⟨U, hxU, I, e⟩
  obtain ⟨U, hxU, hU⟩ := AlgebraicGeometry.Scheme.Modules.exists_common_open x P hmono hex
  choose I hI using hU
  have hfin : ∀ i, Finite (I i) := by
    intro i
    exact AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free
      (Q i) U (I i) (hI i).some x hxU
  letI : ∀ i, Fintype (I i) := fun i => Fintype.ofFinite (I i)
  have eB : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
      (CategoryTheory.Limits.biproduct Q) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Sigma I) := by
    let e0 : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        (CategoryTheory.Limits.biproduct Q) ≅
        CategoryTheory.Limits.biproduct (fun i =>
          (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (Q i)) :=
      (AlgebraicGeometry.Scheme.Modules.pullback U.ι).mapBiproduct Q
    exact e0 ≪≫
      (AlgebraicGeometry.Scheme.Modules.biproduct_iso_free
        (fun i => (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (Q i)) I
        (fun i => (hI i).some)).some
  rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
    (CategoryTheory.Limits.biproduct Q) U (Sigma I) eB x hxU]
  have hcard : ∀ i, Fintype.card (I i) = 1 := by
    intro i
    have hline : AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (F.lineQuotient i).toModules x = 1 :=
      ((F.lineQuotient i).rankAtStalk_eq x).trans (F.lineQuotient i).rank_eq_one
    rw [← hline]
    exact (AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
      (Q i) U (I i) (hI i).some x hxU).symm
  simp [Fintype.card_sigma, hcard]

private theorem split_bundle_dimension_candidate {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {n r : ℕ}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (F : SubbundleFiltration E (n + 1)) (hr : 1 ≤ r) :
    (splitWeightedProjectivization F r).left.dimension = (n + 1) * r := by
  let Q : Fin r → C.toScheme.Modules := fun _ =>
    CategoryTheory.Limits.biproduct (fun i : Fin (n + 1) => (F.lineQuotient i).toModules)
  letI : ∀ q, (Q q).IsLocallyFree := fun q => by
    dsimp [Q]
    infer_instance
  letI : ∀ q, (Q q).IsFiniteType := fun q => by
    dsimp [Q]
    infer_instance
  have hQrank : ∀ (q : Fin r) (x : C.toScheme), (Q q).rankAtStalk x = n + 1 := by
    intro q x
    simpa [Q] using biproduct_rank_candidate F x
  obtain ⟨hS, _⟩ := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    _ r (n + 1) Q (fun _ => inferInstance) (fun _ => inferInstance) hQrank
  let σ := ULift.{u} (Fin (n + 1) × Fin r)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  let hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  letI : Fintype σ := inferInstance
  letI : Nonempty σ := ⟨ULift.up ⟨⟨0, Nat.zero_lt_succ n⟩,
    ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩⟩
  have hS' : (splitWeightedAlgebraOf F r).IsLocallyWeightedPolynomial w hw := by
    simpa [splitWeightedAlgebraOf, Q, w, hw] using hS
  have hkw := relativeProj_locallyWeighted_krullDim
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (splitWeightedAlgebraOf F r) w hw hS'
  have hraw : topologicalKrullDim (splitWeightedProjectivization F r).left =
      ((1 : WithBot ℕ∞) + ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞)) := by
    simpa [splitWeightedProjectivization] using hkw.trans (by rw [C.dim_one])
  have hprod : 1 ≤ (n + 1) * r := by
    calc
      1 ≤ r := hr
      _ ≤ (n + 1) * r := Nat.le_mul_of_pos_left r (Nat.succ_pos n)
  have hcardσ : Fintype.card σ = (n + 1) * r := by simp [σ]
  have hraw' : topologicalKrullDim (splitWeightedProjectivization F r).left =
      (((n + 1) * r : ℕ) : WithBot ℕ∞) := by
    rw [hraw, hcardσ, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hprod]
  have hbot : topologicalKrullDim (splitWeightedProjectivization F r).left ≠ ⊥ := by
    rw [hraw']
    exact WithBot.coe_ne_bot
  have htop : topologicalKrullDim (splitWeightedProjectivization F r).left ≠ ⊤ := by
    rw [hraw']
    intro h
    apply ENat.natCast_ne_top ((n + 1) * r)
    exact WithBot.coe_eq_top.mp h
  have hs := AlgebraicGeometry.Scheme.dimension_spec
    (splitWeightedProjectivization F r).left hbot htop
  exact_mod_cast hs.symm.trans hraw'

private theorem structure_compat_candidate {k : Type u} [Field k]
    {X Z Y Yt Y' : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ι : Z ⟶ Y) (π : Y ⟶ AlgebraicGeometry.Scheme.affineLineOver X)
    (ε : Z ≅ Yt) (πt : Yt ⟶ X) (φ : Yt ≅ Y') (π' : Y' ⟶ X)
    (hε : ε.hom ≫ πt = ι ≫ π ≫ AlgebraicGeometry.Scheme.affineLineOver.toBase X)
    (hφ : φ.hom ≫ π' = πt) :
    (ε ≪≫ φ).hom ≫ π' ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ι ≫ (π ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X) ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase
          (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  have key : AlgebraicGeometry.Scheme.affineLineOver.toBase X ≫
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase
          (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (AlgebraicGeometry.AffineSpace.map_over
      (n := ULift.{u} (Fin 1)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).symm
  calc
    (ε ≪≫ φ).hom ≫ π' ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        (ε.hom ≫ (φ.hom ≫ π')) ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      simp only [Iso.trans_hom, Category.assoc]
    _ = ι ≫ π ≫
        (AlgebraicGeometry.Scheme.affineLineOver.toBase X ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
      rw [hφ, hε]
      simp only [Category.assoc]
    _ = _ := by rw [key]; simp only [Category.assoc]

private theorem twist_compat_candidate {Z Yt Y' : AlgebraicGeometry.Scheme.{u}}
    (ε : Z ≅ Yt) (φ : Yt ≅ Y') (M : Z.Modules) (Mt : Yt.Modules) (M' : Y'.Modules)
    (h1 : Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback ε.hom).obj Mt))
    (h2 : Nonempty (Mt ≅ (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).obj M')) :
    Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback (ε ≪≫ φ).hom).obj M') := by
  obtain ⟨a⟩ := h1
  obtain ⟨b⟩ := h2
  exact ⟨a ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback ε.hom).mapIso b ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp ε.hom φ.hom).app M'⟩

theorem split_tautological_top_intersection_eq {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {C : SmoothProjectiveCurve k} (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom]
    (sec : C.toScheme ⟶ Z.left) (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _)
    [AlgebraicGeometry.IsClosedImmersion sec] (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx)
    {n r : ℕ} [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (hr : 1 ≤ r)
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm0 : 0 < m) (hmdiv : ∃ c, m = c * ((n + 1) * r * jetWeight r))
    (h₁ : letI : (splitWeightedProjectivization F r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
        ⟨(splitWeightedProjectivization F r).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩;
      IsProperOver k (splitWeightedProjectivization F r).left)
    (h₂ : letI : (weightedJetProjectivization (k := k) Z sec hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
        ⟨(weightedJetProjectivization (k := k) Z sec hs r).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩;
      IsProperOver k (weightedJetProjectivization (k := k) Z sec hs r).left)
    [SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ))]
    [SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ))] :
    letI : (splitWeightedProjectivization F r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(splitWeightedProjectivization F r).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : (weightedJetProjectivization (k := k) Z sec hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(weightedJetProjectivization (k := k) Z sec hs r).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩;
    tautologicalTopSelfIntersection (splitWeightedProjectivization F r).left h₁
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ)) m hm0
      = tautologicalTopSelfIntersection (weightedJetProjectivization (k := k) Z sec hs r).left h₂
        (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)) m hm0 := by
  letI : (splitWeightedProjectivization F r).left.Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(splitWeightedProjectivization F r).hom ≫
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : (weightedJetProjectivization (k := k) Z sec hs r).left.Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(weightedJetProjectivization (k := k) Z sec hs r).hom ≫
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let V : Fin r → C.toScheme.Modules := fun _ => E.toModules
  let S := @AlgebraicGeometry.Scheme.weightedSymAlgebra _ r V
    (fun _ => E.locallyFree) (fun _ => E.isFiniteType)
  have hrank : ∀ (q : Fin r) (x : C.toScheme), (V q).rankAtStalk x = n + 1 := by
    intro q x
    dsimp [V]
    exact (E.rankAtStalk_eq x).trans hE
  obtain ⟨hS, _⟩ := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    _ r (n + 1) V (fun _ => E.locallyFree) (fun _ => E.isFiniteType) hrank
  let σ := ULift.{u} (Fin (n + 1) × Fin r)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  let hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  letI : Fintype σ := inferInstance
  letI : Nonempty σ := ⟨ULift.up ⟨⟨0, Nat.zero_lt_succ n⟩,
    ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩⟩
  have hS' : S.IsLocallyWeightedPolynomial w hw := by
    simpa [S, V, w, hw] using hS
  let hmdiv0 := hmdiv
  obtain ⟨mult, hmult⟩ := hmdiv
  have hmult_pos : 0 < mult := by
    have : 0 < ((n + 1) * r * jetWeight r) * mult := by
      rw [Nat.mul_comm ((n + 1) * r * jetWeight r), ← hmult]
      exact hm0
    exact Nat.pos_of_mul_pos_left this
  have hSuff0 := veronese_generation_multiple S w
    (fun i => Finset.mem_Icc.mpr ⟨Nat.succ_pos _, (i.down.2).2⟩) hS' mult hmult_pos
  have hcard : Fintype.card σ = (n + 1) * r := by simp [σ]
  have hEq : mult * (Fintype.card σ * jetWeight r) = m := by
    rw [hcard]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmult.symm
  have hSuff : S.SufficientlyDivisible m := by
    rw [← hEq]
    exact hSuff0
  have hSuff' : (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r
      (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
      (fun _ => E.isFiniteType)).SufficientlyDivisible m := by
    simpa [S] using hSuff
  let pC : C.toScheme ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let hlf : ∀ q : Fin r, (E.toModules).IsLocallyFree := fun _ => E.locallyFree
  let hft : ∀ q : Fin r, (E.toModules).IsFiniteType := fun _ => E.isFiniteType
  let S0 := @AlgebraicGeometry.Scheme.weightedSymAlgebra _ r
    (fun _ : Fin r => E.toModules) hlf hft
  have hSuff0' : S0.SufficientlyDivisible m := by
    simpa [S0, hlf, hft] using hSuff'
  letI : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist S0 (m : ℤ)) :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S0 m hSuff0'
  letI : AlgebraicGeometry.IsProper pC := by
    exact IsProjectiveOver.isProper C.projective
  letI : AlgebraicGeometry.IsProper
      (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
        (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
        (fun _ => E.isFiniteType)).hom :=
    proper_relativeProj_of_localProduct_candidate pC S w hw hS'
  letI : (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
      (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
      (fun _ => E.isFiniteType)).left.Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(@AlgebraicGeometry.Scheme.weightedProjBundle _ r
      (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
      (fun _ => E.isFiniteType)).hom ≫
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let hL_weighted : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r
          (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
          (fun _ => E.isFiniteType)) (m : ℤ)) :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist _ m hSuff'
  letI : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r
          (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
          (fun _ => E.isFiniteType)) (m : ℤ)) := hL_weighted
  let hL_S : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S m hSuff
  letI : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) := hL_S
  have hWBproper : IsProperOver k
      (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
        (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
        (fun _ => E.isFiniteType)).left := by
    exact weighted_bundle_proper_candidate E hE hr
  have hdimWB := weighted_bundle_dimension_candidate E hE hr
  have hgeom := ykGG_integral_normal_projective Z sec hs n r hr hloc
  have hdimJet : (weightedJetProjectivization (k := k) Z sec hs r).left.dimension =
      (n + 1) * r := hgeom.2.2.2.2
  let mBase := (n + 1) * r * jetWeight r
  obtain ⟨hflat, hproj, -, hone, hzero⟩ :=
    deformationFamily_flat_projective Z sec hs Zx hsZx n r E hE hEZ hloc hr mBase rfl
  have hdeformLoc : (deformedJetAlgebra Z sec hs r).IsLocallyWeightedPolynomial w hw := by
    exact deformedJetAlgebra_isLocallyWeightedPolynomial Z sec hs n r hloc
  have hdeformSuff0 := veronese_generation_multiple
    (deformedJetAlgebra Z sec hs r) w
    (fun i => Finset.mem_Icc.mpr ⟨Nat.succ_pos _, (i.down.2).2⟩)
    hdeformLoc mult hmult_pos
  have hdeformSuff : (deformedJetAlgebra Z sec hs r).SufficientlyDivisible m := by
    rw [← hEq]
    exact hdeformSuff0
  let hL_deformed : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (deformedJetAlgebra Z sec hs r) (m : ℤ)) :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist _ m hdeformSuff
  letI : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (deformedJetAlgebra Z sec hs r) (m : ℤ)) := hL_deformed
  let hL_jet : SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)) := inferInstance
  have hfirst :
      @AlgebraicGeometry.topSelfIntersection k _
          (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
            (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
            (fun _ => E.isFiniteType)).left _ hWBproper
          (AlgebraicGeometry.Scheme.relativeProj.twist
            (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r
              (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
              (fun _ => E.isFiniteType)) (m : ℤ)) hL_weighted =
        @AlgebraicGeometry.topSelfIntersection k _
          (weightedJetProjectivization (k := k) Z sec hs r).left _ h₂
          (AlgebraicGeometry.Scheme.relativeProj.twist
            (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)) hL_jet := by
    obtain ⟨e1, he1, hLe1⟩ := hone
    obtain ⟨e0, he0, hLe0⟩ := hzero
    have he0' : e0.hom ≫
        (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
          (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
          (fun _ => E.isFiniteType)).hom ≫ pC =
        ((deformationFamily Z sec hs r).hom ≫
          AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι
          (AlgebraicGeometry.Scheme.affineLineOver.point k 0) ≫
          ((deformationFamily Z sec hs r).hom ≫
            AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme) ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase
            (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      simpa [pC, Category.assoc] using
        (structure_compat_candidate
          (X := C.toScheme)
          (ι := ((deformationFamily Z sec hs r).hom ≫
            AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι
            (AlgebraicGeometry.Scheme.affineLineOver.point k 0))
          (π := (deformationFamily Z sec hs r).hom)
          (ε := e0)
          (πt := (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
            (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
            (fun _ => E.isFiniteType)).hom)
          (φ := CategoryTheory.Iso.refl _)
          (π' := (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
            (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
            (fun _ => E.isFiniteType)).hom)
          he0 (by simp))
    have he1' : e1.hom ≫
        (weightedJetProjectivization (k := k) Z sec hs r).hom ≫ pC =
        ((deformationFamily Z sec hs r).hom ≫
          AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι
          (AlgebraicGeometry.Scheme.affineLineOver.point k 1) ≫
          ((deformationFamily Z sec hs r).hom ≫
            AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme) ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase
            (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      simpa [pC, Category.assoc] using
        (structure_compat_candidate
          (X := C.toScheme)
          (ι := ((deformationFamily Z sec hs r).hom ≫
            AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι
            (AlgebraicGeometry.Scheme.affineLineOver.point k 1))
          (π := (deformationFamily Z sec hs r).hom)
          (ε := e1)
          (πt := (weightedJetProjectivization (k := k) Z sec hs r).hom)
          (φ := CategoryTheory.Iso.refl _)
          (π' := (weightedJetProjectivization (k := k) Z sec hs r).hom)
          he1 (by simp))
    exact @topSelfIntersection_eq_of_rational_fibers k _ _
      ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme)
      _ _
      (AlgebraicGeometry.Scheme.relativeProj.twist (deformedJetAlgebra Z sec hs r) (m : ℤ))
      hL_deformed (0 : k) (1 : k) (Y₁ :=
        (@AlgebraicGeometry.Scheme.weightedProjBundle _ r
          (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
          (fun _ => E.isFiniteType)).left)
      (Y₂ := (weightedJetProjectivization (k := k) Z sec hs r).left)
      _ _ hWBproper h₂
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r
          (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree)
          (fun _ => E.isFiniteType)) (m : ℤ))
      hL_weighted
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ))
      hL_jet
      e0 he0' (by simpa [S] using hLe0 m) e1 he1' (hLe1 m)
        (by rw [hdimWB, hdimJet])
  have hsecond := second_deformation_preserves_top_intersection
    (k := k) hr E hE F m hm0 hmdiv0 h₁ hWBproper
  have htop :
      AlgebraicGeometry.topSelfIntersection (splitWeightedProjectivization F r).left h₁
          (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ)) =
        AlgebraicGeometry.topSelfIntersection
          (weightedJetProjectivization (k := k) Z sec hs r).left h₂
          (AlgebraicGeometry.Scheme.relativeProj.twist
            (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ)) :=
    hsecond.trans hfirst
  have hdimSplit := split_bundle_dimension_candidate E hE F hr
  dsimp [tautologicalTopSelfIntersection]
  rw [hdimSplit, hdimJet]
  norm_num [htop]


end
