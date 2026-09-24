import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.TangentBundle
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeAdditiveShortExact
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeAdditiveFiltration
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ExtensionLocallyFree
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAdditiveShortExact
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.Paper.S2WeightedJets.Cone.TangentSequence
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import Mathlib.Data.Finite.Sigma

/-! # Rank and degree of the cone tangent bundle

From the tangent sequence, `rk E = n+1` and `deg E = d`: `E = s^*T_{𝒵/C}` is a vector bundle of
rank `1 + n` and degree `deg O_C + deg f^*T_X = 0 + d`, where `d = deg f^*T_X` is the degree in the
main theorem (eq. (2.3) of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem cone_rank_degree {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {X : SmoothProjectiveVariety k} {N δ : ℕ}
    (e : ProjectiveEmbedding k X.toScheme N) (E : EmbeddingEquations k e δ)
    (f : C.toScheme ⟶ X.toScheme)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord)
    (hvanish : ∀ j, evalHomogeneousAtSections (seedLineBundle e f) (E.F j) (E.homogeneous j) coord = 0) :
    let Z := twistedAffineCone (seedLineBundle e f) N E.deg E.F E.homogeneous
    let s := seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous hvanish
    ∃ V : AlgebraicGeometry.VectorBundle C.toVariety,
      Nonempty (V.toModules ≅ coneTangentBundle Z.hom s.1 s.2) ∧
      V.rank = X.toVariety.dim + 1 ∧
      VectorBundle.degree V = TangentBundle.pullbackDegree f := by
  dsimp
  obtain ⟨i, π, hz, hS⟩ :=
    cone_tangent_shortExact e E E.deg_pos f coord hcoord hvanish
  let S : CategoryTheory.ShortComplex C.toScheme.Modules :=
    CategoryTheory.ShortComplex.mk i π hz
  let O : AlgebraicGeometry.VectorBundle C.toVariety :=
    (LineBundle.one C.toVariety).toVectorBundle
  let T : AlgebraicGeometry.VectorBundle C.toVariety := TangentBundle.pullback f
  letI : S.X₁.IsLocallyFree := by infer_instance
  letI : S.X₁.IsFiniteType := by infer_instance
  letI : S.X₃.IsLocallyFree :=
    (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback f (tangentBundle X).toModules).1
  letI : S.X₃.IsFiniteType :=
    AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback f (tangentBundle X).toModules
  have hS' : S.ShortExact := hS
  have hVlf : S.X₂.IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_shortExact hS'
  letI : S.X₂.IsLocallyFree := hVlf
  have hVft : S.X₂.IsFiniteType := by
    refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback S.X₂ fun x => ?_
    obtain ⟨U, hxU, σ, hσ⟩ := AlgebraicGeometry.Scheme.Modules.shortExact_locallySplit hS' x
    obtain ⟨U₁, I₁, hI₁, p₁, hx₁, hp₁⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType S.X₁ x
    obtain ⟨U₃, I₃, hI₃, p₃, hx₃, hp₃⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType S.X₃ x
    let W : C.toScheme.Opens := U ⊓ U₁ ⊓ U₃
    have hxW : x ∈ W := ⟨⟨hxU, hx₁⟩, hx₃⟩
    obtain ⟨σ', hσ'⟩ := extLF.section_of_le S.g
      (inf_le_left.trans inf_le_left : W ≤ U) σ hσ
    obtain ⟨p₁', hp₁'⟩ := AlgebraicGeometry.Scheme.Modules.epi_free_pullback_of_le S.X₁
      (inf_le_left.trans inf_le_right : W ≤ U₁) I₁ p₁ hp₁
    obtain ⟨p₃', hp₃'⟩ := AlgebraicGeometry.Scheme.Modules.epi_free_pullback_of_le S.X₃
      (inf_le_right : W ≤ U₃) I₃ p₃ hp₃
    have hSW := AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isOpenImmersion W.ι hS'
    let spl : (S.map (AlgebraicGeometry.Scheme.Modules.pullback W.ι)).Splitting :=
      CategoryTheory.ShortComplex.Splitting.ofExactOfSection _ hSW.exact σ' hσ' hSW.mono_f
    let G : WalkingPair → W.toScheme.Modules :=
      CategoryTheory.Limits.pairFunction
        ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj S.X₁)
        ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj S.X₃)
    let e₂ : (AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj S.X₂ ≅
        CategoryTheory.Limits.biproduct G :=
      spl.isoBinaryBiproduct ≪≫
        CategoryTheory.Limits.biproduct.uniqueUpToIso G
          ((CategoryTheory.Limits.BinaryBicone.toBiconeIsBilimit _).symm
            (CategoryTheory.Limits.BinaryBiproduct.isBilimit _ _))
    let I : WalkingPair → Type u := fun j =>
      WalkingPair.casesOn j I₁ I₃
    let J : WalkingPair → W.toScheme.Modules :=
      fun j => SheafOfModules.free (R := W.toScheme.ringCatSheaf) (I j)
    let hmap : ∀ j : WalkingPair, J j ⟶ G j := fun j =>
      WalkingPair.casesOn j p₁' p₃'
    let q : CategoryTheory.Limits.biproduct J ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj S.X₂ :=
      CategoryTheory.Limits.biproduct.map hmap ≫ e₂.inv
    letI : Epi p₁' := hp₁'
    letI : Epi p₃' := hp₃'
    have hmap_epi : Epi (CategoryTheory.Limits.biproduct.map hmap) :=
      @CategoryTheory.Limits.biproduct.map_epi _ _ _ _ J G _ _ hmap (fun j => by
        cases j
        · exact hp₁'
        · exact hp₃')
    have hq : Epi q := by
      dsimp [q]
      letI : Epi (CategoryTheory.Limits.biproduct.map hmap) := hmap_epi
      infer_instance
    letI : Fintype WalkingPair := inferInstance
    letI : Finite I₁ := hI₁
    letI : Finite I₃ := hI₃
    letI : Fintype I₁ := Fintype.ofFinite I₁
    letI : Fintype I₃ := Fintype.ofFinite I₃
    letI : ∀ j, Fintype (I j) := fun j => match j with
      | WalkingPair.left => inferInstance
      | WalkingPair.right => inferInstance
    let eSigma : (I WalkingPair.left ⊕ I WalkingPair.right) ≃ (Σ j, I j) :=
      { toFun := fun z => match z with
          | Sum.inl a => ⟨WalkingPair.left, a⟩
          | Sum.inr b => ⟨WalkingPair.right, b⟩
        invFun := fun z => match z with
          | ⟨WalkingPair.left, a⟩ => Sum.inl a
          | ⟨WalkingPair.right, b⟩ => Sum.inr b
        left_inv := by intro z; cases z <;> rfl
        right_inv := by intro z; cases z with
          | mk j a => cases j <;> rfl }
    letI : Finite (Σ j, I j) := Finite.of_equiv _ eSigma
    letI : Fintype (Σ j, I j) := Fintype.ofFinite (Σ j, I j)
    let eFree := biproductLF.freeSigmaIso (Y := W.toScheme) I
    refine ⟨W, Σ j, I j, inferInstanceAs (Finite (Σ j, I j)), eFree.inv ≫ q, hxW, ?_⟩
    letI : Epi eFree.inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv eFree)
    letI : Epi q := hq
    exact CategoryTheory.epi_comp' (f := eFree.inv) (g := q) (by infer_instance) hq
  let V : AlgebraicGeometry.VectorBundle C.toVariety :=
    { toModules := S.X₂
      rank := X.toVariety.dim + 1
      locallyFree := hVlf
      isFiniteType := hVft
      rankAtStalk_eq := by
        intro x
        rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_add_of_shortExact hS' x]
        have h1 : AlgebraicGeometry.Scheme.Modules.rankAtStalk S.X₁ x = 1 := by
          simpa [S, O, LineBundle.one, LineBundle.ofModules, LineBundle.one_toModules] using
            (O.rankAtStalk_eq x)
        have h3 : AlgebraicGeometry.Scheme.Modules.rankAtStalk S.X₃ x = X.toVariety.dim := by
          simpa [S, T, TangentBundle.pullback, AlgebraicGeometry.VectorBundle.pullback,
            tangentBundle_rank]
            using (T.rankAtStalk_eq x)
        omega }
  have hdeg := VectorBundle.degree_add_of_shortExact hS' O V T
    (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
  refine ⟨V, ⟨⟨CategoryTheory.Iso.refl _⟩, rfl, ?_⟩⟩
  calc
    VectorBundle.degree V = VectorBundle.degree O + VectorBundle.degree T := hdeg
    _ = 0 + VectorBundle.degree T := by rw [lineBundle_vector_degree, LineBundle.degree_one]
    _ = TangentBundle.pullbackDegree f := by simpa [T, TangentBundle.pullbackDegree]

end
