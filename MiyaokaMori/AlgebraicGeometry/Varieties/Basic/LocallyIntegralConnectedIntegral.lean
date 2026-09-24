import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Stacks020j

/-! # A scheme which is locally a product over an irreducible base is integral

Let `π : X → C` with `C` irreducible, and suppose that locally on `C` one has
`π⁻¹(Uᵢ) ≅ Uᵢ ×_k F` with `F` irreducible over the algebraically closed field `k`, these local
products being integral. Then `X` is integral. (This is the step "the local products are
integral and `C` is connected, hence `Y_k^GG` is integral" of the paper.) The argument makes
explicit the step the paper omits: since `π` is locally a product projection (an open map) with
irreducible fibres, `X` is irreducible, in particular connected.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem isIntegral_of_locally_product_over_irreducible {k : Type u} [Field k] [IsAlgClosed k]
    {X C F : AlgebraicGeometry.Scheme.{u}}
    (pC : C ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (pF : F ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [IrreducibleSpace C] [IrreducibleSpace F]
    (π : X ⟶ C) (𝒰 : C.OpenCover)
    (e : ∀ i, ∃ φ : CategoryTheory.Limits.pullback π (𝒰.f i) ≅
        CategoryTheory.Limits.pullback (𝒰.f i ≫ pC) pF,
        φ.hom ≫ CategoryTheory.Limits.pullback.fst (𝒰.f i ≫ pC) pF =
          CategoryTheory.Limits.pullback.snd π (𝒰.f i))
    (hint : ∀ i, AlgebraicGeometry.IsIntegral
        (CategoryTheory.Limits.pullback (𝒰.f i ≫ pC) pF)) :
    AlgebraicGeometry.IsIntegral X := by
  let 𝒱 : X.OpenCover :=
    { I₀ := 𝒰.I₀
      X := fun i => CategoryTheory.Limits.pullback π (𝒰.f i)
      f := fun i => CategoryTheory.Limits.pullback.fst π (𝒰.f i)
      mem₀ := by
        rw [AlgebraicGeometry.Scheme.presieve₀_mem_precoverage_iff]
        constructor
        · intro x
          obtain ⟨i, y, hy⟩ := AlgebraicGeometry.Scheme.Cover.exists_eq
            (𝒰.pullback₁ π) x
          exact ⟨i, y, hy⟩
        · intro i
          infer_instance }
  have hlocal_lift (i : 𝒰.I₀) (y : 𝒰.X i) :
      ∃ z : 𝒱.X i, (π.base ((𝒱.f i).base z)) = (𝒰.f i).base y := by
    obtain ⟨φ, hφ⟩ := e i
    let f₀ : F := Classical.choice (inferInstance : Nonempty F)
    have hbase : (𝒰.f i ≫ pC).base y = pF.base f₀ := Subsingleton.elim _ _
    obtain ⟨q, hq₁, hq₂⟩ :=
      AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback y f₀ hbase
    let z : 𝒱.X i := φ.inv q
    refine ⟨z, ?_⟩
    have hsnd : (pullback.snd π (𝒰.f i)).base z = y := by
      rw [← hφ]
      simp only [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
      simpa [z] using hq₁
    have hcond := congrArg (fun g : 𝒱.X i ⟶ C => g.base z)
      (CategoryTheory.Limits.pullback.condition (f := π) (g := 𝒰.f i))
    change π.base ((pullback.fst π (𝒰.f i)).base z) = (𝒰.f i).base y
    simpa only [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
      hsnd] using hcond
  letI : AlgebraicGeometry.IsReduced X := by
    letI : ∀ i, AlgebraicGeometry.IsReduced (𝒱.X i) := fun i => by
      obtain ⟨φ, _⟩ := e i
      have hInt : AlgebraicGeometry.IsIntegral (𝒱.X i) := by
        letI : AlgebraicGeometry.IsIntegral
            (CategoryTheory.Limits.pullback (𝒰.f i ≫ pC) pF) := hint i
        exact AlgebraicGeometry.IsIntegral.of_isIso φ.inv
      letI : AlgebraicGeometry.IsIntegral (𝒱.X i) := hInt
      infer_instance
    exact AlgebraicGeometry.IsReduced.of_openCover X 𝒱
  letI : IrreducibleSpace X := by
    letI : ∀ i, IrreducibleSpace (𝒱.X i) := fun i => by
      obtain ⟨φ, _⟩ := e i
      letI : AlgebraicGeometry.IsIntegral
          (CategoryTheory.Limits.pullback (𝒰.f i ≫ pC) pF) := hint i
      letI : AlgebraicGeometry.IsIntegral (𝒱.X i) :=
        AlgebraicGeometry.IsIntegral.of_isIso φ.inv
      exact AlgebraicGeometry.irreducibleSpace_of_isIntegral (𝒱.X i)
    haveI : PreirreducibleSpace X := by
      apply PreirreducibleSpace.of_isOpenCover
        (U := fun i => (𝒱.f i).opensRange)
      · intro i j hij
        intro hd
        have hbase_i : ((𝒰.f i).opensRange : Set C).Nonempty := by
          letI : Nonempty (𝒱.X i) := (inferInstance : IrreducibleSpace (𝒱.X i)).toNonempty
          let z : 𝒱.X i := Classical.choice (inferInstance : Nonempty (𝒱.X i))
          exact ⟨π.base ((𝒱.f i).base z), ⟨(pullback.snd π (𝒰.f i)).base z, by
            have hcond := congrArg (fun g : 𝒱.X i ⟶ C => g.base z)
              (CategoryTheory.Limits.pullback.condition (f := π) (g := 𝒰.f i))
            change (𝒰.f i).base ((pullback.snd π (𝒰.f i)).base z) =
              π.base ((pullback.fst π (𝒰.f i)).base z)
            simpa only [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp,
              Function.comp_apply] using hcond.symm⟩⟩
        have hbase_j : ((𝒰.f j).opensRange : Set C).Nonempty := by
          letI : Nonempty (𝒱.X j) := (inferInstance : IrreducibleSpace (𝒱.X j)).toNonempty
          let z : 𝒱.X j := Classical.choice (inferInstance : Nonempty (𝒱.X j))
          exact ⟨π.base ((𝒱.f j).base z), ⟨(pullback.snd π (𝒰.f j)).base z, by
            have hcond := congrArg (fun g : 𝒱.X j ⟶ C => g.base z)
              (CategoryTheory.Limits.pullback.condition (f := π) (g := 𝒰.f j))
            change (𝒰.f j).base ((pullback.snd π (𝒰.f j)).base z) =
              π.base ((pullback.fst π (𝒰.f j)).base z)
            simpa only [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp,
              Function.comp_apply] using hcond.symm⟩⟩
        obtain ⟨c, hci, hcj⟩ := nonempty_preirreducible_inter
          (𝒰.f i).isOpenEmbedding.isOpen_range (𝒰.f j).isOpenEmbedding.isOpen_range
            hbase_i hbase_j
        change c ∈ Set.range (𝒰.f i).base at hci
        change c ∈ Set.range (𝒰.f j).base at hcj
        obtain ⟨yi, hyi⟩ := hci
        obtain ⟨yj, hyj⟩ := hcj
        obtain ⟨z, hz⟩ := hlocal_lift i yi
        have hz_i : (𝒱.f i) z ∈ (𝒱.f i).opensRange := ⟨z, rfl⟩
        have hz_j : (𝒱.f i) z ∈ (𝒱.f j).opensRange := by
          have hπz : π.base ((𝒱.f i).base z) = (𝒰.f j).base yj :=
            hz.trans (hyi.trans hyj.symm)
          obtain ⟨w, hw₁, hw₂⟩ :=
            AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
              ((𝒱.f i).base z) yj hπz
          exact ⟨w, hw₁⟩
        have hmem : (𝒱.f i) z ∈ (𝒱.f i).opensRange ⊓ (𝒱.f j).opensRange :=
          ⟨hz_i, hz_j⟩
        have hbot : (𝒱.f i).opensRange ⊓ (𝒱.f j).opensRange = (⊥ : X.Opens) :=
          disjoint_iff.mp hd
        have hzero : (𝒱.f i) z ∈ (⊥ : X.Opens) := by
          rw [← hbot]
          exact hmem
        simpa using hzero
      · exact 𝒱.isOpenCover_opensRange
      · intro i
        have hi : IsPreirreducible (Set.range (𝒱.f i).base) := by
          simpa only [Set.image_univ] using
            (PreirreducibleSpace.isPreirreducible_univ (X := 𝒱.X i)).image
              (𝒱.f i).base (𝒱.f i).continuous.continuousOn
        apply isPreirreducible_iff_preirreducibleSpace.mp
        simpa only [AlgebraicGeometry.Scheme.Hom.coe_opensRange] using hi
    refine { toPreirreducibleSpace := inferInstance, toNonempty := ?_ }
    let i := 𝒰.idx (Classical.choice (inferInstance : Nonempty C))
    exact ⟨(𝒱.f i) (Classical.choice (inferInstance : Nonempty (𝒱.X i)))⟩
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced X

end
