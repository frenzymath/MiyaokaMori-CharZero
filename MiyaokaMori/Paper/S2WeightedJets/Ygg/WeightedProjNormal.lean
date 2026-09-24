import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.LocallyIntegralConnectedIntegral
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPartFiniteType
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalIsLocal
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjVeroneseIso
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphismComp
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.RelativeDimensionAdd
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.RelativeProjLocallyWeightedDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGeneration
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseSubalgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjSpaceDimension
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjSpaceIntegral
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjChartProdNormal
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjSpaceNormal
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurveIntegral
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverIffProjectiveMorphism

/-! # `Y_k^GG` is integral, normal and projective

The weighted projectivization `Y_k^GG` is integral, normal and projective over `C` (hence
projective over `k`), of dimension `s_k = (n+1)k`: locally over `C` it is a product with the
weighted projective space `ℙ(1^{n+1}, …, k^{n+1})`, which is integral and normal
(Lemma 2.2 of the paper; Dolgachev, *Weighted projective varieties*,
Proposition 1.3.3(i)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem normal_of_iso {X Y : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y)
    (hX : X.IsNormal) : Y.IsNormal := by
  constructor
  · intro y
    let x : X := e.inv.base y
    let ε : X.presheaf.stalk x ≃+* Y.presheaf.stalk y :=
      (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
    letI : IsDomain (X.presheaf.stalk x) := hX.isDomain x
    exact ε.symm.toMulEquiv.isDomain _
  · intro y
    let x : X := e.inv.base y
    let ε : X.presheaf.stalk x ≃+* Y.presheaf.stalk y :=
      (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
    letI : IsIntegrallyClosed (X.presheaf.stalk x) := hX.integrallyClosed x
    exact IsIntegrallyClosed.of_equiv ε

private theorem finite_weightedMonomials {σ : Type u} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (m : ℕ) :
    Finite (weightedMonomials w m) := by
  exact (Finsupp.finite_of_nat_weight_eq w (fun i => Nat.ne_of_gt (hw i)) m).to_subtype

private theorem local_part_isFiniteType_veronese {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {σ : Type u} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) (m : ℕ) :
    ((S.veronese m).part 1).IsFiniteType := by
  simpa [AlgebraicGeometry.Scheme.GradedQCAlgebra.veronese] using
    (locallyWeighted_part_isFiniteType S w hw
      (by
        simpa [AlgebraicGeometry.Scheme.GradedQCAlgebra.IsLocallyWeightedPolynomial] using hS) m)

theorem ykGG_integral_normal_projective {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {C : SmoothProjectiveCurve k} (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom]
    (sec : C.toScheme ⟶ Z.left) (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _)
    (n r : ℕ) (hr : 1 ≤ r)
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _)) :
    AlgebraicGeometry.IsIntegral (weightedJetProjectivization (k := k) Z sec hs r).left ∧
      (weightedJetProjectivization (k := k) Z sec hs r).left.IsNormal ∧
      AlgebraicGeometry.IsProjectiveMorphism (weightedJetProjectivization (k := k) Z sec hs r).hom ∧
      AlgebraicGeometry.IsProjectiveMorphism ((weightedJetProjectivization (k := k) Z sec hs r).hom ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ∧
      (weightedJetProjectivization (k := k) Z sec hs r).left.dimension = (n + 1) * r := by
  let S := (jetGradedAlgebra (k := k) Z sec hs r).1
  let Y := weightedJetProjectivization (k := k) Z sec hs r
  let σ := ULift.{u} (Fin (n + 1) × Fin r)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  let pC : C.toScheme ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  letI : Fintype σ := inferInstance
  letI : Nonempty σ := ⟨ULift.up ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
  have hw : ∀ i, 0 < w i := by intro i; simp [w]
  have hS : S.IsLocallyWeightedPolynomial w hw := by simpa [S, w] using hloc
  have hCint : AlgebraicGeometry.IsIntegral C.toScheme :=
    SmoothProjectiveCurve.isIntegral_of_smooth_connected C
  letI : AlgebraicGeometry.IsIntegral C.toScheme := hCint
  letI : IrreducibleSpace C.toScheme :=
    AlgebraicGeometry.irreducibleSpace_of_isIntegral C.toScheme
  letI : AlgebraicGeometry.Smooth pC := by
    simpa [pC, IsSmoothOver] using C.smooth
  obtain ⟨𝒰, h𝒰⟩ := relativeProj_locallyWeighted_localProduct pC S w hw hS
  letI : GradedRing
      (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
        (fun i : σ => (⟨w i, hw i⟩ : ℕ+))) :=
    MvPolynomial.weightedGradedAlgebra
      (R := k) (w := fun i : σ => w i)
  have hFirr : IrreducibleSpace (weightedProjectiveSpace k w hw) := by
    change IrreducibleSpace
      (AlgebraicGeometry.Proj
        (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
          (fun i : σ => (⟨w i, hw i⟩ : ℕ+))))
    apply AlgebraicGeometry.Proj.irreducibleSpace_of_isDomain
    let i : σ := Classical.choice (inferInstance : Nonempty σ)
    refine ⟨w i, MvPolynomial.X i, ?_, ?_, ?_⟩
    · exact hw i
    · exact (MvPolynomial.mem_weightedHomogeneousSubmodule k _ _ _).mpr
        (MvPolynomial.isWeightedHomogeneous_X k
          (fun j => (w j : ℕ)) i)
    · exact MvPolynomial.X_ne_zero i
  letI : IrreducibleSpace (weightedProjectiveSpace k w hw) := hFirr
  let 𝒲 : C.toScheme.OpenCover.{u} :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers
      (C.toScheme) (fun x => 𝒰.X (𝒰.idx x)) (fun x => 𝒰.f (𝒰.idx x))
      (by
        intro x
        obtain ⟨y, hy⟩ := 𝒰.covers x
        exact ⟨x, y, hy⟩)
      (fun x => 𝒰.map_prop (𝒰.idx x))
  have hInt : AlgebraicGeometry.IsIntegral Y.left := by
    apply isIntegral_of_locally_product_over_irreducible pC
      (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) Y.hom 𝒲
    · intro i
      change C.toScheme at i
      obtain ⟨φ, hφ, _⟩ := h𝒰 (𝒰.idx i)
      exact ⟨φ, hφ⟩
    · intro i
      letI : AlgebraicGeometry.IsOpenImmersion (𝒲.f i) := 𝒲.map_prop i
      letI : Nonempty (𝒲.X i) := by
        change Nonempty (𝒰.X (𝒰.idx i))
        obtain ⟨y, hy⟩ := 𝒰.covers i
        exact ⟨y⟩
      letI : AlgebraicGeometry.IsIntegral (𝒲.X i) :=
        AlgebraicGeometry.isIntegral_of_isOpenImmersion (𝒲.f i)
      letI : AlgebraicGeometry.Smooth (𝒲.f i ≫ pC) := inferInstance
      -- Normality of `U_i` is supplied explicitly: it is smooth over a field of dimension `≤ 1`.
      letI : (𝒲.X i).IsNormal :=
        AlgebraicGeometry.Smooth.isNormal_of_field_of_dim_le_one (𝒲.f i ≫ pC)
          (le_trans (𝒲.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le
            (le_of_eq C.dim_one))
      apply weightedProjectiveSpace_prod_isIntegral k w hw (𝒲.X i) (𝒲.f i ≫ pC)
  have hNorm : Y.left.IsNormal := by
    let 𝒱 : Y.left.OpenCover.{u} := 𝒰.pullback₁ Y.hom
    apply isNormal_of_openCover 𝒱
    intro i
    obtain ⟨φ, hφ, _⟩ := h𝒰 i
    letI : AlgebraicGeometry.IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    letI : AlgebraicGeometry.Smooth (𝒰.f i ≫ pC) := inferInstance
    have hdimU : topologicalKrullDim (𝒰.X i) ≤ 1 :=
      le_trans (𝒰.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le (le_of_eq C.dim_one)
    -- `U_i` must be integral and normal; it may be empty, so first reduce to the nonempty case.
    have hp : (CategoryTheory.Limits.pullback (𝒰.f i ≫ pC)
        (weightedProjectiveSpace k w hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of k))).IsNormal := by
      apply AlgebraicGeometry.Scheme.isNormal_of_nonempty_imp
      intro hne
      letI : Nonempty (𝒰.X i) :=
        ⟨(CategoryTheory.Limits.pullback.fst (𝒰.f i ≫ pC)
          (weightedProjectiveSpace k w hw ↘
            AlgebraicGeometry.Spec (CommRingCat.of k))).base hne.some⟩
      letI : AlgebraicGeometry.IsIntegral (𝒰.X i) :=
        @AlgebraicGeometry.isIntegral_of_isOpenImmersion _ _ (𝒰.f i) (𝒰.map_prop i)
          inferInstance inferInstance
      letI : (𝒰.X i).IsNormal :=
        AlgebraicGeometry.Smooth.isNormal_of_field_of_dim_le_one (𝒰.f i ≫ pC) hdimU
      exact weightedProjectiveSpace_prod_isNormal k w hw (𝒰.X i) (𝒰.f i ≫ pC)
    exact normal_of_iso φ.symm hp
  let m : ℕ := Fintype.card σ * jetWeight r
  have hm : 0 < m := by
    dsimp [m]
    have hjet : 0 < jetWeight r := by
      rw [jetWeight]
      apply Nat.pos_of_ne_zero
      rw [Finset.lcm_ne_zero_iff]
      intro x hx
      exact Nat.ne_of_gt (Finset.mem_Icc.mp hx).1
    exact Nat.mul_pos Fintype.card_pos hjet
  have hwm : ∀ i, w i ∈ Finset.Icc 1 r := by
    intro i
    simp [w]
  have hgen := veronese_generation S w hwm hS
  have hft : ((S.veronese m).part 1).IsFiniteType :=
    local_part_isFiniteType_veronese S w hw hS m
  have hprojC : AlgebraicGeometry.IsProjectiveMorphism Y.hom := by
    let e := AlgebraicGeometry.Scheme.relativeProj.veroneseIso S m hm
    have hi : AlgebraicGeometry.IsClosedImmersion e.inv.left := by
      have hleft : e.inv.left ≫ e.hom.left = 𝟙 _ :=
        congrArg CategoryTheory.Over.Hom.left e.inv_hom_id
      have hcomp : AlgebraicGeometry.IsClosedImmersion (e.inv.left ≫ e.hom.left) := by
        rw [hleft]
        infer_instance
      exact AlgebraicGeometry.IsClosedImmersion.of_comp e.inv.left e.hom.left
    have hover : e.inv.left ≫ (AlgebraicGeometry.Scheme.relativeProj (S.veronese m)).hom = Y.hom :=
      CategoryTheory.Over.w e.inv
    refine ⟨(S.veronese m), e.inv.left, hgen.2, hft, hi, ?_⟩
    exact hover
  have hprojK : AlgebraicGeometry.IsProjectiveMorphism (Y.hom ≫ pC) := by
    letI : AlgebraicGeometry.IsProjectiveMorphism Y.hom := hprojC
    letI : AlgebraicGeometry.IsProjectiveMorphism pC :=
      (isProjectiveOver_iff_isProjectiveMorphism k C.toScheme).mp C.projective
    exact IsProjectiveMorphism.comp Y.hom pC
  have hdim : Y.left.dimension = (n + 1) * r := by
    have hkr := relativeProj_locallyWeighted_krullDim pC S w hw hS
    unfold AlgebraicGeometry.Scheme.dimension
    rw [hkr, C.dim_one]
    have hcard : Fintype.card σ = (n + 1) * r := by simp [σ]
    have hprod : 1 ≤ (n + 1) * r := by
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero n) (Nat.ne_of_gt hr))
    have hNat : 1 + ((n + 1) * r - 1) = (n + 1) * r := by omega
    have hCast : (1 : WithBot ℕ∞) + ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) =
        (((n + 1) * r : ℕ) : WithBot ℕ∞) := by
      rw [hcard]
      exact_mod_cast hNat
    rw [hCast]
    change (((n + 1) * r : ℕ) : ℕ∞).toNat = (n + 1) * r
    simp
  exact ⟨hInt, hNorm, hprojC, hprojK, hdim⟩

end
