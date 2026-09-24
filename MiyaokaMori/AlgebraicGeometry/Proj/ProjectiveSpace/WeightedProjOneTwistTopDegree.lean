import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjBundleFiberDegreeOne
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceGradedRingIsos
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIso
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoProjTwistZero
import MiyaokaMori.AlgebraicGeometry.Chow.NormalizedFirstChernClassIndep
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceDimension

/-! # Top self-intersection of `O(m)` on `P(1,…,1)`

On `P^N = P(1,…,1)` (`|σ| = N + 1` coordinates, all of weight `1`) we have `(O(m)^N) = m^N`.

References: Hartshorne II.6; Fulton, Example 2.5.1 (`c_1(O(1))^N ∩ [P^N]` is one point); the fiber
degree of the polarization in Lemma 2.2 of the paper.

## Route

The top-level theorem `weightedProjectiveSpace_one_topSelfIntersection` is assembled from:

1. `firstChernClass_twist_natCast`: on an absolute `Proj 𝒜` with `𝒜` generated in degree one,
   `c_1(O(m)) = m·c_1(O(1))`. Induction on `m`: `O(0) ≅ O` (`Proj.isIso_unitToTwistZero`) and
   `c_1(O) = 0` (`firstChernClass_one`); `O(a) ⊗ O(1) ≅ O(a+1)` (the multiplication `Proj.twistMul` is an
   isomorphism, `Proj.twistMul_isIso_of_generatedInDegree`, Stacks 01MS), and `c_1` is additive on tensor
   products (`firstChernClass_tensor_any`).
2. `topSelfIntersection_of_firstChernClass_nsmul`: `c_1(L) = m·c_1(L')` implies `(L^d) = m^d (L'^d)`
   (`capPow` is the iterated cap with `c_1`; pull out one `m` per level; the degree map is additive).
3. `weightedProjectiveSpace_one_iso_projectiveSpace_twist`: a `k`-isomorphism
   `ι : P(1,…,1)_σ ≅ ProjectiveSpace N k` (`Proj.isoOfGradedRingEquiv` along
   `MvPolynomial.renameEquiv k (σ ≃ Fin (N+1))`; compatibility with the structure morphisms by
   `Proj.isoOfGradedRingEquiv_hom_toSpecZero`, Stacks 01MX), with `O(1) ≅ ι^*O(1)` (the comparison map
   `θ = Proj.twistPullbackHom` of Stacks 01MX is an isomorphism for a graded ring isomorphism,
   `Proj.isIso_twistPullbackHom_of_bijective`).
4. The top self-intersection is invariant under `k`-isomorphisms (`topSelfIntersection_eq_of_iso_over`),
   `(O_{P^N}(1)^N) = 1` (`projectiveSpace_top_selfIntersection_one`), and `dim P(1,…,1) = N`
   (`weightedProjectiveSpace_one_dimension`).

Edge cases: for `N = 0` (`σ` a singleton) `P^0 = Spec k` and both sides are `1`; for `m = 0` and
`N > 0`, `c_1(O(0)) = 0` and both sides are `0`. The arguments `[IsAlgClosed k]` and `[IsLineBundle]`
only match the statement as used downstream: the proof does not use `IsAlgClosed`, and the line-bundle
property follows for all `m` from `weightedProjTwist_one_isLineBundle`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace WeightedProjOneTwistTopDegree

/-! ## (2) `capPow` and multiples of `c_1` -/

/-- If `c_1(L) = m·c_1(L')` (in every dimension), then the `n`-fold iterated caps with `c_1` differ by
`m^n`: `capPow L n d = m^n • capPow L' n d`. Induction on `n`: `capPow (n+1)` is the composite of
`capPow n` with `c_1`, and each level pulls out one `m` through `map_nsmul`. -/
theorem capPow_nsmul_of_firstChernClass_nsmul {X : AlgebraicGeometry.Scheme.{u}}
    (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (m : ℕ)
    (h : ∀ d : ℕ, AlgebraicGeometry.firstChernClass L (d + 1) =
      m • AlgebraicGeometry.firstChernClass L' (d + 1)) :
    ∀ (n d : ℕ), AlgebraicGeometry.firstChernClass.capPow L n d =
      m ^ n • AlgebraicGeometry.firstChernClass.capPow L' n d
  | 0, _ => by simp [AlgebraicGeometry.firstChernClass.capPow]
  | n + 1, d => by
    show (AlgebraicGeometry.firstChernClass.capPow L n d).comp
        (AlgebraicGeometry.firstChernClass L (d + n + 1)) =
      m ^ (n + 1) • (AlgebraicGeometry.firstChernClass.capPow L' n d).comp
        (AlgebraicGeometry.firstChernClass L' (d + n + 1))
    rw [capPow_nsmul_of_firstChernClass_nsmul L L' m h n d, h (d + n)]
    ext x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, map_nsmul, pow_succ, mul_nsmul]

/-- `c_1(L) = m·c_1(L')` implies `(L^d) = m^d·(L'^d)` for the top self-intersection, `d = dim X`. -/
theorem topSelfIntersection_of_firstChernClass_nsmul {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (m : ℕ)
    (h : ∀ d : ℕ, AlgebraicGeometry.firstChernClass L (d + 1) =
      m • AlgebraicGeometry.firstChernClass L' (d + 1)) :
    AlgebraicGeometry.topSelfIntersection X hX L =
      (m : ℤ) ^ X.dimension * AlgebraicGeometry.topSelfIntersection X hX L' := by
  unfold AlgebraicGeometry.topSelfIntersection
  rw [capPow_nsmul_of_firstChernClass_nsmul L L' m h, AddMonoidHom.nsmul_apply, map_nsmul]
  simp

/-! ## (1) `c_1(O(m)) = m·c_1(O(1))` on an absolute `Proj` -/

section Proj

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- `c_1(O(0)) = 0`: `O(0) ≅ O_{Proj 𝒜}` (`Proj.isIso_unitToTwistZero`) and `c_1(O) = 0` (`firstChernClass_one`). -/
theorem firstChernClass_twist_zero [(AlgebraicGeometry.Proj.twist 𝒜 0).IsLineBundle] (d : ℕ) :
    AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Proj.twist 𝒜 0) (d + 1) = 0 := by
  have := AlgebraicGeometry.Proj.isIso_unitToTwistZero 𝒜
  have : (𝟙_ (AlgebraicGeometry.Proj 𝒜).Modules).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso
      (asIso (AlgebraicGeometry.Proj.unitToTwistZero 𝒜)).symm
  rw [← AlgebraicGeometry.firstChernClass_congr _ _ (asIso (AlgebraicGeometry.Proj.unitToTwistZero 𝒜)) d]
  exact AlgebraicGeometry.firstChernClass_one _ d

/-- If `𝒜` is generated in degree one, `c_1(O(a+1)) = c_1(O(a)) + c_1(O(1))`: the multiplication
`O(a) ⊗ O(1) → O(a+1)` is an isomorphism (`Proj.twistMul_isIso_of_generatedInDegree`, Stacks 01MS), and
`c_1` is additive on tensor products (`firstChernClass_tensor_any`). -/
theorem firstChernClass_twist_succ
    (hgen : ∀ (k : ℕ) (a : A), a ∈ 𝒜 (1 * k) → a ∈ Subring.closure ((𝒜 0 : Set A) ∪ (𝒜 1 : Set A)))
    [∀ m : ℤ, (AlgebraicGeometry.Proj.twist 𝒜 m).IsLineBundle] (a : ℤ) (d : ℕ) :
    AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Proj.twist 𝒜 (a + 1)) (d + 1) =
      AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Proj.twist 𝒜 a) (d + 1) +
        AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Proj.twist 𝒜 1) (d + 1) := by
  have := AlgebraicGeometry.Proj.twistMul_isIso_of_generatedInDegree 𝒜 1 Nat.one_pos hgen a 1 (one_dvd _)
  have : (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Proj.twist 𝒜 a)
      (AlgebraicGeometry.Proj.twist 𝒜 1)).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso (asIso (AlgebraicGeometry.Proj.twistMul 𝒜 a 1)).symm
  rw [← AlgebraicGeometry.firstChernClass_congr _ _ (asIso (AlgebraicGeometry.Proj.twistMul 𝒜 a 1)) d,
    AlgebraicGeometry.firstChernClass_tensor_any]

/-- If `𝒜` is generated in degree one, `c_1(O(m)) = m·c_1(O(1))` for `m : ℕ`, by induction on `m`. -/
theorem firstChernClass_twist_natCast
    (hgen : ∀ (k : ℕ) (a : A), a ∈ 𝒜 (1 * k) → a ∈ Subring.closure ((𝒜 0 : Set A) ∪ (𝒜 1 : Set A)))
    [∀ m : ℤ, (AlgebraicGeometry.Proj.twist 𝒜 m).IsLineBundle] (m : ℕ) (d : ℕ) :
    AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Proj.twist 𝒜 (m : ℤ)) (d + 1) =
      m • AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Proj.twist 𝒜 1) (d + 1) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, firstChernClass_twist_zero 𝒜 d, zero_smul]
  | succ m ih =>
    rw [Nat.cast_succ, firstChernClass_twist_succ 𝒜 hgen (m : ℤ) d, ih, succ_nsmul]

end Proj

/-! ## (3) The concrete data of `P(1,…,1)_σ` -/

/-- The standard grading of `k[x_σ]` is generated in degree one: every polynomial lies in the subring
generated by the constants and the variables (`MvPolynomial.induction_on`). -/
theorem weightedPolynomialGrading_one_generated (k : Type u) [Field k] {σ : Type u} (n : ℕ)
    (a : MvPolynomial σ k)
    (_ha : a ∈ MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun _ : σ => (1 : ℕ+)) (1 * n)) :
    a ∈ Subring.closure
      ((MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun _ : σ => (1 : ℕ+)) 0 : Set (MvPolynomial σ k)) ∪
        (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun _ : σ => (1 : ℕ+)) 1 : Set (MvPolynomial σ k))) := by
  clear _ha
  induction a using MvPolynomial.induction_on with
  | C r =>
    apply Subring.subset_closure
    exact Or.inl (MvPolynomial.isWeightedHomogeneous_C _ r)
  | add p q hp hq => exact Subring.add_mem _ hp hq
  | mul_X p i hp =>
    refine Subring.mul_mem _ hp (Subring.subset_closure (Or.inr ?_))
    exact MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => ((1 : ℕ+) : ℕ)) i

/-- Every `O(m)` on `P(1,…,1)` is a line bundle: the coordinates `x_i` are homogeneous of degree one and
the `D_+(x_i)` cover (`weightedCoordinateOpen_iSup`); apply `Proj.twist_isLineBundle`. -/
theorem weightedProjTwist_one_isLineBundle (k : Type u) [Field k] {σ : Type u} (m : ℤ) :
    (weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) m).IsLineBundle :=
  AlgebraicGeometry.Proj.twist_isLineBundle
    (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun _ : σ => (1 : ℕ+)))
    (fun i : σ => MvPolynomial.X i)
    (fun i => MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => ((1 : ℕ+) : ℕ)) i)
    (MiyaokaMori.WeightedJets.weightedCoordinateOpen_iSup k (fun _ : σ => (1 : ℕ+))) m

/-- `P(1,…,1)` (coordinates `σ`) is `k`-isomorphic to `P^N` (`N = |σ| − 1`), with `O(1) ≅ ι^*O(1)`.
The isomorphism is `Proj.isoOfGradedRingEquiv` along `renameEquiv k (σ ≃ Fin (N+1))` (the weight-one
grading is the standard grading, and `rename` preserves homogeneity:
`IsHomogeneous.rename_isHomogeneous_iff`); compatibility with the structure morphisms is
`isoOfGradedRingEquiv_hom_toSpecZero` plus the fact that `rename` fixes constants; `O(1)` is transported
by the comparison map `θ` of Stacks 01MX (`Proj.twistPullbackHom`), an isomorphism for a bijective graded
homomorphism (`Proj.isIso_twistPullbackHom_of_bijective`). -/
theorem weightedProjectiveSpace_one_iso_projectiveSpace_twist (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [Nonempty σ] :
    ∃ e : weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ≅
        ProjectiveSpace (Fintype.card σ - 1) k,
      e.hom ≫ (ProjectiveSpace (Fintype.card σ - 1) k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      Nonempty (weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) 1 ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          (projectiveSpaceTwist k (Fintype.card σ - 1) 1)) := by
  classical
  have hcardpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr inferInstance
  have hcard : Fintype.card σ - 1 + 1 = Fintype.card σ := by omega
  let eσ : σ ≃ Fin (Fintype.card σ - 1 + 1) := (Fintype.equivFin σ).trans (finCongr hcard.symm)
  let ε : MvPolynomial σ k ≃+* MvPolynomial (Fin (Fintype.card σ - 1 + 1)) k :=
    (MvPolynomial.renameEquiv k eσ).toRingEquiv
  have hε : ∀ i (a : MvPolynomial σ k),
      a ∈ MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun _ : σ => (⟨1, Nat.one_pos⟩ : ℕ+)) i ↔
        ε a ∈ AlgebraicGeometry.Proj.projectiveGrading k (Fintype.card σ - 1) i := by
    intro i a
    change MvPolynomial.IsWeightedHomogeneous _ a i ↔
      MvPolynomial.IsHomogeneous (MvPolynomial.rename eσ a) i
    rw [MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff eσ.injective]
    rfl
  refine ⟨AlgebraicGeometry.Proj.isoOfGradedRingEquiv ε hε, ?_, ?_⟩
  · change (AlgebraicGeometry.Proj.isoOfGradedRingEquiv ε hε).hom ≫
        (AlgebraicGeometry.Proj.toSpecZero _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k _))) =
      AlgebraicGeometry.Proj.toSpecZero _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k _))
    rw [← CategoryTheory.Category.assoc, AlgebraicGeometry.Proj.isoOfGradedRingEquiv_hom_toSpecZero,
      CategoryTheory.Category.assoc, ← AlgebraicGeometry.Spec.map_comp]
    congr 2
    ext c
    simp [AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm, ε]
  · have := AlgebraicGeometry.Proj.isIso_twistPullbackHom_of_bijective
      (AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm ε hε)
      (AlgebraicGeometry.Proj.irrelevant_le_map_gradedRingHomOfRingEquivSymm ε hε)
      ε.symm.bijective 1
    exact ⟨(asIso (AlgebraicGeometry.Proj.twistPullbackHom
      (AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm ε hε)
      (AlgebraicGeometry.Proj.irrelevant_le_map_gradedRingHomOfRingEquivSymm ε hε) 1)).symm⟩

/-- `dim P(1,…,1) = |σ| − 1` (the `ℕ`-valued version of `weightedProjectiveSpace_one_dimension`). -/
theorem weightedProjectiveSpace_one_dimension_nat (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    [Nonempty σ] :
    (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos)).dimension = Fintype.card σ - 1 := by
  unfold AlgebraicGeometry.Scheme.dimension
  rw [weightedProjectiveSpace_one_dimension k]
  exact ENat.toNat_natCast _

end WeightedProjOneTwistTopDegree

/-! ## The top-level theorem -/

open WeightedProjOneTwistTopDegree in
/-- On `P(1,…,1)` we have `(O(m)^N) = m^N`, `N = |σ| − 1`. See the route in the module docstring. -/
theorem weightedProjectiveSpace_one_topSelfIntersection (k : Type u) [Field k] [IsAlgClosed k]
    {σ : Type u} [Fintype σ] [Nonempty σ] (m : ℕ)
    (hP : IsProperOver k (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos)))
    [(weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) (m : ℤ)).IsLineBundle] :
    AlgebraicGeometry.topSelfIntersection
        (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos)) hP
        (weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) (m : ℤ))
      = (m : ℤ) ^ (Fintype.card σ - 1) := by
  classical
  have hLB : ∀ n : ℤ, (AlgebraicGeometry.Proj.twist
      (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun _ : σ => (1 : ℕ+))) n).IsLineBundle :=
    fun n => weightedProjTwist_one_isLineBundle k n
  have : (weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) 1).IsLineBundle :=
    weightedProjTwist_one_isLineBundle k 1
  have hc1 : ∀ d : ℕ, AlgebraicGeometry.firstChernClass
      (weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) (m : ℤ)) (d + 1) =
      m • AlgebraicGeometry.firstChernClass
        (weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) 1) (d + 1) := fun d =>
    firstChernClass_twist_natCast
      (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun _ : σ => (1 : ℕ+)))
      (weightedPolynomialGrading_one_generated k) m d
  rw [topSelfIntersection_of_firstChernClass_nsmul _ hP _ _ m hc1]
  obtain ⟨e, he, hL⟩ := weightedProjectiveSpace_one_iso_projectiveSpace_twist k (σ := σ)
  have : e.hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨he⟩
  have hP' : IsProperOver k (ProjectiveSpace (Fintype.card σ - 1) k) := inferInstance
  rw [AlgebraicGeometry.topSelfIntersection_eq_of_iso_over e hP hP'
      (projectiveSpaceTwist k (Fintype.card σ - 1) 1) _ hL,
    projectiveSpace_top_selfIntersection_one _ hP', mul_one,
    weightedProjectiveSpace_one_dimension_nat k]

end
