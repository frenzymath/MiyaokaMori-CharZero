import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueDegreeSpecMapGenericPoint
import MiyaokaMori.RingTheory.WeightedPowerAwayMapFinrank
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPowerMapPullbackTwist
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPowerChartFinite
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2SchemeGenerator
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition

/-! # Degree of the power map and pullback of the twisting sheaf

When some coordinate has weight `1`, the power map `φ : P^N → P(w)`, `[u] ↦ [u_i^{w_i}]`, has
function field degree `∏ w_i`; and when every `w_i` divides `m`, `φ^* O_{P(w)}(m) ≅ O_{P^N}(m)`.
This is the computation of `deg φ_k = (k!)^{n+1}` and of `φ_k^* O(m)` in the proof of the Veronese
polarization lemma of the paper.

## Route

The top-level statement `weightedPowerMap_degree_twist` combines two independent results:

* **Degree** `weightedPowerMap_functionFieldDegree`: `deg g = ∏ w_i`. Take `w_{i₀} = 1`; on the
  chart `D_+(u_{i₀}) = g⁻¹(D_+(x_{i₀}))`, `g` is `Spec` of the ring map
  `φ = weightedPowerAwayMap k w hw i₀ : k[x]^{(w)}_(x_{i₀}) → k[u]_(u_{i₀})` (the local formula of
  Stacks 01MY).
  1. `weightedPowerMap_functionFieldDegree_eq_chart`: open immersions have residue degree `1` and
     residue degrees multiply along composites, so `deg g` is the residue degree of `Spec φ` at the
     generic point;
  2. `residueDegree_specMap_genericPoint`: for an injective `φ : R → S` between domains, the residue
     degree of `Spec φ` at the generic point is `[Frac S : Frac R] = finrank_R S`
     (`IsFractionRing.finrank_eq`);
  3. `weightedPowerAwayMap_finrank` (pure algebra): `k[u]_(u_{i₀}) ≅ k[z]` (`z_j = u_j/u_{i₀}`) is
     free as a module over `k[x]^{(w)}_(x_{i₀}) ≅ k[y]` (`y_j ↦ z_j^{w_j}`), with basis `z^a`
     (`0 ≤ a_j < w_j`), of rank `∏ w_j`.
* **Twisting sheaf** `weightedPowerMap_pullback_twist`: the local frames `x_j^{m/w_j} ↦ u_j^m` glue.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Auxiliary: the coordinate charts of the Proj of a domain are nonempty -/

/-- For a domain `A` and a nonzero homogeneous `f` of positive degree, `Spec (A_(f))₀` is nonempty:
the zero ideal is a point of `Proj A` lying in `D_+(f)`, and it is pulled back through the image of
the open immersion `Proj.awayι` (`opensRange_awayι`). -/
theorem AlgebraicGeometry.Proj.nonempty_spec_away_of_ne_zero {A σ : Type u} [CommRing A] [IsDomain A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m : ℕ} (hf : f ∈ 𝒜 m)
    (hm : 0 < m) (hf0 : f ≠ 0) :
    Nonempty (AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))) := by
  let p : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := Ideal.isPrime_bot
      not_irrelevant_le := by
        intro hle
        have hfm : f ∈ (HomogeneousIdeal.irrelevant 𝒜 : Set A) :=
          HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hm hf
        have : f ∈ (⊥ : HomogeneousIdeal 𝒜) := hle hfm
        exact hf0 (show f = 0 from this) }
  have hp : (p : AlgebraicGeometry.Proj 𝒜) ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
    show f ∉ p.asHomogeneousIdeal
    exact hf0
  rw [← AlgebraicGeometry.Proj.opensRange_awayι 𝒜 f hf hm] at hp
  obtain ⟨ξ, -⟩ := hp
  exact ⟨ξ⟩

/-! ## Step 1: reducing `deg g` to a chart -/

/-- The function field degree of the power map `g` equals the residue degree at the generic point
`ξ` of `Spec` of the chart ring map `φ = weightedPowerAwayMap k w hw i₀` (in the affine scheme
`Spec k[u]_(u_{i₀}^{w_{i₀}})` corresponding to `D_+(u_{i₀})`).

Reference: Stacks 01MY (the morphism of `Proj`s induced by a graded ring homomorphism is
`Spec (A_(f) → B_(ψ f))` on `D_+(ψ f)`).

Proof sketch. Write `ψ = weightedPowerGradedHom k w`, `f = x_{i₀} ∈ 𝒜_1` (`w_{i₀} = 1`),
`ψ f = u_{i₀}^1 ∈ ℬ_1`. `InducedByPowerMap g` says
`g = (topIso).inv ≫ (isoOfEq h).hom ≫ Proj.mapOfGradedHom ψ`, and `Proj.mapOfGradedHom_basicOpen ψ f 1`
gives the commutative square
`(basicOpenIsoSpec ℬ (ψ f)).inv ≫ homOfLE ≫ mapOfGradedHom ψ = Spec.map φ ≫ awayι 𝒜 f`, where
`awayι ℬ (ψ f) = (basicOpenIsoSpec ℬ (ψ f)).inv ≫ (D_+(ψ f)).ι` and
`(D_+(ψ f)).ι ≫ topIso.inv ≫ isoOfEq.hom = homOfLE` (`Scheme.homOfLE_ι`, `isoOfEq_hom_ι`); hence
`awayι ℬ (ψ f) ≫ g = Spec.map φ ≫ awayι 𝒜 f`. Apply `residueDegree_comp` (residue degrees multiply
along composites) at `ξ`: the left side is
`g.residueDegree (awayι ξ) · (awayι ℬ).residueDegree ξ = g.residueDegree (genericPoint) · 1` (an open
immersion has residue degree `1`: `residueFieldMap` is an isomorphism), and the right side is
`(awayι 𝒜 f).residueDegree (Spec φ ξ) · (Spec φ).residueDegree ξ = (Spec φ).residueDegree ξ`. Finally
`functionFieldDegree g = g.residueDegree (genericPoint)` by definition. -/
theorem weightedPowerMap_functionFieldDegree_eq_chart (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (i₀ : σ) (h1 : w i₀ = 1)
    [AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos))]
    [AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k w hw)]
    (g : weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ⟶
      weightedProjectiveSpace k w hw) (hg : InducedByPowerMap g) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    ∀ ξ : AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (weightedPowerGradedHom k w (MvPolynomial.X i₀)))),
      (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
          (weightedPowerGradedHom k w (MvPolynomial.X i₀))
          ((weightedPowerGradedHom k w).2 (weightedAwayDegreeOneEquiv.X_mem k w i₀ h1))
          Nat.one_pos).base ξ =
        genericPoint (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos)) →
      functionFieldDegree g =
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw i₀))).residueDegree ξ := by
  let _ := MvPolynomial.weightedGradedAlgebra (R := k) w
  let _ := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  obtain ⟨h, rfl⟩ := hg
  set ψ := weightedPowerGradedHom k w with hψ
  intro ξ hξ
  have h' : AlgebraicGeometry.Proj.mapDomain ψ = ⊤ := h
  have hX : (MvPolynomial.X i₀ : MvPolynomial σ k) ∈ MvPolynomial.weightedHomogeneousSubmodule k w 1 :=
    weightedAwayDegreeOneEquiv.X_mem k w i₀ h1
  have hle : AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ (MvPolynomial.X i₀)) ≤
      AlgebraicGeometry.Proj.mapDomain ψ :=
    le_iSup_of_le (MvPolynomial.X i₀) (le_iSup_of_le 1 (le_iSup_of_le Nat.one_pos (le_iSup_of_le hX le_rfl)))
  -- D_+(ψ x_{i₀}) ↪ P^N = ⊤ ≅ U(ψ) is `homOfLE`
  have hfac : (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ (MvPolynomial.X i₀))).ι ≫
      (AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).topIso.inv ≫
      ((AlgebraicGeometry.Proj
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).isoOfEq h'.symm).hom =
      (AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).homOfLE hle := by
    rw [← cancel_mono (AlgebraicGeometry.Proj.mapDomain ψ).ι]
    simp only [Category.assoc, AlgebraicGeometry.Scheme.isoOfEq_hom_ι, AlgebraicGeometry.Scheme.toIso_inv_ι,
      Category.comp_id, AlgebraicGeometry.Scheme.homOfLE_ι]
  -- Stacks 01MY on the chart: awayι ℬ (ψ x_{i₀}) ≫ g = Spec φ ≫ awayι 𝒜 x_{i₀}
  have key : AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (ψ (MvPolynomial.X i₀)) (ψ.2 hX) Nat.one_pos ≫
      ((AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).topIso.inv ≫
        ((AlgebraicGeometry.Proj
          (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).isoOfEq h'.symm).hom ≫
        AlgebraicGeometry.Proj.mapOfGradedHom ψ) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw i₀)) ≫
        AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀)
          hX Nat.one_pos := by
    change _ = AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map ψ (MvPolynomial.X i₀))) ≫ _
    rw [← AlgebraicGeometry.Proj.mapOfGradedHom_basicOpen ψ (MvPolynomial.X i₀) 1 Nat.one_pos hX,
      ← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι, Category.assoc, ← hfac]
    simp only [Category.assoc]
  -- residue degrees multiply along composites; open immersions contribute 1
  have hcomp := AlgebraicGeometry.Intersection.residueDegree_comp
    (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
      (ψ (MvPolynomial.X i₀)) (ψ.2 hX) Nat.one_pos)
    ((AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).topIso.inv ≫
        ((AlgebraicGeometry.Proj
          (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).isoOfEq h'.symm).hom ≫
        AlgebraicGeometry.Proj.mapOfGradedHom ψ) ξ
  rw [key, AlgebraicGeometry.Intersection.residueDegree_comp,
    AlgebraicGeometry.Scheme.Hom.residueDegree_eq_one_of_isOpenImmersion
      (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀)
        hX Nat.one_pos),
    AlgebraicGeometry.Scheme.Hom.residueDegree_eq_one_of_isOpenImmersion
      (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (ψ (MvPolynomial.X i₀)) (ψ.2 hX) Nat.one_pos),
    one_mul, mul_one] at hcomp
  unfold functionFieldDegree
  rw [← hξ]
  exact hcomp.symm

/-! ## Assembly: the degree -/

/-- `deg g = ∏ w_i`, assembled from steps 1, 2 and 3. -/
theorem weightedPowerMap_functionFieldDegree (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h1 : ∃ i, w i = 1)
    [AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos))]
    [AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k w hw)]
    (g : weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ⟶
      weightedProjectiveSpace k w hw) (hg : InducedByPowerMap g) :
    functionFieldDegree g = ∏ i, w i := by
  obtain ⟨i₀, h1⟩ := h1
  let _ := MvPolynomial.weightedGradedAlgebra (R := k) w
  let _ := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  set ψ := weightedPowerGradedHom k w
  have hX : (MvPolynomial.X i₀ : MvPolynomial σ k) ∈ MvPolynomial.weightedHomogeneousSubmodule k w 1 :=
    weightedAwayDegreeOneEquiv.X_mem k w i₀ h1
  -- the two coordinate rings are domains (the charts are open in integral schemes)
  have hintw : AlgebraicGeometry.IsIntegral
      (AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k w)) :=
    ‹AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k w hw)›
  have hint1 : AlgebraicGeometry.IsIntegral
      (AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))) :=
    ‹AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos))›
  have := AlgebraicGeometry.Proj.nonempty_spec_away_of_ne_zero
    (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀) hX Nat.one_pos
    (MvPolynomial.X_ne_zero i₀)
  have := AlgebraicGeometry.Proj.nonempty_spec_away_of_ne_zero
    (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ (MvPolynomial.X i₀)) (ψ.2 hX)
    Nat.one_pos (by rw [weightedPowerGradedHom_X, h1, pow_one]; exact MvPolynomial.X_ne_zero i₀)
  have hA : IsDomain (HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀)) :=
    (AlgebraicGeometry.affine_isIntegral_iff _).mp
      (AlgebraicGeometry.isIntegral_of_isOpenImmersion
        (AlgebraicGeometry.Proj.awayι _ (MvPolynomial.X i₀) hX Nat.one_pos))
  have hB : IsDomain (HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ (MvPolynomial.X i₀))) :=
    (AlgebraicGeometry.affine_isIntegral_iff _).mp
      (AlgebraicGeometry.isIntegral_of_isOpenImmersion
        (AlgebraicGeometry.Proj.awayι _ (ψ (MvPolynomial.X i₀)) (ψ.2 hX) Nat.one_pos))
  -- the generic point of the chart maps to the generic point
  have hgen := AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion
    (AlgebraicGeometry.Proj.awayι _ (ψ (MvPolynomial.X i₀)) (ψ.2 hX) Nat.one_pos)
  rw [weightedPowerMap_functionFieldDegree_eq_chart k w hw i₀ h1 g hg _ hgen,
    AlgebraicGeometry.Scheme.Hom.residueDegree_specMap_genericPoint _
      (weightedPowerAwayMap_finite_injective k w hw i₀).2]
  exact weightedPowerAwayMap_finrank k w hw i₀ h1

/-! ## The main statement -/

/-- The power map `g : P^N → P(w)` has function field degree `∏ w_i`, and `g^* O_{P(w)}(m) ≅ O_{P^N}(m)`
whenever every `w_i` divides `m`. -/
theorem weightedPowerMap_degree_twist (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h1 : ∃ i, w i = 1)
    [AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos))]
    [AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k w hw)]
    (g : weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ⟶
      weightedProjectiveSpace k w hw) (hg : InducedByPowerMap g) :
    functionFieldDegree g = ∏ i, w i ∧
      ∀ m : ℕ, (∀ i, w i ∣ m) →
        Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (weightedProjTwist k w hw (m : ℤ)) ≅
          weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) (m : ℤ)) :=
  ⟨weightedPowerMap_functionFieldDegree k w hw h1 g hg,
    fun m hm => weightedPowerMap_pullback_twist k w hw g hg m hm⟩

end
