import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionOpenCoverSup
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.RingTheory.PolynomialAwayVariableRingEquiv

/-! # Krull dimension of a locally polynomial relative Proj

Statement: `X` a locally Noetherian scheme, `S` a graded quasicoherent `O_X`-algebra which is locally the
standard-graded polynomial algebra in `n + 1` variables (`|σ| = n + 1`, all weights 1). Then
`dim Proj_X S = dim X + n` (topological Krull dimensions, in `WithBot ℕ∞`).
The Noetherian hypothesis is necessary: for a general domain R one only has dim R + 1 ≤ dim R[x] ≤ 2 dim R + 1
(Mathlib `Polynomial.ringKrullDim_le`), and Seidenberg constructed domains with dim R = 1, dim R[x] = 3, for which
dim P^1_R = dim R[x] = 3 ≠ dim R + 1.
Proof:
1. Charts. Atlas charts U_i (affine, covering X) with S(U_i) ≃+* R_i[x_σ] (R_i = Γ(X, U_i), standard grading).
   π⁻¹(U_i) = image of the open immersion `projChart U_i : Proj S(U_i) → Proj_X S` (`proj_preimage_eq_opensRange`),
   so the `projChart U_i` form an open cover of Proj_X S indexed by the atlas; `Proj.map` along the graded
   isomorphism `𝒜.equiv i` (both directions) gives Proj S(U_i) ≅ Proj R_i[x_σ] (`projIsoOfRingEquiv` below, a private
   copy of `Proj.isoOfRingEquiv` from `LocallyWeightedProjLocalProduct.lean`, copied to avoid importing that module's
   closure).
2. Dimension of a chart (`Proj.topologicalKrullDim_mvPolynomial_of_isNoetherianRing`). R_i is Noetherian
   (`IsLocallyNoetherian.component_noetherian`). Proj R_i[x_σ] is covered by the |σ| affine opens
   D_+(x_j) ≅ Spec (R_i[x_σ]_{x_j})_0 (`Proj.basicOpenIsoSpec`, `Proj.iSup_basicOpen_eq_top'`: the x_j generate
   R_i[x_σ] over degree 0), and (R_i[x_σ]_{x_j})_0 ≅ R_i[y_k : k ≠ j] (dehomogenisation,
   `MvPolynomial.homogeneousAwayXRingEquiv`). dim Spec A = ringKrullDim A
   (`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`), `MvPolynomial.ringKrullDim_of_isNoetherianRing` gives
   ringKrullDim R_i[y_k : k ≠ j] = ringKrullDim R_i + (|σ| − 1). All blocks have the same dimension and σ ≠ ∅, so
   `topologicalKrullDim_eq_iSup_openCover` gives dim Proj R_i[x_σ] = ringKrullDim R_i + n.
3. Globalise. `topologicalKrullDim_eq_iSup_openCover` for Proj_X S with the chart cover and for X with the cover
   {U_i}; dim U_i = ringKrullDim R_i (U_i ≅ Spec R_i); dimension is invariant under isomorphism
   (`IsHomeomorph.topologicalKrullDim_eq`): dim Proj_X S = ⨆_i (dim U_i + n) = (⨆_i dim U_i) + n = dim X + n, where
   the middle step is `withBot_iSup_add_const` (private copy from `RelativeDimensionAdd.lean`) for a nonempty index
   set; if the atlas index set is empty, X is empty and both sides are ⊥.
Edge cases: n = 0 (|σ| = 1): Proj R[x] ≅ Spec R, dim = dim X + 0 — the formula holds. |σ| = 0 is excluded by
hσ (the relative Proj would be empty and the right side dim X + (−1) is not expressible). X empty: both sides ⊥.
X disconnected / not irreducible: fine, the formula is a sup over charts on both sides. X = Spec of a field:
dim P^n_k = 0 + n.
Source: Matsumura, Commutative Ring Theory, Thm 15.4 (dim R[x] = dim R + 1 for Noetherian R; Mathlib
`Polynomial.ringKrullDim_of_isNoetherianRing`); Hartshorne II.2.5. Used for the ruled surface `P(O ⊕ L)`
of Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `(⨆ i, f i) + a = ⨆ i, (f i + a)` in `WithBot ℕ∞` for a nonempty index set (private copy of the lemma of the
same name in `RelativeDimensionAdd.lean`, which is `private` there). -/
private lemma withBot_iSup_add_const
    {ι : Type*} [Nonempty ι] (f : ι → WithBot ℕ∞)
    (a : WithBot ℕ∞) :
    (⨆ i, f i) + a = ⨆ i, f i + a := by
  cases a with
  | bot => simp
  | coe a =>
      by_cases hs : (⨆ i, f i) = ⊥
      · have hfbot : ∀ i, f i = ⊥ := by
          intro i
          exact le_bot_iff.mp ((le_iSup f i).trans_eq hs)
        simp [hfbot]
      · obtain ⟨s, hs'⟩ := WithBot.ne_bot_iff_exists.mp hs
        have hS : (⨆ i, f i) = (s : WithBot ℕ∞) := hs'.symm
        have hex : ∃ j, f j ≠ ⊥ := by
          by_contra h
          push Not at h
          exact hs (by simp [h])
        obtain ⟨j, hj⟩ := hex
        let g : ι → ℕ∞ := fun i => (f i).unbotD 0
        have hfg : ∀ i, f i ≤ (g i : WithBot ℕ∞) := by
          intro i
          exact WithBot.le_coe_unbotD (f i) 0
        have hgs : ∀ i, (g i : WithBot ℕ∞) ≤ ⨆ i, f i := by
          intro i
          by_cases hi : f i = ⊥
          · simp [g, hi, hS]
          · obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hi
            have hi' : (g i : WithBot ℕ∞) = f i := by
              simp [g, ← hx]
            rw [hi']
            exact le_iSup f i
        have hSg : (⨆ i, f i) = (⨆ i, g i : ℕ∞) := by
          apply le_antisymm
          · rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
            exact iSup_mono hfg
          · rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
            exact iSup_le hgs
        have hqa : ∀ i, f i + (a : WithBot ℕ∞) ≤ ((g i + a : ℕ∞) : WithBot ℕ∞) := by
          intro i
          have := add_le_add_right (hfg i) (a : WithBot ℕ∞)
          simpa only [WithBot.coe_add, add_comm] using this
        have hqb : ∀ i, ((g i + a : ℕ∞) : WithBot ℕ∞) ≤ ⨆ i, f i + (a : WithBot ℕ∞) := by
          intro i
          by_cases hi : f i = ⊥
          · have hja : ((0 + a : ℕ∞) : WithBot ℕ∞) ≤
                f j + (a : WithBot ℕ∞) := by
              obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hj
              have hxa : ((0 + a : ℕ∞) : WithBot ℕ∞) ≤ ((x + a : ℕ∞) : WithBot ℕ∞) := by
                exact WithBot.coe_le_coe.mpr (add_le_add_left (bot_le : (0 : ℕ∞) ≤ x) a)
              simpa only [← hx, WithBot.coe_add] using hxa
            simpa [g, hi] using hja.trans (le_iSup (fun k => f k + (a : WithBot ℕ∞)) j)
          · obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hi
            have hi' : ((g i + a : ℕ∞) : WithBot ℕ∞) =
                f i + (a : WithBot ℕ∞) := by
              simp [g, ← hx]
            rw [hi']
            exact le_iSup (fun k => f k + (a : WithBot ℕ∞)) i
        have hq : (⨆ i, f i + (a : WithBot ℕ∞)) =
            (⨆ i, g i + a : ℕ∞) := by
          rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
          apply le_antisymm
          · exact iSup_mono hqa
          · exact iSup_le hqb
        calc
          (⨆ i, f i) + (a : WithBot ℕ∞) =
              (((⨆ i, g i : ℕ∞) + a : ℕ∞) : WithBot ℕ∞) := by rw [hSg, WithBot.coe_add]
          _ = (((⨆ i, g i + a : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by rw [ENat.iSup_add]
          _ = ⨆ i, f i + (a : WithBot ℕ∞) := hq.symm

section ProjIso

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
variable [GradedRing 𝒜] [GradedRing ℬ]

/-- A degree-preserving ring equivalence induces an isomorphism of Proj schemes (private copy of
`AlgebraicGeometry.Proj.isoOfRingEquiv` in `LocallyWeightedProjLocalProduct.lean`, copied so
that this module does not import that module's closure). -/
private def projIsoOfRingEquiv (e : A ≃+* B)
    (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) : AlgebraicGeometry.Proj 𝒜 ≅ AlgebraicGeometry.Proj ℬ := by
  let f : 𝒜 →+*ᵍ ℬ :=
    { toRingHom := e.toRingHom
      map_mem := fun {i} {a} ha => (he i a).mp ha }
  let g : ℬ →+*ᵍ 𝒜 :=
    { toRingHom := e.symm.toRingHom
      map_mem := fun {i} {b} hb => (he i (e.symm b)).mpr (by simpa using hb) }
  have hf : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map f := by
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi b hb
    change b ∈ ℬ i at hb
    rw [← show f (e.symm b) = b by simp [f]]
    apply Ideal.mem_map_of_mem f.toRingHom
    exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi
      ((he i (e.symm b)).mpr (by simpa using hb))
  have hg : HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant ℬ).map g := by
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi a ha
    change a ∈ 𝒜 i at ha
    rw [← show g (e a) = a by simp [g]]
    apply Ideal.mem_map_of_mem g.toRingHom
    exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi
      ((he i a).mp ha)
  refine
    { hom := AlgebraicGeometry.Proj.map g hg
      inv := AlgebraicGeometry.Proj.map f hf
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← AlgebraicGeometry.Proj.map_comp f g hf hg]
    have hfg : g.comp f = GradedRingHom.id 𝒜 := by
      ext a
      simp [f, g]
    have hmap : AlgebraicGeometry.Proj.map (g.comp f)
        (HomogeneousIdeal.irrelevant_le_map_comp hf hg) =
        AlgebraicGeometry.Proj.map (GradedRingHom.id 𝒜) (by simp) := by
      congr 1
    exact hmap.trans AlgebraicGeometry.Proj.map_id
  · rw [← AlgebraicGeometry.Proj.map_comp g f hg hf]
    have hgf : f.comp g = GradedRingHom.id ℬ := by
      ext b
      simp [f, g]
    have hmap : AlgebraicGeometry.Proj.map (f.comp g)
        (HomogeneousIdeal.irrelevant_le_map_comp hg hf) =
        AlgebraicGeometry.Proj.map (GradedRingHom.id ℬ) (by simp) := by
      congr 1
    exact hmap.trans AlgebraicGeometry.Proj.map_id

end ProjIso

/-- **dim P^{|σ|−1}_R = dim R + |σ| − 1** for a Noetherian ring `R` and a nonempty finite variable set `σ`:
Proj of the standard-graded polynomial ring is covered by the affine charts D_+(x_j) ≅ Spec R[y_k : k ≠ j]
(`MvPolynomial.homogeneousAwayXRingEquiv`), each of dimension dim R + (|σ| − 1)
(`MvPolynomial.ringKrullDim_of_isNoetherianRing`), and dimension is the sup over an open cover
(`topologicalKrullDim_eq_iSup_openCover`). Source: Hartshorne II.2.5 + Matsumura Thm 15.4. -/
theorem AlgebraicGeometry.Proj.topologicalKrullDim_mvPolynomial_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] {σ : Type u} [Fintype σ] [Nonempty σ] :
    topologicalKrullDim (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule σ R)) =
      ringKrullDim R + ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have hX : ∀ j : σ, (MvPolynomial.X j : MvPolynomial σ R) ∈ MvPolynomial.homogeneousSubmodule σ R 1 :=
    fun j => MvPolynomial.isHomogeneous_X R j
  have htop : (⨆ j : σ, AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ R)
      (MvPolynomial.X j)) = ⊤ := by
    apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
    · exact fun j ↦ ⟨1, hX j⟩
    · apply top_unique
      intro p hp
      clear hp
      induction p using MvPolynomial.induction_on with
      | C r =>
        exact (Algebra.adjoin (MvPolynomial.homogeneousSubmodule σ R 0)
            (Set.range (MvPolynomial.X : σ → MvPolynomial σ R))).algebraMap_mem
          ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C σ r⟩
      | add p q hp hq => exact Subalgebra.add_mem _ hp hq
      | mul_X p j hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (Set.mem_range_self j))
  let 𝒰 : (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule σ R)).OpenCover :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers σ
      (fun j => (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ R)
        (MvPolynomial.X j)).toScheme)
      (fun j => (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ R)
        (MvPolynomial.X j)).ι)
      (fun x => by
        have hx : x ∈ (⨆ j : σ, AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X j)) := by
          rw [htop]; trivial
        obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨j, ⟨x, hj⟩, rfl⟩)
  have hcard : ∀ j : σ, Nat.card {k : σ // k ≠ j} = Fintype.card σ - 1 := by
    intro j
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype_compl (fun k : σ => k = j)]
  have hblock : ∀ j : σ, topologicalKrullDim (𝒰.X j) =
      ringKrullDim R + ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := by
    intro j
    let e := AlgebraicGeometry.Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule σ R)
      (MvPolynomial.X j) (hX j) Nat.one_pos
    change topologicalKrullDim (AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X j)).toScheme = _
    rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    change topologicalKrullDim (AlgebraicGeometry.Spec _) = _
    erw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.homogeneousAwayXRingEquiv R j),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, hcard j]
  rw [topologicalKrullDim_eq_iSup_openCover 𝒰]
  exact (iSup_congr hblock).trans iSup_const

theorem AlgebraicGeometry.Scheme.relativeProj_topologicalKrullDim_of_isLocallyWeightedPolynomial
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X] (S : X.GradedQCAlgebra)
    {σ : Type u} [Fintype σ] (n : ℕ) (hσ : Fintype.card σ = n + 1)
    (hS : S.IsLocallyWeightedPolynomial (fun _ : σ => 1) (fun _ => Nat.one_pos)) :
    topologicalKrullDim (AlgebraicGeometry.Scheme.relativeProj S).left =
      topologicalKrullDim X + (n : WithBot ℕ∞) := by
  classical
  obtain ⟨𝒜⟩ := hS
  have : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  -- the cover of X by the atlas charts
  let 𝒰 : X.OpenCover :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers 𝒜.I
      (fun i => (𝒜.chart i).toOpens.toScheme)
      (fun i => (𝒜.chart i).toOpens.ι)
      (fun x => by
        obtain ⟨i, hi⟩ := 𝒜.covers x
        exact ⟨i, ⟨x, hi⟩, rfl⟩)
  -- the cover of Proj_X S by the charts Proj S(U_i)
  let 𝒱 : (AlgebraicGeometry.Scheme.relativeProj S).left.OpenCover :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers 𝒜.I
      (fun i => AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (𝒜.chart i)))
      (fun i => S.toGradedAffineAlgebra.projChart (𝒜.chart i))
      (fun x => by
        obtain ⟨i, hi⟩ := 𝒜.covers ((AlgebraicGeometry.Scheme.relativeProj S).hom x)
        have hx : x ∈ S.toGradedAffineAlgebra.relativeProj.hom ⁻¹ᵁ (𝒜.chart i).toOpens := hi
        rw [S.toGradedAffineAlgebra.proj_preimage_eq_opensRange] at hx
        obtain ⟨y, hy⟩ := hx
        exact ⟨i, y, hy⟩)
      (fun i => S.toGradedAffineAlgebra.projChart_isOpenImmersion (𝒜.chart i))
  have hblock : ∀ i : 𝒜.I, topologicalKrullDim (𝒱.X i) =
      topologicalKrullDim (𝒰.X i) + (n : WithBot ℕ∞) := by
    intro i
    have : IsNoetherianRing Γ(X, (𝒜.chart i).toOpens) :=
      AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨(𝒜.chart i).toOpens, (𝒜.chart i).2⟩
    have hU : topologicalKrullDim (𝒰.X i) = ringKrullDim Γ(X, (𝒜.chart i).toOpens) := by
      change topologicalKrullDim (𝒜.chart i).toOpens.toScheme = _
      rw [IsHomeomorph.topologicalKrullDim_eq _
        (𝒜.chart i).2.isoSpec.hom.homeomorph.isHomeomorph]
      change topologicalKrullDim (PrimeSpectrum Γ(X, (𝒜.chart i).toOpens)) = _
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    have he : ∀ (m : ℕ) (a : S.toGradedAffineAlgebra.toAffineAlgebra.sections (𝒜.chart i)),
        a ∈ S.toGradedAffineAlgebra.grading (𝒜.chart i) m ↔
          𝒜.equiv i a ∈ MvPolynomial.homogeneousSubmodule σ Γ(X, (𝒜.chart i).toOpens) m := by
      intro m a
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact 𝒜.equiv_grading i m a
    let iso := projIsoOfRingEquiv (𝒜.equiv i) he
    change topologicalKrullDim (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (𝒜.chart i))) = _
    rw [iso.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq,
      AlgebraicGeometry.Proj.topologicalKrullDim_mvPolynomial_of_isNoetherianRing, hU, hσ]
    simp
  rw [topologicalKrullDim_eq_iSup_openCover 𝒱, topologicalKrullDim_eq_iSup_openCover 𝒰]
  refine (iSup_congr hblock).trans ?_
  cases isEmpty_or_nonempty 𝒜.I with
  | inl h =>
      have : IsEmpty 𝒰.I₀ := h
      rw [iSup_of_empty, iSup_of_empty, WithBot.bot_add]
  | inr h => exact (withBot_iSup_add_const _ _).symm

end
