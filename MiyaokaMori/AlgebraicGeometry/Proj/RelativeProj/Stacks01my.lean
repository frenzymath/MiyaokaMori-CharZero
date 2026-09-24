import MiyaokaMori.Prelude

/-! # The morphism of Proj induced by a graded ring map (Stacks 01MY)

A graded ring homomorphism `ψ : A → B` induces a morphism `r_ψ : U(ψ) → Proj A` defined on the open
`U(ψ) = ⋃ D_+(ψ(f))`; its restriction `D_+(ψ(f)) → D_+(f)` is `Spec` of the degree-zero
homogeneous localization map `A_(f) → B_(ψ(f))` (Stacks 01MY). Used for the finite map from
ordinary to weighted projective space in Lemma 3.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `U(ψ) = ⋃_{f ∈ A_+ homogeneous} D_+(ψ f) ⊆ Proj B`. -/

def AlgebraicGeometry.Proj.mapDomain {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ) :
    (AlgebraicGeometry.Proj ℬ).Opens :=
  ⨆ (f : A) (m : ℕ) (_ : 0 < m) (_ : f ∈ 𝒜 m), AlgebraicGeometry.Proj.basicOpen ℬ (ψ f)

/-- `D_+(ψ f) ≤ U(ψ)` for every homogeneous `f` of positive degree. -/
theorem AlgebraicGeometry.Proj.basicOpen_le_mapDomain {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    {f : A} {m : ℕ} (hm : 0 < m) (hf : f ∈ 𝒜 m) :
    AlgebraicGeometry.Proj.basicOpen ℬ (ψ f) ≤ AlgebraicGeometry.Proj.mapDomain ψ :=
  le_iSup_of_le f (le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le hf le_rfl)))

/-- `U(ψ)` is the supremum of the `D_+(ψ f)` indexed by the subtype of homogeneous
elements of positive degree (reindexing of the definition of `mapDomain`). -/
theorem AlgebraicGeometry.Proj.iSup_basicOpen_eq_mapDomain {A B σ τ : Type u} [CommRing A]
    [CommRing B] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ) :
    (⨆ i : {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}, AlgebraicGeometry.Proj.basicOpen ℬ (ψ i.1.1)) =
      AlgebraicGeometry.Proj.mapDomain ψ := by
  apply le_antisymm
  · exact iSup_le fun i => AlgebraicGeometry.Proj.basicOpen_le_mapDomain ψ i.2.1 i.2.2
  · refine iSup_le fun f => iSup_le fun m => iSup_le fun hm => iSup_le fun hf => ?_
    exact le_iSup_of_le ⟨(f, m), hm, hf⟩ le_rfl

/-- The preimages of the `D_+(ψ f)` in `U(ψ)` form an open cover of `U(ψ)`: this is the definition of
`mapDomain` as a supremum. -/
theorem AlgebraicGeometry.Proj.mapDomain_isOpenCover {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ) :
    TopologicalSpace.IsOpenCover (fun i : {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2} =>
      (AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ i.1.1)) := by
  show (⨆ i : {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2},
      (AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ i.1.1)) = ⊤
  rw [← AlgebraicGeometry.Scheme.Hom.preimage_iSup,
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_mapDomain,
    AlgebraicGeometry.Scheme.Opens.ι_preimage_self]

noncomputable def AlgebraicGeometry.Proj.mapOfGradedHom.cover {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ) :
    (AlgebraicGeometry.Proj.mapDomain ψ).toScheme.OpenCover :=
  (AlgebraicGeometry.Proj.mapDomain ψ).toScheme.openCoverOfIsOpenCover
    (fun i : {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2} =>
      (AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ i.1.1))
    (AlgebraicGeometry.Proj.mapDomain_isOpenCover ψ)

/-- The local morphism `D_+(ψ f) ≅ Spec B_(ψ f) → Spec A_(f) → Proj A`. -/

noncomputable def AlgebraicGeometry.Proj.mapOfGradedHom.chart {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ) (i : {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}) :
    ((AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ i.1.1)).toScheme ⟶
      AlgebraicGeometry.Proj 𝒜 :=
  (AlgebraicGeometry.Proj.mapDomain ψ).ι.resLE (AlgebraicGeometry.Proj.basicOpen ℬ (ψ i.1.1)) _ le_rfl ≫
    (AlgebraicGeometry.Proj.basicOpenIsoSpec ℬ (ψ i.1.1) (ψ.2 i.2.2) i.2.1).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ i.1.1)) ≫
    AlgebraicGeometry.Proj.awayι 𝒜 i.1.1 i.2.2 i.2.1

/-- The ring identity behind the compatibility of the charts (Stacks 01MY, proof):
both `A_(f) → B_(ψ f) → B_(ψ(fg))` and `A_(f) → A_(fg) → B_(ψ(fg))` send `a/fⁿ` to
`ψ(a)ψ(g)ⁿ/ψ(fg)ⁿ`. -/
theorem HomogeneousLocalization.awayMap_comp_Away_map {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    {f g : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) :
    (HomogeneousLocalization.awayMap ℬ (ψ.2 hg) (map_mul ψ f g)).comp
        (HomogeneousLocalization.Away.map ψ f) =
      (HomogeneousLocalization.Away.map ψ (f * g)).comp (HomogeneousLocalization.awayMap 𝒜 hg rfl) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf x
  simp only [RingHom.comp_apply, HomogeneousLocalization.Away.map_mk,
    HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp [map_mul, map_pow]

/-- `D_+(ψ(fg)) ≤ D_+(ψ f)` pulled back to `U(ψ)`. -/
theorem AlgebraicGeometry.Proj.mapDomain_preimage_basicOpen_le {A B σ τ : Type u} [CommRing A]
    [CommRing B] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    {f g k : A} (hk : k = f * g) :
    (AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ k) ≤
      (AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f) :=
  AlgebraicGeometry.Scheme.Hom.preimage_mono _
    (AlgebraicGeometry.Proj.basicOpen_mono ℬ _ _ ⟨ψ g, by rw [hk, map_mul]⟩)

/-- Restriction compatibility of the charts (Stacks 01MY, proof): the chart of `f` restricted to
`D_+(ψ(fg))` is the chart of `fg`. -/
theorem AlgebraicGeometry.Proj.mapOfGradedHom.homOfLE_chart {A B σ τ : Type u} [CommRing A]
    [CommRing B] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (i j k : {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}) (hk : k.1.1 = i.1.1 * j.1.1)
    (hkm : k.1.2 = i.1.2 + j.1.2) :
    (AlgebraicGeometry.Proj.mapDomain ψ).toScheme.homOfLE
        (AlgebraicGeometry.Proj.mapDomain_preimage_basicOpen_le ψ hk) ≫
      AlgebraicGeometry.Proj.mapOfGradedHom.chart ψ i =
    AlgebraicGeometry.Proj.mapOfGradedHom.chart ψ k := by
  obtain ⟨⟨f, m⟩, hm, hf⟩ := i
  obtain ⟨⟨g, n⟩, hn, hg⟩ := j
  obtain ⟨⟨x, d⟩, hd, hx⟩ := k
  dsimp only at hk hkm hm hn hd hf hg hx ⊢
  subst hk hkm
  simp only [AlgebraicGeometry.Proj.mapOfGradedHom.chart, AlgebraicGeometry.Scheme.Hom.map_resLE_assoc]
  rw [← AlgebraicGeometry.Scheme.Hom.resLE_map_assoc (AlgebraicGeometry.Proj.mapDomain ψ).ι le_rfl
    (AlgebraicGeometry.Proj.basicOpen_mono ℬ (ψ f) (ψ (f * g)) ⟨ψ g, map_mul ψ f g⟩),
    AlgebraicGeometry.Proj.basicOpenIsoSpec_hom, AlgebraicGeometry.Proj.basicOpenIsoSpec_hom,
    ← AlgebraicGeometry.Proj.basicOpenToSpec_SpecMap_awayMap_assoc ℬ (ψ.2 hg) (map_mul ψ f g)]
  congr 2
  rw [← AlgebraicGeometry.Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    HomogeneousLocalization.awayMap_comp_Away_map ψ hf hg, CommRingCat.ofHom_comp,
    AlgebraicGeometry.Spec.map_comp_assoc,
    AlgebraicGeometry.Proj.SpecMap_awayMap_awayι 𝒜 hf hm hg rfl]

/-- Compatibility on pullbacks for a cover of the form `Scheme.openCoverOfIsOpenCover`:
if the local morphisms `g i` agree on an open `W ⊇ U i ⊓ U j` for every pair, they agree on the
pullbacks `U i ×[X] U j` (generic scheme-level helper). -/
theorem AlgebraicGeometry.Scheme.openCoverOfIsOpenCover_pullback_compat {X Y : AlgebraicGeometry.Scheme.{u}}
    {s : Type v} (U : s → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (g : ∀ i, (U i).toScheme ⟶ Y)
    (H : ∀ i j, ∃ (W : X.Opens) (h₁ : W ≤ U i) (h₂ : W ≤ U j),
      U i ⊓ U j ≤ W ∧ X.homOfLE h₁ ≫ g i = X.homOfLE h₂ ≫ g j) (x y : s) :
    CategoryTheory.Limits.pullback.fst ((X.openCoverOfIsOpenCover U hU).f x)
        ((X.openCoverOfIsOpenCover U hU).f y) ≫ g x =
      CategoryTheory.Limits.pullback.snd _ _ ≫ g y := by
  show CategoryTheory.Limits.pullback.fst (U x).ι (U y).ι ≫ g x =
    CategoryTheory.Limits.pullback.snd (U x).ι (U y).ι ≫ g y
  obtain ⟨W, h₁, h₂, hW, hg⟩ := H x y
  refine (cancel_epi (AlgebraicGeometry.isPullback_opens_inf (U x) (U y)).isoPullback.hom).mp ?_
  rw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc,
    ← X.homOfLE_homOfLE hW h₁, ← X.homOfLE_homOfLE hW h₂, Category.assoc, Category.assoc, hg]

/-- Compatibility on overlaps (the restriction compatibility in the proof of Stacks 01MY). -/
theorem AlgebraicGeometry.Proj.mapOfGradedHom.chart_compat {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (x y : (AlgebraicGeometry.Proj.mapOfGradedHom.cover ψ).I₀) :
    CategoryTheory.Limits.pullback.fst ((AlgebraicGeometry.Proj.mapOfGradedHom.cover ψ).f x)
        ((AlgebraicGeometry.Proj.mapOfGradedHom.cover ψ).f y) ≫
        AlgebraicGeometry.Proj.mapOfGradedHom.chart ψ x =
      CategoryTheory.Limits.pullback.snd _ _ ≫ AlgebraicGeometry.Proj.mapOfGradedHom.chart ψ y := by
  refine AlgebraicGeometry.Scheme.openCoverOfIsOpenCover_pullback_compat
    (fun i : {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2} =>
      (AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ i.1.1))
    (AlgebraicGeometry.Proj.mapDomain_isOpenCover ψ)
    (AlgebraicGeometry.Proj.mapOfGradedHom.chart ψ) (fun i j => ?_) x y
  refine ⟨_, AlgebraicGeometry.Proj.mapDomain_preimage_basicOpen_le ψ
      (rfl : i.1.1 * j.1.1 = i.1.1 * j.1.1),
    AlgebraicGeometry.Proj.mapDomain_preimage_basicOpen_le ψ (mul_comm i.1.1 j.1.1), ?_, ?_⟩
  · rw [← AlgebraicGeometry.Scheme.Hom.preimage_inf, ← AlgebraicGeometry.Proj.basicOpen_mul, map_mul]
  · rw [AlgebraicGeometry.Proj.mapOfGradedHom.homOfLE_chart ψ i j
        ⟨(i.1.1 * j.1.1, i.1.2 + j.1.2), Nat.add_pos_left i.2.1 _, SetLike.mul_mem_graded i.2.2 j.2.2⟩
        rfl rfl,
      AlgebraicGeometry.Proj.mapOfGradedHom.homOfLE_chart ψ j i
        ⟨(i.1.1 * j.1.1, i.1.2 + j.1.2), Nat.add_pos_left i.2.1 _, SetLike.mul_mem_graded i.2.2 j.2.2⟩
        (mul_comm _ _) (add_comm _ _)]

noncomputable def AlgebraicGeometry.Proj.mapOfGradedHom {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ) :
    (AlgebraicGeometry.Proj.mapDomain ψ).toScheme ⟶ AlgebraicGeometry.Proj 𝒜 :=
  (AlgebraicGeometry.Proj.mapOfGradedHom.cover ψ).glueMorphisms
    (AlgebraicGeometry.Proj.mapOfGradedHom.chart ψ) (AlgebraicGeometry.Proj.mapOfGradedHom.chart_compat ψ)

/-- For `V ≤ U`, the inverse of `U.ι.resLE V (U.ι ⁻¹ᵁ V) le_rfl : (U.ι ⁻¹ᵁ V) ⟶ V`
(generic scheme-level helper). -/
def AlgebraicGeometry.Scheme.Opens.toPreimageι {X : AlgebraicGeometry.Scheme.{u}} {U V : X.Opens}
    (h : V ≤ U) : V.toScheme ⟶ (U.ι ⁻¹ᵁ V).toScheme :=
  (X.isoOfEq (by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι, inf_eq_right.mpr h] :
      U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V)).inv ≫ (U.ι.isoImage (U.ι ⁻¹ᵁ V)).inv

@[reassoc]
theorem AlgebraicGeometry.Scheme.Opens.toPreimageι_ι {X : AlgebraicGeometry.Scheme.{u}}
    {U V : X.Opens} (h : V ≤ U) :
    AlgebraicGeometry.Scheme.Opens.toPreimageι h ≫ (U.ι ⁻¹ᵁ V).ι = X.homOfLE h := by
  rw [AlgebraicGeometry.Scheme.Opens.toPreimageι, Category.assoc,
    AlgebraicGeometry.Scheme.Opens.isoImage_ι_inv_ι, AlgebraicGeometry.Scheme.isoOfEq_inv,
    AlgebraicGeometry.Scheme.homOfLE_homOfLE]

@[reassoc]
theorem AlgebraicGeometry.Scheme.Opens.toPreimageι_resLE {X : AlgebraicGeometry.Scheme.{u}}
    {U V : X.Opens} (h : V ≤ U) :
    AlgebraicGeometry.Scheme.Opens.toPreimageι h ≫ U.ι.resLE V (U.ι ⁻¹ᵁ V) le_rfl = 𝟙 _ := by
  rw [← cancel_mono V.ι, Category.assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι,
    AlgebraicGeometry.Scheme.Opens.toPreimageι_ι_assoc, AlgebraicGeometry.Scheme.homOfLE_ι,
    Category.id_comp]

/-- On `D_+(ψ f)` the morphism is `Spec (HomogeneousLocalization.Away.map ψ f)`. -/

theorem AlgebraicGeometry.Proj.mapOfGradedHom_basicOpen {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (f : A) (m : ℕ) (hm : 0 < m) (hf : f ∈ 𝒜 m) :
    (AlgebraicGeometry.Proj.basicOpenIsoSpec ℬ (ψ f) (ψ.2 hf) hm).inv ≫
        (AlgebraicGeometry.Proj ℬ).homOfLE (U := AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
          (V := AlgebraicGeometry.Proj.mapDomain ψ)
          (le_iSup_of_le f (le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le hf le_rfl)))) ≫
        AlgebraicGeometry.Proj.mapOfGradedHom ψ =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
        AlgebraicGeometry.Proj.awayι 𝒜 f hf hm := by
  have h1 : (AlgebraicGeometry.Proj ℬ).homOfLE (U := AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
      (V := AlgebraicGeometry.Proj.mapDomain ψ)
      (le_iSup_of_le f (le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le hf le_rfl)))) =
      AlgebraicGeometry.Scheme.Opens.toPreimageι
        (AlgebraicGeometry.Proj.basicOpen_le_mapDomain ψ hm hf) ≫
        ((AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f)).ι :=
    (AlgebraicGeometry.Scheme.Opens.toPreimageι_ι _).symm
  have h2 : ((AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f)).ι ≫
      AlgebraicGeometry.Proj.mapOfGradedHom ψ =
      (AlgebraicGeometry.Proj.mapDomain ψ).ι.resLE (AlgebraicGeometry.Proj.basicOpen ℬ (ψ f)) _ le_rfl ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec ℬ (ψ f) (ψ.2 hf) hm).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
        AlgebraicGeometry.Proj.awayι 𝒜 f hf hm :=
    AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms (AlgebraicGeometry.Proj.mapOfGradedHom.cover ψ)
      (AlgebraicGeometry.Proj.mapOfGradedHom.chart ψ) (AlgebraicGeometry.Proj.mapOfGradedHom.chart_compat ψ)
      (⟨(f, m), hm, hf⟩ : {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2})
  rw [h1, Category.assoc, h2,
    AlgebraicGeometry.Scheme.Opens.toPreimageι_resLE_assoc, Iso.inv_hom_id_assoc]

end
