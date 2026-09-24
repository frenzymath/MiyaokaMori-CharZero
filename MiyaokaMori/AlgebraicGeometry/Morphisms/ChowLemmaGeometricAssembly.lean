import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Stacks0200_ChowAssembly_Aux
import MiyaokaMori.AlgebraicGeometry.Morphisms.ChowLemmaProjectiveMorphismAux

/-! # Chow's lemma over a base: the geometric assembly (relative form)

Steps 3–9 of Chow's lemma over a Noetherian affine base (`ChowLemmaNoetherianAffineBase.lean`; Stacks 0200
proof with base `S`, Remark 0201), in a form that does not mention the base ring: the data `ChowSetup g`
records an integral scheme `Z` proper over `S`, a finite family of open immersions `u i : W i ⟶ Z` covering
`Z`, open immersions `e i : W i ⟶ Zc i` into projective `S`-schemes `f i : Zc i ⟶ S`, a projective `S`-scheme
`fP : P ⟶ S` with `S`-projections `p i : P ⟶ Zc i`, a nonempty quasi-compact open `U ⊆ Z` contained in every
`(u i).opensRange` (through `s i : U ⟶ W i`), and the "diagonal" `gU : U ⟶ P` with `gU ≫ p i = s i ≫ e i`.

**Route.** Instead of taking the closure
`X''` of `U` in `P`, then the opens `V_i ⊆ X''` and gluing `π`, we take the scheme-theoretic image
`Z' := γ.image` of the graph `γ = (U.ι, gU) : U ⟶ Z ×_S P` (Mathlib `Scheme.Hom.image`). Then

* `π := imageι ≫ pullback.fst : Z' ⟶ Z` is a closed immersion into the base change `Z ×_S P → Z` of the
  projective `fP`, hence projective (`isProjectiveMorphism_of_isClosedImmersion_comp`,
  `isProjectiveMorphism_pullback_fst`) — no gluing and no graph argument are needed;
* `h := imageι ≫ pullback.snd : Z' ⟶ P` is proper (`h ≫ fP = π ≫ g`, `fP` separated) and an immersion:
  on `Z'_i := π ⁻¹ᵁ (u i).opensRange` the morphism `h` factors through `Γ_i := W_i ×_{Zc i} P` (the graph
  of `p i` over the open `(e i).opensRange`), which maps isomorphically onto the open
  `O_i := p i ⁻¹ᵁ (e i).opensRange` of `P`; the factorization `k_i : Z'_i ⟶ Γ_i` is an immersion (because
  `k_i` followed by `Γ_i ⟶ Z ×_S P` is `Z'_i ⟶ Z'`, an open immersion, followed by the closed immersion
  `imageι`) and proper (`k_i` followed by `Γ_i ⟶ W_i` is `π` restricted over `W_i`, which is proper, and
  `Γ_i ⟶ W_i` is separated); the key identity `h ⁻¹ᵁ O_i = Z'_i` holds because the open immersion
  `Z'_i ⟶ h ⁻¹ᵁ O_i` is proper (`Z'_i ⟶ O_i` is proper and `h ∣_ O_i` is separated) with nonempty source into
  an irreducible scheme (`isIso_of_isOpenImmersion_of_isProper`, `Stacks0200_ChowAssembly_Aux.lean`);
  since the `Z'_i` cover `Z'`, `h` is an immersion (`isImmersion_of_preimage_cover`), hence a closed
  immersion, and `π ≫ g = h ≫ fP` is projective;
* `π` is an isomorphism over `U`: the section `τ : U ⟶ π ⁻¹ᵁ U` induced by `toImage` satisfies
  `τ ≫ (π ∣_ U) = 𝟙`, so `τ` is a proper open immersion with nonempty source into an irreducible scheme,
  hence an isomorphism, and so is `π ∣_ U`.

The compatibility `a_i ≫ e_i = Z'_i.ι ≫ h ≫ p_i` needed to define `k_i` is proved by
`ext_of_isDominant_of_isSeparated` (Mathlib): both sides agree on the dense open `U ⊆ Z'_i`, `Z'_i` is
reduced (open in the integral `Z'`) and `f i : Zc i ⟶ S` is separated. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- The input data of the geometric assembly step of Chow's lemma over `S` (Stacks 0200 proof): a finite
open cover `u i : W i ⟶ Z`, projective completions `e i : W i ⟶ Zc i` over `S`, the product `P` of the
`Zc i` over `S` with its projections, a nonempty quasi-compact open `U ⊆ ⋂ (u i).opensRange`, and the
diagonal `gU : U ⟶ P`. Only the *existence* of the factorization `gU` is recorded (no uniqueness). -/
structure ChowSetup {S Z : Scheme.{u}} (g : Z ⟶ S) where
  /-- index set of the cover -/
  ι : Type u
  [fin : Finite ι]
  /-- the pieces of the cover -/
  W : ι → Scheme.{u}
  /-- the open immersions of the cover -/
  u : ∀ i, W i ⟶ Z
  [hu : ∀ i, IsOpenImmersion (u i)]
  hcover : ⨆ i, (u i).opensRange = ⊤
  /-- projective completions of the pieces -/
  Zc : ι → Scheme.{u}
  e : ∀ i, W i ⟶ Zc i
  [he : ∀ i, IsOpenImmersion (e i)]
  f : ∀ i, Zc i ⟶ S
  [hf : ∀ i, IsProjectiveMorphism (f i)]
  hef : ∀ i, e i ≫ f i = u i ≫ g
  /-- the product of the completions over `S` -/
  P : Scheme.{u}
  fP : P ⟶ S
  [hP : IsProjectiveMorphism fP]
  p : ∀ i, P ⟶ Zc i
  hp : ∀ i, p i ≫ f i = fP
  /-- the dense open `U` -/
  U : Z.Opens
  hUne : (U : Set Z).Nonempty
  hUc : IsCompact (U : Set Z)
  s : ∀ i, (U : Scheme.{u}) ⟶ W i
  hs : ∀ i, s i ≫ u i = U.ι
  /-- the diagonal `U ⟶ P` -/
  gU : (U : Scheme.{u}) ⟶ P
  hgU : ∀ i, gU ≫ p i = s i ≫ e i
  hgUf : gU ≫ fP = U.ι ≫ g

namespace ChowSetup

attribute [local instance] ChowSetup.fin ChowSetup.hu ChowSetup.he ChowSetup.hf ChowSetup.hP

variable {S Z : Scheme.{u}} {g : Z ⟶ S} (D : ChowSetup g)

/-- The graph `γ = (U.ι, gU) : U ⟶ Z ×_S P`. -/
def γ : (D.U : Scheme.{u}) ⟶ pullback g D.fP := pullback.lift D.U.ι D.gU D.hgUf.symm

@[simp] lemma γ_fst : D.γ ≫ pullback.fst g D.fP = D.U.ι := pullback.lift_fst _ _ _

@[simp] lemma γ_snd : D.γ ≫ pullback.snd g D.fP = D.gU := pullback.lift_snd _ _ _

instance isImmersion_γ : IsImmersion D.γ := by
  have : IsImmersion (D.γ ≫ pullback.fst g D.fP) := by rw [γ_fst]; infer_instance
  exact IsImmersion.of_comp D.γ (pullback.fst g D.fP)

instance compactSpace_U : CompactSpace D.U := isCompact_iff_compactSpace.mp D.hUc

instance nonempty_U : Nonempty D.U := ⟨⟨D.hUne.choose, D.hUne.choose_spec⟩⟩

instance isProper_fP : IsProper D.fP := IsProjectiveMorphism.isProper D.fP

instance isProper_f (i : D.ι) : IsProper (D.f i) := IsProjectiveMorphism.isProper (D.f i)

/-- `Z'`, the scheme-theoretic image of the graph `γ : U ⟶ Z ×_S P`. -/
abbrev Z' : Scheme.{u} := D.γ.image

/-- The closed immersion `Z' ⟶ Z ×_S P`. -/
abbrev ι' : D.Z' ⟶ pullback g D.fP := D.γ.imageι

/-- The open immersion `U ⟶ Z'`. -/
abbrev t : (D.U : Scheme.{u}) ⟶ D.Z' := D.γ.toImage

@[reassoc (attr := simp)] lemma t_ι' : D.t ≫ D.ι' = D.γ := Scheme.Hom.toImage_imageι _

/-- `π : Z' ⟶ Z`, the projective morphism of Chow's lemma. -/
def π : D.Z' ⟶ Z := D.ι' ≫ pullback.fst g D.fP

/-- `h : Z' ⟶ P`, the (closed) immersion of `Z'` into the product of the completions. -/
def h : D.Z' ⟶ D.P := D.ι' ≫ pullback.snd g D.fP

@[reassoc (attr := simp)] lemma t_π : D.t ≫ D.π = D.U.ι := by
  rw [π, t_ι'_assoc, γ_fst]

@[reassoc (attr := simp)] lemma t_h : D.t ≫ D.h = D.gU := by
  rw [h, t_ι'_assoc, γ_snd]

lemma π_g : D.π ≫ g = D.h ≫ D.fP := by
  rw [π, h, Category.assoc, Category.assoc, pullback.condition]

instance isProjectiveMorphism_π : IsProjectiveMorphism D.π :=
  have := isProjectiveMorphism_pullback_fst g D.fP
  isProjectiveMorphism_of_isClosedImmersion_comp D.ι' _

instance isProper_π : IsProper D.π := IsProjectiveMorphism.isProper D.π

variable [IsProper g]

instance isProper_h : IsProper D.h :=
  have : IsProper (D.h ≫ D.fP) := by rw [← π_g]; infer_instance
  IsProper.of_comp D.h D.fP

variable [QuasiSeparatedSpace S]

theorem quasiSeparatedSpace_pullback : QuasiSeparatedSpace ↥(pullback g D.fP : Scheme.{u}) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst g D.fP ≫ g)

instance quasiCompact_γ : QuasiCompact D.γ := by
  have := D.quasiSeparatedSpace_pullback
  infer_instance

instance isOpenImmersion_t : IsOpenImmersion D.t := inferInstance

instance isDominant_t : IsDominant D.t := inferInstance

instance isIntegral_Z' [IsIntegral Z] : IsIntegral D.Z' := isIntegral_image D.γ


section Pieces

variable [IsIntegral Z]

/-- `V i := (u i).opensRange`, the `i`-th piece of the cover as an open of `Z`. -/
abbrev V (i : D.ι) : Z.Opens := (D.u i).opensRange

/-- `Z'_i := π ⁻¹ᵁ V i`. -/
abbrev Zi (i : D.ι) : D.Z'.Opens := D.π ⁻¹ᵁ D.V i

/-- `O i := p i ⁻¹ᵁ (e i).opensRange`, the open of `P` over which `Z'_i` lives. -/
abbrev O (i : D.ι) : D.P.Opens := D.p i ⁻¹ᵁ (D.e i).opensRange

/-- `a i : Z'_i ⟶ W i`, the restriction of `π` over the piece `W i`. -/
def a (i : D.ι) : (D.Zi i : Scheme.{u}) ⟶ D.W i := (D.π ∣_ D.V i) ≫ (D.u i).isoOpensRange.inv

@[reassoc] lemma a_u (i : D.ι) : D.a i ≫ D.u i = (D.Zi i).ι ≫ D.π := by
  rw [a, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]

instance isProper_a (i : D.ι) : IsProper (D.a i) := by
  have := isProper_of_isIso (D.u i).isoOpensRange.inv
  unfold a
  infer_instance

lemma t_mem_Zi (i : D.ι) (x : (D.U : Scheme.{u})) : D.t x ∈ D.Zi i := by
  have : (D.s i ≫ D.u i) x ∈ D.V i := ⟨D.s i x, by rw [Scheme.Hom.comp_apply]⟩
  rwa [D.hs i, ← D.t_π, Scheme.Hom.comp_apply] at this

lemma t_range_le (i : D.ι) : Set.range D.t ⊆ Set.range (D.Zi i).ι := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨D.t x, D.t_mem_Zi i x⟩, rfl⟩

/-- `t' i : U ⟶ Z'_i`, the open immersion `t` restricted to `Z'_i`. -/
def t' (i : D.ι) : (D.U : Scheme.{u}) ⟶ D.Zi i := IsOpenImmersion.lift (D.Zi i).ι D.t (D.t_range_le i)

@[reassoc (attr := simp)] lemma t'_ι (i : D.ι) : D.t' i ≫ (D.Zi i).ι = D.t :=
  IsOpenImmersion.lift_fac _ _ _

instance isDominant_t' (i : D.ι) : IsDominant (D.t' i) := by
  constructor
  have h1 : Dense ((D.Zi i).ι ⁻¹' Set.range D.t) :=
    D.t.denseRange.preimage (D.Zi i).ι.isOpenEmbedding.isOpenMap
  have hset : Set.range (D.t' i) = (D.Zi i).ι ⁻¹' Set.range D.t := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [← D.t'_ι i, Scheme.Hom.comp_apply]⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (D.Zi i).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, D.t'_ι i, hx]
  show Dense (Set.range (D.t' i))
  rw [hset]
  exact h1

@[reassoc] lemma t'_a (i : D.ι) : D.t' i ≫ D.a i = D.s i := by
  rw [← cancel_mono (D.u i), Category.assoc, a_u, t'_ι_assoc, t_π, D.hs i]

/-- The two morphisms `Z'_i ⟶ Zc i` (through `W i` and through `P`) agree: they agree on the dense open
`U`, `Z'_i` is reduced and `Zc i` is separated over `S`. -/
lemma a_e (i : D.ι) : D.a i ≫ D.e i = (D.Zi i).ι ≫ D.h ≫ D.p i := by
  refine ext_of_isDominant_of_isSeparated (D.f i) ?_ (D.t' i) ?_
  · simp only [Category.assoc, D.hef i, a_u_assoc, D.hp i, ← π_g]
  · rw [t'_a_assoc, t'_ι_assoc, t_h_assoc, D.hgU i]

/-- `k i : Z'_i ⟶ Γ_i = W i ×_{Zc i} P`, the factorization of `h` on `Z'_i` through the graph of `p i`. -/
def k (i : D.ι) : (D.Zi i : Scheme.{u}) ⟶ pullback (D.e i) (D.p i) :=
  pullback.lift (D.a i) ((D.Zi i).ι ≫ D.h) (D.a_e i)

@[reassoc (attr := simp)] lemma k_fst (i : D.ι) : D.k i ≫ pullback.fst (D.e i) (D.p i) = D.a i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma k_snd (i : D.ι) :
    D.k i ≫ pullback.snd (D.e i) (D.p i) = (D.Zi i).ι ≫ D.h :=
  pullback.lift_snd _ _ _

lemma m_cond (i : D.ι) :
    (pullback.fst (D.e i) (D.p i) ≫ D.u i) ≫ g = pullback.snd (D.e i) (D.p i) ≫ D.fP := by
  rw [Category.assoc, ← D.hef i, ← D.hp i, pullback.condition_assoc]

/-- `m i : Γ_i ⟶ Z ×_S P`. -/
def m (i : D.ι) : pullback (D.e i) (D.p i) ⟶ pullback g D.fP :=
  pullback.lift (pullback.fst _ _ ≫ D.u i) (pullback.snd _ _) (D.m_cond i)

lemma k_m (i : D.ι) : D.k i ≫ D.m i = (D.Zi i).ι ≫ D.ι' := by
  apply pullback.hom_ext
  · simp only [m, Category.assoc, pullback.lift_fst, k_fst_assoc, a_u]
    rfl
  · simp only [m, Category.assoc, pullback.lift_snd, k_snd]
    rfl

instance isImmersion_k (i : D.ι) : IsImmersion (D.k i) := by
  have : IsImmersion (D.k i ≫ D.m i) := by rw [k_m]; infer_instance
  exact IsImmersion.of_comp _ (D.m i)

instance isSeparated_p (i : D.ι) : IsSeparated (D.p i) := by
  have : IsSeparated (D.p i ≫ D.f i) := by rw [D.hp i]; infer_instance
  exact IsSeparated.of_comp (D.p i) (D.f i)

instance isProper_k (i : D.ι) : IsProper (D.k i) := by
  have : IsProper (D.k i ≫ pullback.fst (D.e i) (D.p i)) := by rw [k_fst]; infer_instance
  exact IsProper.of_comp _ (pullback.fst (D.e i) (D.p i))

lemma range_snd (i : D.ι) : Set.range (pullback.snd (D.e i) (D.p i)) = Set.range (D.O i).ι := by
  rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.range_ι]

/-- `Γ_i ≅ O_i`: the graph of `p i` over `(e i).opensRange` is the open `O i` of `P`. -/
def ψ (i : D.ι) : pullback (D.e i) (D.p i) ≅ (D.O i : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (pullback.snd (D.e i) (D.p i)) (D.O i).ι (D.range_snd i)

@[reassoc (attr := simp)] lemma ψ_hom_ι (i : D.ι) :
    (D.ψ i).hom ≫ (D.O i).ι = pullback.snd (D.e i) (D.p i) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma Zi_le (i : D.ι) : D.Zi i ≤ D.h ⁻¹ᵁ D.O i := by
  intro y hy
  have h2 := congrArg (fun φ : (D.Zi i : Scheme.{u}) ⟶ D.P => φ ⟨y, hy⟩) (D.k_snd i).symm
  simp only at h2
  have : D.h y ∈ Set.range (pullback.snd (D.e i) (D.p i)) := ⟨D.k i ⟨y, hy⟩, h2.symm⟩
  rwa [D.range_snd i, Scheme.Opens.range_ι] at this

/-- **The key identity** `h ⁻¹ᵁ O i = Z'_i`: the open immersion `Z'_i ⟶ h ⁻¹ᵁ O i` is proper (its composite
with `h ∣_ O i` is `k i` followed by the isomorphism `Γ_i ≅ O_i`, and `h ∣_ O i` is separated), has nonempty
source (it contains `U`) and irreducible target (an open of the integral `Z'`), hence is an isomorphism. -/
lemma preimage_O (i : D.ι) : D.h ⁻¹ᵁ D.O i = D.Zi i := by
  let φ : (D.Zi i : Scheme.{u}) ⟶ (D.h ⁻¹ᵁ D.O i : Scheme.{u}) := D.Z'.homOfLE (D.Zi_le i)
  have hφ : φ ≫ (D.h ∣_ D.O i) = D.k i ≫ (D.ψ i).hom := by
    rw [← cancel_mono (D.O i).ι, Category.assoc, Category.assoc, morphismRestrict_ι, ψ_hom_ι, k_snd,
      Scheme.homOfLE_ι_assoc]
  have h1 : IsProper (φ ≫ (D.h ∣_ D.O i)) := by
    rw [hφ]
    have := isProper_of_isIso (D.ψ i).hom
    infer_instance
  have h2 : IsProper φ := IsProper.of_comp φ (D.h ∣_ D.O i)
  have h3 : PreirreducibleSpace (D.h ⁻¹ᵁ D.O i) := preirreducibleSpace_opens _
  have h4 : Nonempty (D.Zi i) := ⟨D.t' i (Classical.arbitrary D.U)⟩
  have h5 : IsIso φ := isIso_of_isOpenImmersion_of_isProper φ
  have hr : Set.range (D.Zi i).ι = Set.range (D.h ⁻¹ᵁ D.O i).ι := by
    rw [← D.Z'.homOfLE_ι (D.Zi_le i), Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      φ.surjective.range_eq, Set.image_univ]
  apply Opens.ext
  rw [← Scheme.Opens.range_ι, ← Scheme.Opens.range_ι, hr]

lemma preimage_iSup_O : D.h ⁻¹ᵁ (⨆ i, D.O i) = ⊤ := by
  rw [Scheme.Hom.preimage_iSup]
  simp_rw [preimage_O]
  show ⨆ i, D.π ⁻¹ᵁ D.V i = ⊤
  rw [← Scheme.Hom.preimage_iSup, D.hcover, Scheme.Hom.preimage_top]

instance isImmersion_h : IsImmersion D.h := by
  refine isImmersion_of_preimage_cover D.h D.O D.preimage_iSup_O fun i => ?_
  rw [preimage_O, ← k_snd]
  infer_instance

instance isClosedImmersion_h : IsClosedImmersion D.h := isClosedImmersion_of_isImmersion_of_isProper D.h

/-- `π ≫ g : Z' ⟶ S` is projective: `Z'` is a closed subscheme of the projective `S`-scheme `P`. -/
theorem isProjectiveMorphism_π_g : IsProjectiveMorphism (D.π ≫ g) := by
  rw [π_g]
  exact isProjectiveMorphism_of_isClosedImmersion_comp D.h D.fP

/-- `π` is an isomorphism over `U`. -/
theorem isIso_π_restrict : IsIso (D.π ∣_ D.U) := by
  have hrange : Set.range D.t ⊆ Set.range (D.π ⁻¹ᵁ D.U).ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨D.t x, ?_⟩, rfl⟩
    show D.π (D.t x) ∈ D.U
    rw [← Scheme.Hom.comp_apply, t_π]
    exact x.2
  let τ : (D.U : Scheme.{u}) ⟶ (D.π ⁻¹ᵁ D.U : Scheme.{u}) := IsOpenImmersion.lift _ D.t hrange
  have hτ : τ ≫ (D.π ∣_ D.U) = 𝟙 _ := by
    rw [← cancel_mono D.U.ι, Category.assoc, morphismRestrict_ι, Category.id_comp,
      IsOpenImmersion.lift_fac_assoc, t_π]
  have h1 : IsProper (τ ≫ (D.π ∣_ D.U)) := by rw [hτ]; exact isProper_of_isIso _
  have h2 : IsProper τ := IsProper.of_comp τ (D.π ∣_ D.U)
  have h3 : PreirreducibleSpace (D.π ⁻¹ᵁ D.U) := preirreducibleSpace_opens _
  have h4 : IsIso τ := isIso_of_isOpenImmersion_of_isProper τ
  have h5 : IsIso (τ ≫ (D.π ∣_ D.U)) := by rw [hτ]; infer_instance
  exact IsIso.of_isIso_comp_left τ (D.π ∣_ D.U)

include D in
/-- **Chow's lemma, geometric assembly** (Stacks 0200 proof over a base `S`): from the data `D : ChowSetup g`
we get `Z'` and `π : Z' ⟶ Z` projective with `π ≫ g` projective and `π` an isomorphism over the nonempty
open `U`. -/
theorem exists_projective_birational :
    ∃ (Z' : Scheme.{u}) (π : Z' ⟶ Z), IsProjectiveMorphism π ∧ IsProjectiveMorphism (π ≫ g) ∧
      ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ IsIso (π ∣_ U) :=
  ⟨D.Z', D.π, inferInstance, D.isProjectiveMorphism_π_g, D.U, D.hUne, D.isIso_π_restrict⟩

end Pieces

end ChowSetup

end AlgebraicGeometry

end
