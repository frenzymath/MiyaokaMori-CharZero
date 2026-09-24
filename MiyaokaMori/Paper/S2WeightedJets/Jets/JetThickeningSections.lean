import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty

/-! # Sections of the jet thickening

Sections of the thickening `W ×_k D_r`: the parameter `t ∈ Γ(W ×_k D_r, ⊤)`, the ring homomorphism
`Γ(W, V)[t]/(t^{r+1}) → Γ(W ×_k D_r, pr⁻¹V)` (coefficients pulled back along the projection, `t ↦` the
parameter), and the fact that it is bijective (`D_r` is finite free over `k`). In other words, functions on
`W ×_k Spec k[t]/(t^{r+1})` are truncated polynomials (§2 of the paper).

Implementation note: `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with
`jetProjection_surjective` (so that `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and
`Ideal.Quotient.lift_mk` is rewritten with `erw` (it matches only up to unfolding `AdjoinRoot`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The parameter `t` on the thickening `W ×_k D_r`: the pullback along the second projection of the coordinate
of `D_r = Spec k[t]/(t^{r+1})`. -/

noncomputable def jetThickening.parameter {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] : Γ(jetThickening (k := k) r W, ⊤) :=
  (CategoryTheory.Limits.pullback.snd (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
      (MiyaokaMori.Jet.jetProjection k r Polynomial.X))

/-- The parameter satisfies `t^{r+1} = 0`: `t` is the image under a ring homomorphism of the coordinate
`[X] ∈ k[X]/(X^{r+1})` of `D_r`, and `[X]^{r+1} = [X^{r+1}] = 0`. -/

theorem jetThickening.parameter_pow_succ {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetThickening.parameter (k := k) r W ^ (r + 1) = 0 := by
  have h : MiyaokaMori.Jet.jetProjection k r Polynomial.X ^ (r + 1) = 0 :=
    (map_pow _ _ _).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))
  have h2 : (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
        (MiyaokaMori.Jet.jetProjection k r Polynomial.X) ^ (r + 1) = 0 :=
    (map_pow _ _ _).symm.trans ((congrArg _ h).trans (map_zero _))
  exact (map_pow _ _ _).symm.trans ((congrArg _ h2).trans (map_zero _))

/-- Well-definedness of `sectionsHom`: `eval₂` (coefficients pulled back along the projection,
`X ↦ t|_{pr⁻¹V}`) vanishes on the truncation ideal `(X^{r+1})`, since it sends the generator `X^{r+1}` to
`(t|)^{r+1} = (t^{r+1})| = 0` (`parameter_pow_succ`). -/

theorem jetThickening.sectionsHom_wellDefined {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (V : W.Opens) :
    ∀ a ∈ MiyaokaMori.Jet.truncationIdeal Γ(W, V) r,
      (Polynomial.eval₂RingHom ((jetThickeningProj (k := k) r W).app V).hom
        (((jetThickening (k := k) r W).presheaf.map (CategoryTheory.homOfLE le_top).op).hom
          (jetThickening.parameter (k := k) r W))) a = 0 := by
  intro a ha
  have h : MiyaokaMori.Jet.truncationIdeal Γ(W, V) r ≤ RingHom.ker
      (Polynomial.eval₂RingHom ((jetThickeningProj (k := k) r W).app V).hom
        (((jetThickening (k := k) r W).presheaf.map (CategoryTheory.homOfLE le_top).op).hom
          (jetThickening.parameter (k := k) r W))) := by
    rw [MiyaokaMori.Jet.truncationIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    rw [map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, ← map_pow,
      jetThickening.parameter_pow_succ, map_zero]
  exact h ha

/-- The ring homomorphism `Γ(W, V)[t]/(t^{r+1}) → Γ(W ×_k D_r, pr⁻¹V)`: coefficients are pulled back along the
projection and `t` goes to the parameter (`t^{r+1} = 0` by `sectionsHom_wellDefined`). -/

noncomputable def jetThickening.sectionsHom {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (V : W.Opens) :
    MiyaokaMori.Jet.TruncatedJetRing Γ(W, V) r →+*
      Γ(jetThickening (k := k) r W, jetThickeningProj (k := k) r W ⁻¹ᵁ V) :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((jetThickeningProj (k := k) r W).app V).hom
      (((jetThickening (k := k) r W).presheaf.map (CategoryTheory.homOfLE le_top).op).hom
        (jetThickening.parameter (k := k) r W)))
    (jetThickening.sectionsHom_wellDefined (k := k) r W V)

/- Proof of `sectionsHom_bijective`: on affine opens use Mathlib's "sections of a fiber product form a pushout"
   (`pushoutSection`); on general opens glue, both sides being sheaves (the right side coefficientwise). -/

section SectionsAux

open AlgebraicGeometry

/-- The algebraic core: a pushout square `K → R`, `K → A` in `CommRingCat` with `A ≅ k[t]/(t^{r+1})` and `K ≅ k`
gives `R[t]/(t^{r+1}) ≅ P`. The inverse comes from the universal property of the pushout (`R` via `eta`, `A` via
`σ` with coefficients changed along `k → R`); the two composites are checked with `Polynomial.ringHom_ext` and
`IsPushout.hom_ext`. -/
private theorem jetThickening.sectionsAux.alg {K R A P : CommRingCat.{u}} {f : K ⟶ R} {g : K ⟶ A} {inl : R ⟶ P} {inr : A ⟶ P}
    (h : IsPushout f g inl inr) (k : Type u) [CommRing k] (r : ℕ) (γ : k ≃+* K)
    (σ : A ≃+* MiyaokaMori.Jet.TruncatedJetRing k r)
    (hσ : ∀ c : k, σ (g.hom (γ c)) = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r c)
    (inl' : R →+* P) (T' : P) (hinl : inl.hom = inl')
    (hT : inr.hom (σ.symm (MiyaokaMori.Jet.jetProjection k r Polynomial.X)) = T')
    (hwd : ∀ a ∈ MiyaokaMori.Jet.truncationIdeal R r, (Polynomial.eval₂RingHom inl' T') a = 0) :
    Function.Bijective (Ideal.Quotient.lift (MiyaokaMori.Jet.truncationIdeal R r)
      (Polynomial.eval₂RingHom inl' T') hwd) := by
  subst hinl hT
  set Φ := Ideal.Quotient.lift (MiyaokaMori.Jet.truncationIdeal R r)
      (Polynomial.eval₂RingHom inl.hom
        (inr.hom (σ.symm (MiyaokaMori.Jet.jetProjection k r Polynomial.X)))) hwd with hΦ
  let ρ : k →+* R := f.hom.comp γ.toRingHom
  have hc : f ≫ CommRingCat.ofHom (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta (R := R) r) =
      g ≫ CommRingCat.ofHom ((MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r ρ).comp σ.toRingHom) := by
    ext x
    obtain ⟨c, rfl⟩ := γ.surjective x
    have := congrArg (fun φ => φ c) (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_eta r ρ)
    simp only [RingHom.comp_apply] at this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ]
    exact this.symm
  let Ψ : P ⟶ CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing R r) := h.desc _ _ hc
  have hΨl : ∀ a : R, Ψ.hom (inl.hom a) = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r a := fun a =>
    congrArg (fun φ => φ.hom a) (h.inl_desc _ _ hc)
  have hΨr : ∀ z : A, Ψ.hom (inr.hom z) = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r ρ (σ z) :=
    fun z => congrArg (fun φ => φ.hom z) (h.inr_desc _ _ hc)
  have hΦproj : ∀ q : Polynomial R, Φ (MiyaokaMori.Jet.jetProjection R r q) =
      Polynomial.eval₂ inl.hom (inr.hom (σ.symm (MiyaokaMori.Jet.jetProjection k r Polynomial.X))) q :=
    fun q => rfl
  -- Ψ ∘ Φ = id
  have h1 : (Ψ.hom.comp Φ) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro a
      show Ψ.hom (Φ (MiyaokaMori.Jet.jetProjection R r (Polynomial.C a))) = _
      rw [hΦproj, Polynomial.eval₂_C, hΨl]; rfl
    · show Ψ.hom (Φ (MiyaokaMori.Jet.jetProjection R r Polynomial.X)) = _
      rw [hΦproj, Polynomial.eval₂_X, hΨr, RingEquiv.apply_symm_apply,
        MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection, Polynomial.map_X]; rfl
  -- Φ ∘ Ψ = id
  have key : ∀ q : Polynomial k,
      Φ (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r ρ (MiyaokaMori.Jet.jetProjection k r q)) =
        inr.hom (σ.symm (MiyaokaMori.Jet.jetProjection k r q)) := by
    intro q
    have : (Φ.comp ((MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r ρ).comp
        (MiyaokaMori.Jet.jetProjection k r))) =
        (inr.hom.comp (σ.symm.toRingHom.comp (MiyaokaMori.Jet.jetProjection k r))) := by
      apply Polynomial.ringHom_ext
      · intro c
        show Φ (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r ρ
          (MiyaokaMori.Jet.jetProjection k r (Polynomial.C c))) =
          inr.hom (σ.symm (MiyaokaMori.Jet.jetProjection k r (Polynomial.C c)))
        rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection, Polynomial.map_C, hΦproj,
          Polynomial.eval₂_C]
        have e1 : σ.symm (MiyaokaMori.Jet.jetProjection k r (Polynomial.C c)) = g.hom (γ c) := by
          rw [RingEquiv.symm_apply_eq, hσ]; rfl
        rw [e1]
        exact congrArg (fun φ => φ.hom (γ c)) h.w
      · show Φ (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r ρ
          (MiyaokaMori.Jet.jetProjection k r Polynomial.X)) = _
        rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection, Polynomial.map_X, hΦproj,
          Polynomial.eval₂_X]; rfl
    exact congrArg (fun φ => φ q) this
  have h2 : Ψ ≫ CommRingCat.ofHom Φ = 𝟙 P := by
    apply h.hom_ext
    · ext a
      show Φ (Ψ.hom (inl.hom a)) = inl.hom a
      rw [hΨl]
      show Φ (MiyaokaMori.Jet.jetProjection R r (Polynomial.C a)) = _
      rw [hΦproj, Polynomial.eval₂_C]
    · ext z
      show Φ (Ψ.hom (inr.hom z)) = inr.hom z
      rw [hΨr]
      obtain ⟨q, hq⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (σ z)
      have hq' : σ z = MiyaokaMori.Jet.jetProjection k r q := hq.symm
      rw [hq', key, ← hq', RingEquiv.symm_apply_apply]
  refine ⟨fun x y hxy => ?_, fun p => ⟨Ψ.hom p, ?_⟩⟩
  · have := congrArg Ψ.hom hxy
    have e := fun t => congrArg (fun φ => φ t) h1
    simp only [RingHom.comp_apply, RingHom.id_apply] at e
    rwa [e, e] at this
  · exact congrArg (fun φ => φ.hom p) h2

/-- `sectionsHom` is bijective on an affine open `V`: Mathlib's `isIso_pushoutSection_of_isAffineOpen` shows that
`Γ(pr⁻¹V)` is the pushout of `Γ(V)` and `Γ(D_r)` over `Γ(Spec k)`; then apply `alg`. -/
private theorem jetThickening.sectionsAux.affine {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (V : W.Opens) (hV : IsAffineOpen V) :
    Function.Bijective (jetThickening.sectionsHom (k := k) r W V) := by
  have H := IsPullback.of_hasPullback (W ↘ Spec (CommRingCat.of k)) (jetBase k r ↘ Spec (CommRingCat.of k))
  have hUST : (⊤ : (jetBase k r).Opens) ≤ (jetBase k r ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := le_top
  have hUSX : V ≤ (W ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := le_top
  have hUY : jetThickeningProj (k := k) r W ⁻¹ᵁ V =
      pullback.fst (W ↘ Spec (CommRingCat.of k)) (jetBase k r ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ V ⊓
      pullback.snd (W ↘ Spec (CommRingCat.of k)) (jetBase k r ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := by
    unfold jetThickeningProj
    rw [Scheme.Hom.preimage_top, inf_top_eq]
    rfl
  have : IsAffine (jetBase k r) := by unfold jetBase; infer_instance
  have hiso := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY (isAffineOpen_top _)
    (isAffineOpen_top (jetBase k r)) hV
  have hpo := (isIso_pushoutSection_iff H hUST hUSX hUY).mp hiso
  have hσ : ∀ c : k, (Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).commRingCatIsoToRingEquiv
      ((Scheme.Hom.appLE (jetBase k r ↘ Spec (CommRingCat.of k)) ⊤ ⊤ hUST).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv c)) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r c := by
    intro c
    have nat := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap k (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r)))
    have nat' := congrArg (fun φ => (Scheme.ΓSpecIso
      (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).hom.hom (φ.hom c)) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at nat'
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id] at nat'
    exact nat'.symm
  exact jetThickening.sectionsAux.alg hpo k r (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).commRingCatIsoToRingEquiv
    hσ ((jetThickeningProj (k := k) r W).app V).hom
    (((jetThickening (k := k) r W).presheaf.map (CategoryTheory.homOfLE le_top).op).hom
      (jetThickening.parameter (k := k) r W))
    (congrArg CommRingCat.Hom.hom (Scheme.Hom.app_eq_appLE (jetThickeningProj (k := k) r W)).symm)
    rfl
    (jetThickening.sectionsHom_wellDefined (k := k) r W V)


private theorem jetThickening.sectionsAux.ext_coeff {S : Type u} [CommRing S] (r : ℕ)
    (x y : MiyaokaMori.Jet.TruncatedJetRing S r)
    (h : ∀ (n : ℕ) (hn : n ≤ r), MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn x =
      MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn y) : x = y := by
  -- `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; `rw [Ideal.Quotient.eq]` does not match its equalities,
  -- so use the restated `jetProjection_eq_iff`.
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective S r x
  obtain ⟨q, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective S r y
  rw [MiyaokaMori.Jet.jetProjection_eq_iff, Polynomial.X_pow_dvd_iff]
  intro d hd
  have := h d (Nat.lt_succ_iff.mp hd)
  rw [Polynomial.coeff_sub, sub_eq_zero]
  exact this

private theorem jetThickening.sectionsAux.coeff_map {S T : Type u} [CommRing S] [CommRing T] (r n : ℕ) (hn : n ≤ r) (φ : S →+* T)
    (p : MiyaokaMori.Jet.TruncatedJetRing S r) :
    MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r φ p) =
      φ (MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn p) := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  exact Polynomial.coeff_map _ n

variable {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
  [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

private theorem jetThickening.sectionsAux.preimage_mono {V V' : W.Opens} (h : V' ≤ V) :
    jetThickeningProj (k := k) r W ⁻¹ᵁ V' ≤ jetThickeningProj (k := k) r W ⁻¹ᵁ V :=
  fun _ hx => h hx

private theorem jetThickening.sectionsAux.restrict {V V' : W.Opens} (h : V' ≤ V)
    (p : MiyaokaMori.Jet.TruncatedJetRing Γ(W, V) r) :
    jetThickening.sectionsHom (k := k) r W V'
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (W.presheaf.map (homOfLE h).op).hom p) =
      ((jetThickening (k := k) r W).presheaf.map (homOfLE (jetThickening.sectionsAux.preimage_mono (k := k) r W h)).op).hom
        (jetThickening.sectionsHom (k := k) r W V p) := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection]
  unfold jetThickening.sectionsHom
  rw [MiyaokaMori.Jet.lift_jetProjection, MiyaokaMori.Jet.lift_jetProjection]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
  rw [Polynomial.hom_eval₂]
  congr 1
  · ext a
    have := (jetThickeningProj (k := k) r W).naturality (homOfLE h).op
    exact congrArg (fun φ => φ.hom a) this
  · rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl

private theorem jetThickening.sectionsAux.affine_cover (V : W.Opens) :
    V ≤ ⨆ U : {U : W.affineOpens // U.1 ≤ V}, U.1.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

/-- Injectivity on an arbitrary open set: reduce to the affine case coefficient by coefficient, using the
separatedness of the sheaf `O_W` on an affine open cover. -/
private theorem jetThickening.sectionsAux.injective (V : W.Opens) :
    Function.Injective (jetThickening.sectionsHom (k := k) r W V) := by
  intro p q hpq
  apply jetThickening.sectionsAux.ext_coeff
  intro n hn
  fapply W.sheaf.eq_of_locally_eq' (fun U : {U : W.affineOpens // U.1 ≤ V} => U.1.1) V
    (fun U => homOfLE U.2) (jetThickening.sectionsAux.affine_cover W V)
  intro U
  have h1 : jetThickening.sectionsHom (k := k) r W U.1.1
      (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (W.presheaf.map (homOfLE U.2).op).hom p) =
      jetThickening.sectionsHom (k := k) r W U.1.1
      (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (W.presheaf.map (homOfLE U.2).op).hom q) := by
    rw [jetThickening.sectionsAux.restrict, jetThickening.sectionsAux.restrict, hpq]
  have h2 := congrArg (MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn)
    ((jetThickening.sectionsAux.affine (k := k) r W U.1.1 U.1.2).1 h1)
  rw [jetThickening.sectionsAux.coeff_map, jetThickening.sectionsAux.coeff_map] at h2
  exact h2

private theorem jetThickening.sectionsAux.coeff_sum {S : Type u} [CommRing S] (r : ℕ) (c : ℕ → S) (n : ℕ) (hn : n ≤ r) :
    MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn (MiyaokaMori.Jet.jetProjection S r
      (∑ m ∈ Finset.range (r + 1), Polynomial.monomial m (c m))) = c n := by
  show (∑ m ∈ Finset.range (r + 1), Polynomial.monomial m (c m)).coeff n = c n
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (r + 1)) n, if_pos (Finset.mem_range.mpr (by omega))]

/-- Surjectivity on an arbitrary open set: take preimages on affine opens, which agree on overlaps by
injectivity; glue coefficient by coefficient (`O_W` is a sheaf), and verify with the separatedness of
`O_{W ×_k D_r}`. -/
private theorem jetThickening.sectionsAux.surjective (V : W.Opens) :
    Function.Surjective (jetThickening.sectionsHom (k := k) r W V) := by
  intro x
  let ι := {U : W.affineOpens // U.1 ≤ V}
  let J := jetThickening (k := k) r W
  have hp : ∀ U : ι, ∃ p, jetThickening.sectionsHom (k := k) r W U.1.1 p =
      (J.presheaf.map (homOfLE (jetThickening.sectionsAux.preimage_mono (k := k) r W U.2)).op).hom x :=
    fun U => (jetThickening.sectionsAux.affine (k := k) r W U.1.1 U.1.2).2 _
  choose p hp using hp
  have hc : ∀ n : ℕ, ∃ c : Γ(W, V), ∀ (hn : n ≤ r) (U : ι),
      (W.presheaf.map (homOfLE U.2).op).hom c =
        MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn (p U) := by
    intro n
    by_cases hn : n ≤ r
    · obtain ⟨c, hc, -⟩ := W.sheaf.existsUnique_gluing' (fun U : ι => U.1.1) V
        (fun U => homOfLE U.2) (jetThickening.sectionsAux.affine_cover W V)
        (fun U => MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn (p U)) (by
          intro U U'
          have e : MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r
              (W.presheaf.map (homOfLE (inf_le_left : U.1.1 ⊓ U'.1.1 ≤ U.1.1)).op).hom (p U) =
              MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r
              (W.presheaf.map (homOfLE (inf_le_right : U.1.1 ⊓ U'.1.1 ≤ U'.1.1)).op).hom (p U') := by
            apply jetThickening.sectionsAux.injective (k := k) r W
            rw [jetThickening.sectionsAux.restrict, jetThickening.sectionsAux.restrict, hp, hp, ← CategoryTheory.comp_apply,
              ← CategoryTheory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
            rfl
          have e' := congrArg (MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn) e
          rw [jetThickening.sectionsAux.coeff_map, jetThickening.sectionsAux.coeff_map] at e'
          exact e')
      exact ⟨c, fun _ U => hc U⟩
    · exact ⟨0, fun hn' => absurd hn' hn⟩
  choose c hc using hc
  refine ⟨MiyaokaMori.Jet.jetProjection _ r
    (∑ m ∈ Finset.range (r + 1), Polynomial.monomial m (c m)), ?_⟩
  fapply J.sheaf.eq_of_locally_eq' (fun U : ι => jetThickeningProj (k := k) r W ⁻¹ᵁ U.1.1)
    (jetThickeningProj (k := k) r W ⁻¹ᵁ V) (fun U => homOfLE (jetThickening.sectionsAux.preimage_mono (k := k) r W U.2))
  · intro y hy
    obtain ⟨U, hU⟩ := Opens.mem_iSup.mp (jetThickening.sectionsAux.affine_cover W V hy)
    exact Opens.mem_iSup.mpr ⟨U, hU⟩
  · intro U
    refine (jetThickening.sectionsAux.restrict (k := k) r W U.2 _).symm.trans (Eq.trans ?_ (hp U))
    congr 1
    apply jetThickening.sectionsAux.ext_coeff
    intro n hn
    rw [jetThickening.sectionsAux.coeff_map, jetThickening.sectionsAux.coeff_sum, hc]

end SectionsAux

/-- Sections of the thickening are truncated polynomials: `D_r → Spec k` is finite free, so
`pr_* O = O_W ⊗_k k[t]/(t^{r+1})`, and this holds on sections over every open set.
On affine opens Mathlib's `isIso_pushoutSection_of_isAffineOpen` gives the pushout square and algebraically
`R[t]/(t^{r+1}) = R ⊗_k k[t]/(t^{r+1})`; on general (not necessarily quasi-compact) opens glue coefficientwise
along an affine open cover. -/

theorem jetThickening.sectionsHom_bijective {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (V : W.Opens) :
    Function.Bijective (jetThickening.sectionsHom (k := k) r W V) :=
  ⟨jetThickening.sectionsAux.injective (k := k) r W V,
    jetThickening.sectionsAux.surjective (k := k) r W V⟩

end
