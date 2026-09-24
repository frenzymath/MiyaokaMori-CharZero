import MiyaokaMori.Paper.S2WeightedJets.Charts.JetAlgebraOfPolynomial
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlasReindex
import MiyaokaMori.AlgebraicGeometry.Varieties.EtaleChart
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetLocalGradedRingEquivEtaleInvariance

/-! # The local graded ring isomorphism of the jet algebra

On an affine open on which the cone tangent bundle is trivial, the jet algebra based at the seed
section is isomorphic, as a graded ring, to the weighted polynomial ring whose variables are the jet
coefficients of each order, and the structure map corresponds to the constant polynomials.

**Proof** (§2.2 of the paper, eq. (2.5); Ein–Mustaţă, *Jet schemes and
singularities*, Lemma 2.9).
Write `A = Γ(C, U)`, `B = Γ(Z, π⁻¹U)`, `ε : B → A` the augmentation `s^♯`; the sections ring of
the jet algebra on `U` is by definition `J_r(B, ε)` with the grading `BasedJetAlgebra.grading`
(both `rfl`: `(jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sections (affineSite U)` unfolds to
`CommRingCat.of (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r)` and its `grading` to
`BasedJetAlgebra.grading`).
1. `exists_etale_chart` gives an affine open `V` with `s(U) ⊆ V ⊆ π⁻¹U` and an
   étale `U`-morphism `φ : V → 𝔸^{n+1}_U`.  Put `B' = Γ(Z, V)`, `P = Γ(𝔸^{n+1}_U)`, with the
   augmentation `ε' = s^♯ : B' → A` and `ε₀ = ε' ∘ φ^♯ : P → A`.
2. The restriction `B → B'` is the ring map of the open immersion `V ⊆ π⁻¹U` between affine
   schemes, hence étale (`HasRingHomProperty.appLE` for `𝟙 Z`); `φ^♯ : P → B'` is étale because
   `φ` is (`HasRingHomProperty.appTop`).
3. Étale invariance of the based jet algebra (`BasedJetAlgebra.towerEquiv`,
   `JetLocalGradedRingEquivEtaleInvariance`): `J_r(B, ε) ≃ J_r(B', ε') ≃ J_r(P, ε₀)` as graded
   rings over `A`, compatible with the structure maps.
4. `P ≃ₐ[A] A[y_1, …, y_{n+1}]` (`AffineSpace.isoOfIsAffine`), so `J_r(P, ε₀) ≃ A[x_{q,i}]` with
   `x_{q,i}` of weight `q+1` and structure map `↦ C` (`BasedJetAlgebra.mvPolynomialEquiv`,
   `mem_grading_iff_isWeightedHomogeneous`, `mvPolynomialEquiv_algebraMap`).
5. Finally change the coefficients `A = Γ(C, U) ≅ Γ(U, ⊤)` (`topIso`, `MvPolynomial.mapEquiv`) and
   the index set `Fin r × ULift (Fin (n+1)) ≃ ULift (Fin (n+1) × Fin r)` (`jetIndexEquiv`,
   `MvPolynomial.renameEquiv`); both preserve weighted homogeneity
   (`IsWeightedHomogeneous.map_iff`, `IsWeightedHomogeneous.rename_of`) and `C`.
The zero-section property of the chart is not needed: the based jet algebra of a polynomial
algebra is a weighted polynomial algebra for every augmentation.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Weighted homogeneity is preserved and reflected by coefficient change along an injective
ring map. -/
theorem MvPolynomial.IsWeightedHomogeneous.map_iff {σ R S : Type*} [CommSemiring R]
    [CommSemiring S] {w : σ → ℕ} (f : R →+* S) (hf : Function.Injective f) {m : ℕ}
    (p : MvPolynomial σ R) :
    (MvPolynomial.map f p).IsWeightedHomogeneous w m ↔ p.IsWeightedHomogeneous w m := by
  constructor
  · intro h d hd
    exact h (by rw [MvPolynomial.coeff_map]; exact (map_ne_zero_iff f hf).mpr hd)
  · intro h d hd
    rw [MvPolynomial.coeff_map] at hd
    exact h ((map_ne_zero_iff f hf).mp hd)

/-- Reindexing of the jet coordinates to the spelling `ULift (Fin (n+1) × Fin r)` used by the
weighted projectivization. -/
def jetIndexEquiv (r n : ℕ) :
    Fin r × ULift.{u} (Fin (n + 1)) ≃ ULift.{u} (Fin (n + 1) × Fin r) where
  toFun qi := ⟨(qi.2.down, qi.1)⟩
  invFun iq := (iq.down.2, ⟨iq.down.1⟩)
  left_inv _ := rfl
  right_inv _ := rfl

theorem jetLocalGradedRingEquiv {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    [C.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C.toScheme ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s]
    (Zx : Z.left.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (r : ℕ)
    (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj
      (coneTangentBundle Z.hom s hs) ≅
        SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    ∃ e : (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sections
          (AlgebraicGeometry.Scheme.affineSite U) ≃+*
        MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(U.1.toScheme, ⊤),
      (∀ (m : ℕ) (a : (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sections
          (AlgebraicGeometry.Scheme.affineSite U)),
        a ∈ (jetGradedAffineAlgebra Z s hs r).grading
            (AlgebraicGeometry.Scheme.affineSite U) m ↔
          (e a).IsWeightedHomogeneous
            (fun iq : ULift.{u} (Fin (n + 1) × Fin r) ↦ (iq.down.2 : ℕ) + 1) m) ∧
      (∀ a : Γ(U.1.toScheme, ⊤),
        e ((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.unitHom
          (AlgebraicGeometry.Scheme.affineSite U) (U.1.topIso.hom a)) = MvPolynomial.C a) := by
  classical
  obtain ⟨V, hV, hsV, hVU, -, φ, hφet, hφover, -⟩ :=
    exists_etale_chart Z.hom s hs Zx hsZx n U htriv
  haveI : AlgebraicGeometry.IsAffine V.toScheme := hV
  haveI : AlgebraicGeometry.IsAffine U.1.toScheme := U.2
  -- Rings.  `A = Γ(C, U)`, `B = Γ(Z, π⁻¹U)`, `B' = Γ(Z, V)`, `P = Γ(𝔸^{n+1}_U, ⊤)`.
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  let ε := relativeJetScheme.augmentation Z s hs U.1
  let W : Z.left.Opens := Z.hom ⁻¹ᵁ U.1
  have hWaff : AlgebraicGeometry.IsAffineOpen W := U.2.preimage Z.hom
  -- `B → B'`: restriction along `V ⊆ π⁻¹U`.
  let res : Γ(Z.left, W) ⟶ Γ(Z.left, V) := Z.left.presheaf.map (homOfLE hVU).op
  letI algAB' : Algebra Γ(C.toScheme, U.1) Γ(Z.left, V) := (Z.hom.appLE U.1 V hVU).hom.toAlgebra
  letI algBB' : Algebra Γ(Z.left, W) Γ(Z.left, V) := res.hom.toAlgebra
  haveI : IsScalarTower Γ(C.toScheme, U.1) Γ(Z.left, W) Γ(Z.left, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hres : RingHom.Etale res.hom := by
    have h := AlgebraicGeometry.HasRingHomProperty.appLE (P := @AlgebraicGeometry.Etale)
      (𝟙 Z.left) inferInstance ⟨W, hWaff⟩ ⟨V, hV⟩ hVU
    have e : (𝟙 Z.left : Z.left ⟶ Z.left).appLE W V hVU = res := by
      simp only [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.id_app]
      rfl
    rwa [e] at h
  haveI : Algebra.FormallyEtale Γ(Z.left, W) Γ(Z.left, V) := hres.formallyEtale
  -- The augmentation of `B'`.
  have hε'comm : ∀ a : Γ(C.toScheme, U.1),
      (s.appLE V U.1 hsV).hom ((Z.hom.appLE U.1 V hVU).hom a) = a := by
    intro a
    have h1 : Z.hom.appLE U.1 V hVU ≫ s.appLE V U.1 hsV =
        (s ≫ Z.hom).appLE U.1 U.1 (hsV.trans ((Opens.map s.base).map (homOfLE hVU)).le) :=
      AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE s Z.hom U.1 V U.1 hVU hsV
    have h2 : ∀ (f : C.toScheme ⟶ C.toScheme) (hf : f = 𝟙 C.toScheme)
        (e : U.1 ≤ f ⁻¹ᵁ U.1), f.appLE U.1 U.1 e = 𝟙 _ := by
      intro f hf e
      subst hf
      simp only [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.id_app]
      exact C.toScheme.presheaf.map_id _
    rw [← CommRingCat.comp_apply, h1, h2 _ hs]
    rfl
  let ε' : Γ(Z.left, V) →ₐ[Γ(C.toScheme, U.1)] Γ(C.toScheme, U.1) :=
    { (s.appLE V U.1 hsV).hom with commutes' := hε'comm }
  have hε₁ : ∀ b : Γ(Z.left, W), ε' (algebraMap Γ(Z.left, W) Γ(Z.left, V) b) = ε b := by
    intro b
    show (s.appLE V U.1 hsV).hom (res.hom b) = (s.appLE W U.1 _).hom b
    rw [← CommRingCat.comp_apply, AlgebraicGeometry.Scheme.Hom.map_appLE]
  -- `J_r(B, ε) ≃ J_r(B', ε')`.
  let Φ₁ := BasedJetAlgebra.towerEquiv ε ε' hε₁ r
  -- `P → B'` through the étale chart.
  let 𝔸 := AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1))) U.1.toScheme
  let g : Γ(𝔸, ⊤) ⟶ Γ(Z.left, V) := φ.appTop ≫ V.topIso.hom
  let ι : Γ(C.toScheme, U.1) ⟶ Γ(𝔸, ⊤) := U.1.topIso.inv ≫ (𝔸 ↘ U.1.toScheme).appTop
  letI algAP : Algebra Γ(C.toScheme, U.1) Γ(𝔸, ⊤) := ι.hom.toAlgebra
  letI algPB' : Algebra Γ(𝔸, ⊤) Γ(Z.left, V) := g.hom.toAlgebra
  have h0 : (𝔸 ↘ U.1.toScheme).appTop ≫ φ.appTop =
      U.1.topIso.hom ≫ Z.hom.appLE U.1 V hVU ≫ V.topIso.inv := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, hφover]
    exact AlgebraicGeometry.Scheme.Hom.resLE_app_top Z.hom hVU
  have hιg : ι ≫ g = Z.hom.appLE U.1 V hVU := by
    show U.1.topIso.inv ≫ (𝔸 ↘ U.1.toScheme).appTop ≫ φ.appTop ≫ V.topIso.hom = _
    rw [← Category.assoc ((𝔸 ↘ U.1.toScheme).appTop), h0]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  haveI : IsScalarTower Γ(C.toScheme, U.1) Γ(𝔸, ⊤) Γ(Z.left, V) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show (Z.hom.appLE U.1 V hVU).hom a = g.hom (ι.hom a)
      rw [← hιg]; rfl
  have hg : RingHom.Etale g.hom :=
    (RingHom.Etale.respectsIso.cancel_right_isIso φ.appTop V.topIso.hom).mpr
      (AlgebraicGeometry.HasRingHomProperty.appTop (P := @AlgebraicGeometry.Etale) φ hφet)
  haveI : Algebra.FormallyEtale Γ(𝔸, ⊤) Γ(Z.left, V) := hg.formallyEtale
  let ε₀ : Γ(𝔸, ⊤) →ₐ[Γ(C.toScheme, U.1)] Γ(C.toScheme, U.1) :=
    ε'.comp (IsScalarTower.toAlgHom Γ(C.toScheme, U.1) Γ(𝔸, ⊤) Γ(Z.left, V))
  -- `J_r(P, ε₀) ≃ J_r(B', ε')`.
  let Φ₂ := BasedJetAlgebra.towerEquiv ε₀ ε' (fun _ => rfl) r
  -- `P ≃ₐ[A] A[y]`.
  let f₁ : MvPolynomial (ULift.{u} (Fin (n + 1))) Γ(U.1.toScheme, ⊤) →+* Γ(𝔸, ⊤) :=
    MvPolynomial.eval₂Hom ((𝔸 ↘ U.1.toScheme).appTop).hom
      (AlgebraicGeometry.AffineSpace.coord U.1.toScheme)
  have hf₁ : CommRingCat.ofHom f₁ =
      (AlgebraicGeometry.Scheme.ΓSpecIso _).inv ≫
        (AlgebraicGeometry.AffineSpace.isoOfIsAffine (ULift.{u} (Fin (n + 1)))
          U.1.toScheme).hom.appTop := by
    rw [AlgebraicGeometry.AffineSpace.isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]
  have hf₁bij : Function.Bijective f₁ := by
    have hiso1 : IsIso ((AlgebraicGeometry.AffineSpace.isoOfIsAffine (ULift.{u} (Fin (n + 1)))
        U.1.toScheme).hom.appTop) :=
      inferInstanceAs (IsIso ((AlgebraicGeometry.AffineSpace.isoOfIsAffine (ULift.{u} (Fin (n + 1)))
        U.1.toScheme).hom.app ⊤))
    have : IsIso (CommRingCat.ofHom f₁) := by rw [hf₁]; exact IsIso.comp_isIso
    exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom f₁)
  let e₁ : MvPolynomial (ULift.{u} (Fin (n + 1))) Γ(U.1.toScheme, ⊤) ≃+* Γ(𝔸, ⊤) :=
    RingEquiv.ofBijective f₁ hf₁bij
  let τ : Γ(U.1.toScheme, ⊤) ≃+* Γ(C.toScheme, U.1) := U.1.topIso.commRingCatIsoToRingEquiv
  let e₂ : MvPolynomial (ULift.{u} (Fin (n + 1))) Γ(U.1.toScheme, ⊤) ≃+*
      MvPolynomial (ULift.{u} (Fin (n + 1))) Γ(C.toScheme, U.1) :=
    MvPolynomial.mapEquiv _ τ
  have hβ : ∀ a : Γ(C.toScheme, U.1),
      (e₁.symm.trans e₂) (algebraMap Γ(C.toScheme, U.1) Γ(𝔸, ⊤) a) =
        algebraMap Γ(C.toScheme, U.1) (MvPolynomial (ULift.{u} (Fin (n + 1))) Γ(C.toScheme, U.1)) a := by
    intro a
    have h1 : e₁ (MvPolynomial.C (τ.symm a)) = algebraMap Γ(C.toScheme, U.1) Γ(𝔸, ⊤) a := by
      show f₁ (MvPolynomial.C (U.1.topIso.inv.hom a)) = ι.hom a
      rw [MvPolynomial.eval₂Hom_C]
      rfl
    rw [RingEquiv.trans_apply, ← h1, RingEquiv.symm_apply_apply]
    show MvPolynomial.map (τ : Γ(U.1.toScheme, ⊤) →+* Γ(C.toScheme, U.1))
      (MvPolynomial.C (τ.symm a)) = MvPolynomial.C a
    rw [MvPolynomial.map_C]
    congr 1
    exact τ.apply_symm_apply a
  let β : Γ(𝔸, ⊤) ≃ₐ[Γ(C.toScheme, U.1)]
      MvPolynomial (ULift.{u} (Fin (n + 1))) Γ(C.toScheme, U.1) :=
    AlgEquiv.ofRingEquiv hβ
  -- `J_r(P, ε₀) ≃ A[x_{q,i}]`.
  let e₃ := BasedJetAlgebra.mvPolynomialEquiv ε₀ r β
  -- Coefficient and index changes.
  let e₄ : MvPolynomial (Fin r × ULift.{u} (Fin (n + 1))) Γ(C.toScheme, U.1) ≃+*
      MvPolynomial (Fin r × ULift.{u} (Fin (n + 1))) Γ(U.1.toScheme, ⊤) :=
    MvPolynomial.mapEquiv _ τ.symm
  let e₅ : MvPolynomial (Fin r × ULift.{u} (Fin (n + 1))) Γ(U.1.toScheme, ⊤) ≃+*
      MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(U.1.toScheme, ⊤) :=
    (MvPolynomial.renameEquiv Γ(U.1.toScheme, ⊤) (jetIndexEquiv r n)).toRingEquiv
  have hΦ₁u : ∀ x : Γ(C.toScheme, U.1),
      Φ₁ (algebraMap Γ(C.toScheme, U.1) (BasedJetAlgebra ε r) x) = algebraMap _ _ x :=
    BasedJetAlgebra.towerEquiv_algebraMap ε ε' hε₁ r
  have hΦ₂u : ∀ x : Γ(C.toScheme, U.1),
      Φ₂.symm (algebraMap Γ(C.toScheme, U.1) (BasedJetAlgebra ε' r) x) = algebraMap _ _ x :=
    BasedJetAlgebra.towerEquiv_symm_algebraMap ε₀ ε' (fun _ => rfl) r
  have he₃u : ∀ x : Γ(C.toScheme, U.1),
      e₃ (algebraMap Γ(C.toScheme, U.1) (BasedJetAlgebra ε₀ r) x) = MvPolynomial.C x :=
    BasedJetAlgebra.mvPolynomialEquiv_algebraMap ε₀ r β
  refine ⟨Φ₁.trans (Φ₂.symm.trans (e₃.trans (e₄.trans e₅))), ?_, ?_⟩
  · intro m a
    have hw : ∀ i : Fin r × ULift.{u} (Fin (n + 1)),
        (fun iq : ULift.{u} (Fin (n + 1) × Fin r) ↦ (iq.down.2 : ℕ) + 1) (jetIndexEquiv r n i) =
          BasedJetAlgebra.weight r (ULift.{u} (Fin (n + 1))) i := fun _ => rfl
    have hw' : ∀ j : ULift.{u} (Fin (n + 1) × Fin r),
        BasedJetAlgebra.weight r (ULift.{u} (Fin (n + 1))) ((jetIndexEquiv r n).symm j) =
          (fun iq : ULift.{u} (Fin (n + 1) × Fin r) ↦ (iq.down.2 : ℕ) + 1) j := fun _ => rfl
    show a ∈ BasedJetAlgebra.grading ε r m ↔
      (MvPolynomial.rename (jetIndexEquiv r n)
        (MvPolynomial.map (τ.symm : Γ(C.toScheme, U.1) →+* Γ(U.1.toScheme, ⊤))
          (e₃ (Φ₂.symm (Φ₁ a))))).IsWeightedHomogeneous _ m
    refine (BasedJetAlgebra.towerEquiv_mem_grading_iff ε ε' hε₁ r m a).trans ?_
    refine (BasedJetAlgebra.towerEquiv_symm_mem_grading_iff ε₀ ε' (fun _ => rfl) r m
      (Φ₁ a)).symm.trans ?_
    refine (BasedJetAlgebra.mem_grading_iff_isWeightedHomogeneous ε₀ r β m _).trans ?_
    refine (MvPolynomial.IsWeightedHomogeneous.map_iff
      (τ.symm : Γ(C.toScheme, U.1) →+* Γ(U.1.toScheme, ⊤)) τ.symm.injective _).symm.trans ?_
    refine ⟨fun h => h.rename_of (jetIndexEquiv r n).injective hw, fun h => ?_⟩
    have h2 := h.rename_of (jetIndexEquiv r n).symm.injective hw'
    rwa [MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id] at h2
  · intro a
    show MvPolynomial.rename (jetIndexEquiv r n)
        (MvPolynomial.map (τ.symm : Γ(C.toScheme, U.1) →+* Γ(U.1.toScheme, ⊤))
          (e₃ (Φ₂.symm (Φ₁ (algebraMap Γ(C.toScheme, U.1) _ (U.1.topIso.hom.hom a)))))) =
      MvPolynomial.C a
    rw [hΦ₁u, hΦ₂u, he₃u, MvPolynomial.map_C, MvPolynomial.rename_C]
    congr 1
    exact τ.symm_apply_apply a

end
