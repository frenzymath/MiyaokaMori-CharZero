import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjMapTwistComparison
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistToPushforwardApply
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue

/-! # Functoriality of the twist comparison maps under composition

Statement (Stacks 01MX/01NP, functoriality of θ): for graded ring homs `f : 𝒜 →+*ᵍ ℬ`, `g : ℬ →+*ᵍ 𝒞`
(with `ℬ₊ ⊆ √(f 𝒜₊)`, `𝒞₊ ⊆ √(g ℬ₊)`), the comparison maps of `ProjMapTwistComparison` are
compatible with composition:
* `twistToPushforward_comp`: `θ_{g∘f} = θ_f ≫ (Proj.map f)_* θ_g` (up to `pushforwardComp` and
  `pushforwardCongr` along `Proj.map (g ∘ f) = Proj.map g ≫ Proj.map f`) — proved pointwise: both sides
  send a local fraction `a/s` to `g(f(a))/g(f(s))` (`Localization.localRingHom_comp`).
* `twistPullbackHom_comp`: the adjoint transposes correspond: `θ^{g∘f} = E ≫ (Proj.map g)^* θ^f ≫ θ^g`,
  where `E : (Proj.map (g∘f))^* ≅ (Proj.map f)^* ⋙ (Proj.map g)^*` is the canonical identification of
  the left adjoints (`Adjunction.leftAdjointUniq`; its right-adjoint side is `pushforwardComp`/`pushforwardCongr`).
* `isIso_twistPullbackHom_comp`: hence `θ^{g∘f}` is an isomorphism as soon as `θ^f` and `θ^g` are
  (also for a `χ` equal to `g ∘ f`, `isIso_twistPullbackHom_of_eq_comp`).

Source: Stacks 01MX (θ), 01NP (transitivity); Mathlib `Localization.localRingHom_comp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory.Adjunction

/-- Transposes along two adjunctions with the same right adjoint correspond under
`leftAdjointUniq` (used by `RelativeProjBaseChangeTwistLocalIso`; kept here so that this module stays generic
and light). -/
theorem homEquiv_symm_eq_leftAdjointUniq' {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {X : C} {Y : D}
    (c : X ⟶ G.obj Y) :
    (adj1.homEquiv X Y).symm c =
      (leftAdjointUniq adj1 adj2).hom.app X ≫ (adj2.homEquiv X Y).symm c := by
  rw [homEquiv_counit, homEquiv_counit, ← leftAdjointUniq_hom_app_counit adj1 adj2 Y,
    ← Category.assoc, (leftAdjointUniq adj1 adj2).hom.naturality c, Category.assoc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.Modules

/-- `pushforwardCongr h ≫ pushforwardCongr h.symm = 𝟙` on components (used above; also in
`RelativeProjBaseChangeTwistLocalIso`). -/
@[reassoc]
theorem pushforwardCongr_hom_app_comp_symm {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : X.Modules) :
    (pushforwardCongr h).hom.app M ≫ (pushforwardCongr h.symm).hom.app M = 𝟙 _ := by
  refine hom_ext _ _ fun U => ?_
  rw [Hom.comp_app, pushforwardCongr_hom_app_app, pushforwardCongr_hom_app_app, Hom.id_app]
  exact (glueAux_map2 M.presheaf _ _ (𝟙 _)).trans (M.presheaf.map_id _)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

variable {σ τ ρ A B C : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [CommRing C] [SetLike ρ C] [AddSubgroupClass ρ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

private lemma localRingHom_family_comp' (V : Set (ProjectiveSpectrum 𝒜))
    (s : ∀ x : V, MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x.1)
    (x₁ x₂ : ProjectiveSpectrum 𝒜) (h₁ : x₁ ∈ V) (h₂ : x₂ ∈ V) (h12 : x₁ = x₂)
    (yB : ProjectiveSpectrum ℬ) (zC : ProjectiveSpectrum 𝒞)
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (hx₁ : x₁.asHomogeneousIdeal.toIdeal = zC.asHomogeneousIdeal.toIdeal.comap χ)
    (hx₂ : x₂.asHomogeneousIdeal.toIdeal = yB.asHomogeneousIdeal.toIdeal.comap φ)
    (hJ : yB.asHomogeneousIdeal.toIdeal = zC.asHomogeneousIdeal.toIdeal.comap ψ) :
    Localization.localRingHom x₁.asHomogeneousIdeal.toIdeal zC.asHomogeneousIdeal.toIdeal χ hx₁
        (s ⟨x₁, h₁⟩) =
      Localization.localRingHom yB.asHomogeneousIdeal.toIdeal zC.asHomogeneousIdeal.toIdeal ψ hJ
        (Localization.localRingHom x₂.asHomogeneousIdeal.toIdeal yB.asHomogeneousIdeal.toIdeal φ hx₂
          (s ⟨x₂, h₂⟩)) := by
  subst h12; subst hχ
  exact DFunLike.congr_fun
    (Localization.localRingHom_comp (I := x₁.asHomogeneousIdeal.toIdeal)
      yB.asHomogeneousIdeal.toIdeal zC.asHomogeneousIdeal.toIdeal φ hx₂ ψ hJ) (s ⟨x₁, h₁⟩)

variable (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
  (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
  (hg : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map g) (n : ℤ)

/-- `comap` of a composite is the composite of the `comap`s. -/
theorem comap_comp_apply (z : ProjectiveSpectrum 𝒞) :
    ProjectiveSpectrum.comap (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) z =
      ProjectiveSpectrum.comap f hf (ProjectiveSpectrum.comap g hg z) := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_)
  show Ideal.comap ((g.comp f : 𝒜 →+*ᵍ 𝒞) : A →+* C) _ =
    Ideal.comap (f : A →+* B) (Ideal.comap (g : B →+* C) _)
  rw [Ideal.comap_comap]
  rfl

/-- Restriction of a section of `O(n)` along an equality of morphisms (`pushforwardCongr`) is
restriction of the underlying function (`rfl` after `subst`). -/
theorem pushforwardCongr_twist_app_apply {Y : AlgebraicGeometry.Scheme.{u}}
    {ι₁ ι₂ : AlgebraicGeometry.Proj 𝒞 ⟶ Y} (h : ι₁ = ι₂) (U : Y.Opens)
    (t : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒞 n (ι₁ ⁻¹ᵁ U))
    (z : (ι₂ ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒞).Opens)) (hz : z.1 ∈ (ι₁ ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒞).Opens)) :
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒞 n (ι₂ ⁻¹ᵁ U) from
      (((AlgebraicGeometry.Scheme.Modules.pushforwardCongr h).hom.app (twist 𝒞 n)).app U).hom t).1 z =
      t.1 ⟨z.1, hz⟩ := by
  subst h
  rfl

/-- **Functoriality of θ** (Stacks 01MX, 01NP): `θ_f ≫ (Proj.map f)_* θ_g = θ_{g ∘ f}` up to the
canonical identifications. -/
theorem twistToPushforward_comp :
    twistToPushforward f hf n ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (map f hf)).map (twistToPushforward g hg n) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (map g hg) (map f hf)).hom.app (twist 𝒞 n) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (map_comp f g hf hg).symm).hom.app (twist 𝒞 n) =
    twistToPushforward (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.Hom.comp_app, AlgebraicGeometry.Scheme.Modules.pushforward_map_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app]
  erw [Category.id_comp]
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine Subtype.ext (funext fun z => ?_)
  obtain ⟨zpt, hz0⟩ := z
  have hz : zpt ∈ ((map g hg ≫ map f hf) ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒞).Opens) := by
    have h := hz0
    rw [map_comp f g hf hg] at h
    exact h
  have hB : ProjectiveSpectrum.comap g hg zpt ∈ ((map f hf) ⁻¹ᵁ U : (AlgebraicGeometry.Proj ℬ).Opens) := hz
  refine Eq.trans ?_ (twistToPushforward_app_apply (g.comp f) _ n U s ⟨zpt, hz0⟩).symm
  refine Eq.trans (pushforwardCongr_twist_app_apply n (map_comp f g hf hg).symm U _ ⟨zpt, hz0⟩ hz) ?_
  refine Eq.trans (twistToPushforward_app_apply g hg n ((map f hf) ⁻¹ᵁ U) _ ⟨zpt, hB⟩) ?_
  refine Eq.trans (congrArg _ (twistToPushforward_app_apply f hf n U s ⟨_, hB⟩)) ?_
  exact (localRingHom_family_comp' _ s.1 _ _ hz0 hB (comap_comp_apply f g hf hg zpt)
    (ProjectiveSpectrum.comap g hg zpt) zpt (f : A →+* B) (g : B →+* C) ((g.comp f : 𝒜 →+*ᵍ 𝒞) : A →+* C)
    rfl rfl rfl rfl).symm

/-- The canonical identification `(Proj.map (g ∘ f))^* ≅ (Proj.map f)^* ⋙ (Proj.map g)^*` of left
adjoints (right adjoints: `pushforwardCongr` along `Proj.map_comp` followed by `pushforwardComp`). -/
def pullbackMapCompIso :
    AlgebraicGeometry.Scheme.Modules.pullback (map (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg)) ≅
      AlgebraicGeometry.Scheme.Modules.pullback (map f hf) ⋙ AlgebraicGeometry.Scheme.Modules.pullback (map g hg) :=
  Adjunction.leftAdjointUniq
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction _).ofNatIsoRight
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (map_comp f g hf hg) ≪≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp (map g hg) (map f hf)).symm))
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (map f hf)).comp
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (map g hg)))

/-- **θ is compatible with composition** (Stacks 01MX): `θ^{g∘f} = E ≫ (Proj.map g)^* θ^f ≫ θ^g`. -/
theorem twistPullbackHom_comp :
    twistPullbackHom (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n =
      (pullbackMapCompIso f g hf hg).hom.app (twist 𝒜 n) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (map g hg)).map (twistPullbackHom f hf n) ≫
      twistPullbackHom g hg n := by
  set e := AlgebraicGeometry.Scheme.Modules.pushforwardCongr (map_comp f g hf hg) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp (map g hg) (map f hf)).symm with he
  set adjL := AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (map (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg)) with hadjL
  set adjR := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (map f hf)).comp
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (map g hg)) with hadjR
  have h1 : twistPullbackHom (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n =
      ((adjL.ofNatIsoRight e).homEquiv _ _).symm
        (twistToPushforward (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n ≫ e.hom.app _) := by
    rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
    rfl
  have h2 := Adjunction.homEquiv_symm_eq_leftAdjointUniq' (adjL.ofNatIsoRight e) adjR
    (twistToPushforward (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n ≫ e.hom.app _)
  have h3 : twistToPushforward (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n ≫
      e.hom.app _ = twistToPushforward f hf n ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (map f hf)).map (twistToPushforward g hg n) := by
    rw [← twistToPushforward_comp f g hf hg n, he]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [AlgebraicGeometry.Scheme.Modules.pushforwardCongr_hom_app_comp_symm_assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have h4 : (adjR.homEquiv _ _).symm (twistToPushforward f hf n ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (map f hf)).map (twistToPushforward g hg n)) =
      (AlgebraicGeometry.Scheme.Modules.pullback (map g hg)).map (twistPullbackHom f hf n) ≫
        twistPullbackHom g hg n := by
    rw [hadjR, Adjunction.comp_homEquiv]
    dsimp only [Equiv.symm_trans_apply]
    rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm]
    rfl
  rw [h1, h2, h3, h4]
  rfl

/-- `θ^{g∘f}` is an isomorphism when `θ^f` and `θ^g` are. -/
theorem isIso_twistPullbackHom_comp [IsIso (twistPullbackHom f hf n)] [IsIso (twistPullbackHom g hg n)] :
    IsIso (twistPullbackHom (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n) := by
  rw [twistPullbackHom_comp f g hf hg n]
  infer_instance

/-- `θ^χ` is an isomorphism when `χ = g ∘ f` (as graded ring homs) and `θ^f`, `θ^g` are. -/
theorem isIso_twistPullbackHom_of_eq_comp (χ : 𝒜 →+*ᵍ 𝒞)
    (hχ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map χ) (e : χ = g.comp f)
    [IsIso (twistPullbackHom f hf n)] [IsIso (twistPullbackHom g hg n)] :
    IsIso (twistPullbackHom χ hχ n) := by
  subst e
  exact isIso_twistPullbackHom_comp f g hf hg n

end AlgebraicGeometry.Proj



end
