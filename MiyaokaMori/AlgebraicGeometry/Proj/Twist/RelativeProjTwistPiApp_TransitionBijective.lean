import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLocalIso
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwist

/-! # The transition maps of the relative twisting sheaf are bijective on sections over opens inside the
smaller chart

Statement (`GradedAffineAlgebra.bijective_twistTransition_app`): for `h : W ≤ V` in `X.AffineZariskiSite`,
`S : X.GradedAffineAlgebra` and an open `Ω ⊆ Proj_X S` contained in the image of the chart `ι_W`, the section map
`(S.twistTransition m h).app Ω : Γ(ι_V⁻¹Ω, O_V(m)) → Γ(ι_W⁻¹Ω, O_W(m))` of the transition map
`θ_h : (ι_V)_* O_V(m) ⟶ (ι_W)_* O_W(m)` is bijective.

Proof. Write `ρ := Proj.map (S.restrictGraded h) : Proj S(W) ⟶ Proj S(V)` (an open immersion,
`isOpenImmersion_projMap_restrictGraded`, with `ρ ≫ ι_V = ι_W`, `map_projChart`).
1. By definition (`twistTransition`, `Proj.twistPushTransition`) `θ_h = (ι_V)_*(φ) ≫ (pushforwardComp ρ ι_V).hom.app _
   ≫ (pushforwardCongr w).hom.app _` with `φ := Proj.twistToPushforward (S.restrictGraded h) _ m : O_V(m) ⟶ ρ_* O_W(m)`.
   The last two factors are components of natural isomorphisms, hence bijective on sections; so it suffices that
   `φ.app (ι_V⁻¹Ω)` is bijective.
2. `ι_V⁻¹Ω ≤ im ρ` (`preimage_projChart_le_opensRange`): for `z ∈ ι_V⁻¹Ω`, `ι_V z ∈ Ω ⊆ im ι_W`, so
   `ι_V z = ι_W y = ι_V (ρ y)`, and `z = ρ y` since `ι_V` is injective.
3. (`bijective_homEquiv_app`) For any open immersion `ρ`, `M`, `N`, and an isomorphism `θ : ρ^* M ⟶ N`, the adjoint
   `φ = homEquiv θ = unit_M ≫ ρ_* θ : M ⟶ ρ_* N` (`Adjunction.homEquiv_unit`) is bijective on sections over every
   `Ω' ≤ im ρ`: `φ.app Ω' = (unit_M).app Ω' ≫ θ.app (ρ⁻¹Ω')`; `θ.app` is bijective (`θ` is an isomorphism), and
   (`bijective_pullbackPushforwardAdjunction_unit_app`) `(unit_M).app Ω'` is bijective because, by the uniqueness of
   left adjoints (`Adjunction.unit_leftAdjointUniq_hom_app` for `restrictAdjunction ρ` and
   `pullbackPushforwardAdjunction ρ`; `restrictFunctorIsoPullback` is this `leftAdjointUniq`), it is the unit of the
   restriction adjunction, `M.presheaf.map (ρ ''ᵁ ρ⁻¹ᵁ Ω' ≤ Ω')` (`restrictAdjunction_unit_app_app`), followed by a
   component of the natural isomorphism `restrictFunctorIsoPullback`; and `ρ ''ᵁ ρ⁻¹ᵁ Ω' = Ω'` when `Ω' ≤ im ρ`
   (`image_preimage_eq_opensRange_inf`), so the restriction map is an isomorphism.
4. `φ = homEquiv (Proj.twistPullbackHom …)` (definition of `twistPullbackHom` as the inverse transpose), and
   `twistPullbackHom` is an isomorphism by `RelativeProjTwistLocalIso`
   (`isIso_twistPullbackHom_restrictGraded`). Steps 2–3 give the bijectivity of `φ.app (ι_V⁻¹Ω)`.

Source: Stacks 01LI (the transition maps of the gluing are isomorphisms on the overlaps), 01MX;
Lemma 2.2 of the paper.
Edge cases: `Ω = ∅` (zero groups); `W = V` (`ρ` is the identity map on `Proj S(V)`, `θ_h` the identity up to the
transports; the argument is uniform).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

-- Guard (as in `RelativeProjTwistLimit`): `O_U(m)` is treated as an opaque module sheaf here.
attribute [local irreducible] AlgebraicGeometry.Proj.twist

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Composition of bijective morphisms of abelian groups is bijective. Stated so that it can be applied by
`exact` to composites whose middle object is only definitionally determined (rewriting with
`AddCommGrpCat.hom_comp` fails there). -/
theorem bijective_comp_hom {A B C : Ab} (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Bijective f.hom)
    (hg : Function.Bijective g.hom) : Function.Bijective (f ≫ g).hom := by
  rw [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp]
  exact hg.comp hf

/-- A morphism of opens between equal opens is an isomorphism (`Y.Opens` is thin). -/
theorem isIso_opens_hom_of_eq {A B : Y.Opens} (i : A ⟶ B) (e : A = B) : IsIso i := by
  subst e
  rw [Subsingleton.elim i (𝟙 A)]
  infer_instance

/-- The unit of `pullback ρ ⊣ pushforward ρ` (`ρ` an open immersion) is bijective on sections over every open
`Ω ≤ im ρ`. -/
theorem bijective_pullbackPushforwardAdjunction_unit_app (ρ : X ⟶ Y) [IsOpenImmersion ρ] (M : Y.Modules)
    (Ω : Y.Opens) (hΩ : Ω ≤ ρ.opensRange) :
    Function.Bijective (((pullbackPushforwardAdjunction ρ).unit.app M).app Ω).hom := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction ρ) (pullbackPushforwardAdjunction ρ) M,
    Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app]
  have : IsIso (homOfLE (ρ.image_preimage_le Ω)) :=
    isIso_opens_hom_of_eq _ (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hΩ])
  -- the middle objects of the composite agree only up to definitional unfolding, so the two factors are
  -- composed by hand (`bijective_comp_hom`) instead of through `IsIso.comp_isIso`
  have hf : Function.Bijective (M.presheaf.map (homOfLE (ρ.image_preimage_le Ω)).op).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hg : Function.Bijective ((((restrictAdjunction ρ).leftAdjointUniq
      (pullbackPushforwardAdjunction ρ)).hom.app M).app (ρ ⁻¹ᵁ Ω)).hom :=
    ConcreteCategory.bijective_of_isIso _
  exact bijective_comp_hom _ _ hf hg

/-- The adjoint transpose of `θ : ρ^* M ⟶ N` on sections. -/
theorem homEquiv_app (ρ : X ⟶ Y) (M : Y.Modules) (N : X.Modules) (θ : (pullback ρ).obj M ⟶ N) (Ω : Y.Opens) :
    ((pullbackPushforwardAdjunction ρ).homEquiv M N θ).app Ω =
      ((pullbackPushforwardAdjunction ρ).unit.app M).app Ω ≫ θ.app (ρ ⁻¹ᵁ Ω) := by
  rw [Adjunction.homEquiv_unit, Hom.comp_app, pushforward_map_app]
  rfl

/-- If `θ : ρ^* M ⟶ N` is an isomorphism (`ρ` an open immersion), its adjoint transpose `M ⟶ ρ_* N` is bijective
on sections over every open `Ω ≤ im ρ`. -/
theorem bijective_homEquiv_app (ρ : X ⟶ Y) [IsOpenImmersion ρ] (M : Y.Modules) (N : X.Modules)
    (θ : (pullback ρ).obj M ⟶ N) [IsIso θ] (Ω : Y.Opens) (hΩ : Ω ≤ ρ.opensRange) :
    Function.Bijective (((pullbackPushforwardAdjunction ρ).homEquiv M N θ).app Ω).hom := by
  rw [homEquiv_app]
  have hθ : Function.Bijective (θ.app (ρ ⁻¹ᵁ Ω)).hom := ConcreteCategory.bijective_of_isIso _
  exact bijective_comp_hom _ _ (bijective_pullbackPushforwardAdjunction_unit_app ρ M Ω hΩ) hθ

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The transition map `T(f) = (ι_A)_*(θ_f) ≫ pushforwardComp ≫ pushforwardCongr` is bijective on sections over
`U` as soon as `θ_f = twistToPushforward f` is bijective on sections over `ι_A⁻¹U` (the other two factors are
components of natural isomorphisms). Stated for generic gradings: the kernel check of the unfolding is cheap
here and expensive on the concrete charts `Proj S(U)` (see the compile-time remarks in
`RelativeProjTwistLimit`). -/
theorem bijective_twistPushTransition_app (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    {Y : Scheme.{u}} (ιA : Proj 𝒜 ⟶ Y) (ιB : Proj ℬ ⟶ Y) (w : Proj.map f hf ≫ ιA = ιB) (U : Y.Opens)
    (h1 : Function.Bijective ((twistToPushforward f hf n).app (ιA ⁻¹ᵁ U)).hom) :
    Function.Bijective ((twistPushTransition f hf n ιA ιB w).app U).hom := by
  have h2 : Function.Bijective
      (((Scheme.Modules.pushforwardComp (Proj.map f hf) ιA).hom.app (Proj.twist ℬ n)).app U).hom :=
    ConcreteCategory.bijective_of_isIso _
  have h3 : Function.Bijective
      (((Scheme.Modules.pushforwardCongr w).hom.app (Proj.twist ℬ n)).app U).hom :=
    ConcreteCategory.bijective_of_isIso _
  unfold twistPushTransition
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app]
  exact Scheme.Modules.bijective_comp_hom _ _ h1 (Scheme.Modules.bijective_comp_hom _ _ h2 h3)

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- If `Ω ≤ im ι_W` and `W ≤ V`, then every point of `ι_V⁻¹Ω` lies in the image of the chart transition
`ρ = Proj.map (S.restrictGraded h) : Proj S(W) ⟶ Proj S(V)`. -/
theorem exists_projMap_eq_of_projChart_mem {W V : X.AffineZariskiSite} (h : W ≤ V)
    (Ω : S.relativeProj.left.Opens) (hΩ : Ω ≤ (S.projChart W).opensRange) (z : Proj (S.grading V))
    (hz : S.projChart V z ∈ Ω) :
    ∃ y, Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) y = z := by
  have hρι : Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) ≫ S.projChart V =
      S.projChart W := S.map_projChart h
  obtain ⟨y, hy⟩ := hΩ hz
  refine ⟨y, (S.projChart V).isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, hρι]
  exact hy

/-- **Stacks 01LI, transition maps**: for `W ≤ V` and an open `Ω ⊆ Proj_X S` inside the chart `im ι_W`, the
transition map `θ_h : (ι_V)_* O_V(m) ⟶ (ι_W)_* O_W(m)` is bijective on sections over `Ω`. -/
theorem bijective_twistTransition_app (m : ℤ) {W V : X.AffineZariskiSite} (h : W ≤ V)
    (Ω : S.relativeProj.left.Opens) (hΩ : Ω ≤ (S.projChart W).opensRange) :
    Function.Bijective ((S.twistTransition m h).app Ω).hom := by
  have := S.isOpenImmersion_projMap_restrictGraded h
  have hφ : Proj.twistToPushforward (S.restrictGraded h) (S.restrict_irrelevant_le h) m =
      (Scheme.Modules.pullbackPushforwardAdjunction
        (Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h))).homEquiv _ _
        (Proj.twistPullbackHom (S.restrictGraded h) (S.restrict_irrelevant_le h) m) := by
    rw [Proj.twistPullbackHom, Equiv.apply_symm_apply]
  have h1 : Function.Bijective
      ((Proj.twistToPushforward (S.restrictGraded h) (S.restrict_irrelevant_le h) m).app
        (S.projChart V ⁻¹ᵁ Ω)).hom := by
    rw [hφ]
    have := S.isIso_twistPullbackHom_restrictGraded m h
    exact Scheme.Modules.bijective_homEquiv_app _ _ _ _ _
      (fun z hz => S.exists_projMap_eq_of_projChart_mem h Ω hΩ z hz)
  exact Proj.bijective_twistPushTransition_app (S.restrictGraded h) (S.restrict_irrelevant_le h) m
    (S.projChart V) (S.projChart W) (S.map_projChart h) Ω h1

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
