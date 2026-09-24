import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ModulesGlueOpenImmersion

/-! # Transposes along the restriction adjunction of an open immersion

Statement: bookkeeping for the adjunction `restrictFunctor f ⊣ pushforward f` of an open immersion
`f : Y ⟶ X` (Mathlib `Scheme.Modules.restrictAdjunction`).
* `restrictTranspose f ρ : M.restrict f ⟶ N` is the transpose of `ρ : M ⟶ f_* N`; on sections over
  `A ⊆ Y` it is `ρ.app (f ''ᵁ A)` followed by the identification `f ⁻¹ᵁ f ''ᵁ A = A`
  (`restrictTranspose_app`); it is an isomorphism as soon as `(restrictFunctor f).map ρ` is
  (`isIso_restrictTranspose`; the counit of `restrictAdjunction` is an isomorphism).
* `pushTransition f t f' h θ : f_* N ⟶ f'_* N'` for `t : Z ⟶ Y`, `t ≫ f = f'`, `θ : N ⟶ t_* N'`:
  `f_* θ ≫ pushforwardComp ≫ pushforwardCongr` (the shape of `Proj.twistPushTransition` and of
  the transition maps `twistTransition` of the glued twisting sheaf).
* `restrictTranspose_pushTransition`: the transpose of `ρ ≫ pushTransition h θ` along `f'` is the
  restriction along `t` of the transpose of `ρ` along `f`, followed by the transpose of `θ`
  (up to the canonical identification `restrictCompIso`).
* `restrictTranspose_quot_compat`: consequently, for `ρ, π : M, N ⟶ f_* P` with invertible
  transposes, the "quotients" `transpose ρ ≫ (transpose π)⁻¹` on `Y` and on `Z` (for
  `ρ ≫ pushTransition`, `π ≫ pushTransition`) are compatible along `t`. This is the compatibility
  hypothesis of `Modules.exists_hom_of_restrict_compat`.

Proof: sections; the identifications `f ⁻¹ᵁ f ''ᵁ A = A`, `f' ''ᵁ A = f ''ᵁ t ''ᵁ A`,
`f' ⁻¹ᵁ U = t ⁻¹ᵁ f ⁻¹ᵁ U` are equalities of opens, and `Opens` is a thin category, so composites of
restriction maps between the same opens agree (`glueAux_map*`); the rest is naturality of `ρ` and
`θ`.

Source: Stacks 01LI (compatibility of the glued sheaf with the transition maps); Mathlib
`AlgebraicGeometry/Modules/Sheaf.lean` (`restrictAdjunction`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion f]

/-- The transpose `M.restrict f ⟶ N` of `ρ : M ⟶ f_* N` along `restrictAdjunction f`. -/
def restrictTranspose {M : X.Modules} {N : Y.Modules} (ρ : M ⟶ (pushforward f).obj N) :
    M.restrict f ⟶ N :=
  ((restrictAdjunction f).homEquiv M N).symm ρ

theorem restrictTranspose_eq {M : X.Modules} {N : Y.Modules} (ρ : M ⟶ (pushforward f).obj N) :
    restrictTranspose f ρ =
      (restrictFunctor f).map ρ ≫ (restrictAdjunction f).counit.app N := by
  rw [restrictTranspose, Adjunction.homEquiv_counit]

private theorem restrictFunctor_map_app_aux {M N : X.Modules} (ρ : M ⟶ N) (A : Y.Opens) :
    ((restrictFunctor f).map ρ).app A = ρ.app (f ''ᵁ A) := rfl

theorem restrictTranspose_app {M : X.Modules} {N : Y.Modules} (ρ : M ⟶ (pushforward f).obj N)
    (A : Y.Opens) :
    (restrictTranspose f ρ).app A =
      ρ.app (f ''ᵁ A) ≫ N.presheaf.map (eqToHom (f.preimage_image_eq A).symm).op := by
  rw [restrictTranspose_eq, Hom.comp_app, restrictAdjunction_counit_app_app,
    restrictFunctor_map_app_aux]
  rfl

theorem isIso_restrictTranspose {M : X.Modules} {N : Y.Modules} (ρ : M ⟶ (pushforward f).obj N)
    (h : IsIso ((restrictFunctor f).map ρ)) : IsIso (restrictTranspose f ρ) := by
  rw [restrictTranspose_eq]
  exact IsIso.comp_isIso

theorem restrictTranspose_comp_map {M : X.Modules} {N N' : Y.Modules}
    (ρ : M ⟶ (pushforward f).obj N) (θ : N ⟶ N') :
    restrictTranspose f (ρ ≫ (pushforward f).map θ) = restrictTranspose f ρ ≫ θ :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

section Transition

variable {Z : AlgebraicGeometry.Scheme.{u}} (t : Z ⟶ Y) (f' : Z ⟶ X)
  [AlgebraicGeometry.IsOpenImmersion f']

omit [AlgebraicGeometry.IsOpenImmersion f] in
theorem preimage_eq_of_comp_eq (h : t ≫ f = f') (U : X.Opens) : f' ⁻¹ᵁ U = t ⁻¹ᵁ f ⁻¹ᵁ U := by
  subst h; rfl

/-- `f_* N ⟶ f'_* N'` induced by `θ : N ⟶ t_* N'` when `t ≫ f = f'`. -/
def pushTransition (h : t ≫ f = f') {N : Y.Modules} {N' : Z.Modules} (θ : N ⟶ (pushforward t).obj N') :
    (pushforward f).obj N ⟶ (pushforward f').obj N' :=
  (pushforward f).map θ ≫ (pushforwardComp t f).hom.app N' ≫ (pushforwardCongr h).hom.app N'

omit [AlgebraicGeometry.IsOpenImmersion f] in
theorem pushTransition_app (h : t ≫ f = f') {N : Y.Modules} {N' : Z.Modules}
    (θ : N ⟶ (pushforward t).obj N') (U : X.Opens) :
    (pushTransition f t f' h θ).app U =
      θ.app (f ⁻¹ᵁ U) ≫ N'.presheaf.map (eqToHom (preimage_eq_of_comp_eq f t f' h U)).op := by
  rw [pushTransition, Hom.comp_app, Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app]
  erw [Category.id_comp]
  rfl

variable [AlgebraicGeometry.IsOpenImmersion t]

/-- Variable-level diagram chase for `restrictTranspose_pushTransition`. -/
private theorem chase_aux {C : Type*} [Category C] {A₀ A₁ B₀ B₁ B₂ D₀ D₁ D₂ E : C}
    (p₀ : A₀ ⟶ B₀) (q : B₀ ⟶ D₀) (m₁ : D₀ ⟶ D₁) (m₂ : D₁ ⟶ E)
    (b' : A₀ ⟶ A₁) (p₁ : A₁ ⟶ B₁) (e₁ : B₁ ⟶ B₂) (p₂ : B₂ ⟶ D₂) (c : D₂ ⟶ E)
    (n₁ : B₀ ⟶ B₁) (k : B₀ ⟶ B₂) (n₂ : D₀ ⟶ D₂)
    (natρ : b' ≫ p₁ = p₀ ≫ n₁) (hk : n₁ ≫ e₁ = k) (natθ : k ≫ p₂ = q ≫ n₂)
    (hN : n₂ ≫ c = m₁ ≫ m₂) :
    (p₀ ≫ q ≫ m₁) ≫ m₂ = b' ≫ (p₁ ≫ e₁) ≫ (p₂ ≫ c) := by
  simp only [Category.assoc]
  rw [reassoc_of% natρ, ← Category.assoc n₁, hk, reassoc_of% natθ, hN]

/-- The transpose of `ρ ≫ pushTransition h θ` is the restriction along `t` of the transpose of `ρ`
followed by the transpose of `θ`. -/
theorem restrictTranspose_pushTransition (h : t ≫ f = f') {M : X.Modules} {N : Y.Modules}
    {N' : Z.Modules} (ρ : M ⟶ (pushforward f).obj N) (θ : N ⟶ (pushforward t).obj N') :
    restrictTranspose f' (ρ ≫ pushTransition f t f' h θ) =
      (restrictCompIso t f f' h).hom.app M ≫ (restrictFunctor t).map (restrictTranspose f ρ) ≫
        restrictTranspose t θ := by
  refine hom_ext _ _ fun A => ?_
  rw [restrictTranspose_app, Hom.comp_app, pushTransition_app, Hom.comp_app, Hom.comp_app,
    restrictCompIso_hom_app_app, restrictFunctor_map_app_aux, restrictTranspose_app,
    restrictTranspose_app]
  have natρ := ρ.mapPresheaf.naturality (eqToHom (image_eq_of_comp_eq t f f' h A).symm).op
  simp only [mapPresheaf_app] at natρ
  rw [pushforward_obj_presheaf_map] at natρ
  have hle : t ''ᵁ A ≤ f ⁻¹ᵁ (f' ''ᵁ A) := by
    rw [image_eq_of_comp_eq t f f' h A, f.preimage_image_eq]
  have natθ := θ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at natθ
  rw [pushforward_obj_presheaf_map] at natθ
  exact chase_aux _ _ _ _ _ _ _ _ _ _ _ _ natρ (glueAux_map2 N.presheaf _ _ (homOfLE hle).op) natθ
    (glueAux_map22 N'.presheaf _ _ _ _)

/-- **Compatibility of the local quotients along a transition.** For `ρ : M ⟶ f_* P`,
`π : N ⟶ f_* P` with invertible transpose of `π`, and `θ : P ⟶ t_* P'` with `t ≫ f = f'`, the
morphisms `transpose ρ ≫ (transpose π)⁻¹` on `Y` and on `Z` (built from `ρ ≫ pushTransition`,
`π ≫ pushTransition`) agree after restriction along `t`. -/
theorem restrictTranspose_quot_compat (h : t ≫ f = f') {M N : X.Modules} {P : Y.Modules}
    {P' : Z.Modules} (ρ : M ⟶ (pushforward f).obj P) (π : N ⟶ (pushforward f).obj P)
    (θ : P ⟶ (pushforward t).obj P')
    (ρ' : M ⟶ (pushforward f').obj P') (π' : N ⟶ (pushforward f').obj P')
    (hρ' : ρ' = ρ ≫ pushTransition f t f' h θ) (hπ' : π' = π ≫ pushTransition f t f' h θ)
    [IsIso (restrictTranspose f π)] [IsIso (restrictTranspose f' π')] :
    restrictTranspose f' ρ' ≫ inv (restrictTranspose f' π') =
      (restrictCompIso t f f' h).hom.app M ≫
        (restrictFunctor t).map (restrictTranspose f ρ ≫ inv (restrictTranspose f π)) ≫
        (restrictCompIso t f f' h).inv.app N := by
  have eπ : restrictTranspose f' π' = (restrictCompIso t f f' h).hom.app N ≫
      (restrictFunctor t).map (restrictTranspose f π) ≫ restrictTranspose t θ := by
    rw [hπ']; exact restrictTranspose_pushTransition f t f' h π θ
  have eρ : restrictTranspose f' ρ' = (restrictCompIso t f f' h).hom.app M ≫
      (restrictFunctor t).map (restrictTranspose f ρ) ≫ restrictTranspose t θ := by
    rw [hρ']; exact restrictTranspose_pushTransition f t f' h ρ θ
  have hlam : IsIso (restrictTranspose t θ) := by
    have h1 : IsIso ((restrictCompIso t f f' h).hom.app N ≫
        (restrictFunctor t).map (restrictTranspose f π) ≫ restrictTranspose t θ) := by
      rw [← eπ]; infer_instance
    have h2 := IsIso.of_isIso_comp_left ((restrictCompIso t f f' h).hom.app N)
      ((restrictFunctor t).map (restrictTranspose f π) ≫ restrictTranspose t θ)
    exact IsIso.of_isIso_comp_left ((restrictFunctor t).map (restrictTranspose f π))
      (restrictTranspose t θ)
  rw [← cancel_mono (restrictTranspose f' π')]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [eρ, eπ]
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
    IsIso.inv_hom_id_assoc]

end Transition

end

end AlgebraicGeometry.Scheme.Modules
