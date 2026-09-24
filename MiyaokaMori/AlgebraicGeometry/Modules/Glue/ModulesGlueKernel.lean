import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueSectionwise
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesSectionsLimits

/-! # The kernel construction of the glued sheaf is a sectionwise equalizer

Let `X` be a scheme, `{U_i}` a family of opens, `F_i` sheaves of modules on `U_i`, and
`θ_ij : F_i|_{U_i ⊓ U_j} ⟶ F_j|_{U_i ⊓ U_j}`. The construction of Stacks 00AL is
`glueKernel U F θ := ker(a - b)` with `a, b : ∏_i ι_{i*}F_i ⟶ ∏_{(i,j)} ι_{ij*}(F_j|_{U_ij})`,
where the `(i,j)` component of `a` is "restrict the `j`-th component to `U_ij`" and that of `b`
is "restrict the `i`-th component to `U_ij`, then apply `θ_ij`"; `glueKernelπ i` is the kernel
inclusion followed by the `i`-th projection. (`GlueData.glued D` is by definition
`glueKernel U D.F (fun i j => (D.φ i j).hom)`.)

The main theorem `isSectionwiseGlue_glueKernel` says that `(glueKernel, glueKernelπ)` is
sectionwise an equalizer of `(F, θ)` (`IsSectionwiseGlue`). Proof sketch: the section map of
`pushforwardRestrictHom` is a restriction map; with `V' = V ⊓ (U_i ⊓ U_j)` the components `α_ij`,
`β_ij` of `a`, `b` on `V` are "restrict to `V'`" followed by an isomorphism `e`, resp. by
`overlapSectionMap θ_ij V'` and `e`; `kernel.condition` gives `π_j ≫ α_ij = π_i ≫ β_ij`, which
yields compatibility; injectivity is `sections_kernel_ι_injective` with `sections_pi_ext`; gluing
uses `sections_pi_exists` and `sections_kernel_exists`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Restriction: for `F` on `W` and `V' ≤ W`, the morphism `W.ι_* F ⟶ V'.ι_*(F|_{V'})` (same body
as `pushforwardRestrictMap`). -/
def pushforwardRestrictHom {V' W : X.Opens} (h : V' ≤ W) (F : W.toScheme.Modules) :
    (pushforward W.ι).obj F ⟶ (pushforward V'.ι).obj (F.restrict (X.homOfLE h)) :=
  (pushforward W.ι).map ((restrictAdjunction (X.homOfLE h)).unit.app F) ≫
    (pushforwardComp (X.homOfLE h) W.ι).inv.app _ ≫
    (pushforwardCongr (X.homOfLE_ι h)).hom.app _

theorem homOfLE_image_preimage_le {V' W : X.Opens} (h : V' ≤ W) (V : X.Opens) :
    X.homOfLE h ''ᵁ (V'.ι ⁻¹ᵁ V) ≤ W.ι ⁻¹ᵁ V := by
  rw [← AlgebraicGeometry.Scheme.Hom.image_le_image_iff W.ι, image_homOfLE_image,
    AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Opens.opensRange_ι, AlgebraicGeometry.Scheme.Opens.opensRange_ι]
  exact inf_le_inf_right _ h

theorem pushforwardRestrictHom_app {V' W : X.Opens} (h : V' ≤ W) (F : W.toScheme.Modules)
    (V : X.Opens) :
    (pushforwardRestrictHom h F).app V =
      F.presheaf.map (homOfLE (homOfLE_image_preimage_le h V)).op := by
  have e : (X.homOfLE h ≫ W.ι) ⁻¹ᵁ V = V'.ι ⁻¹ᵁ V := by rw [X.homOfLE_ι h]
  change F.presheaf.map (homOfLE ((X.homOfLE h).image_preimage_le (W.ι ⁻¹ᵁ V))).op ≫ 𝟙 _ ≫
    F.presheaf.map ((X.homOfLE h).opensFunctor.map (eqToHom e.symm)).op = _
  rw [Category.id_comp]
  exact glueAux_map2 F.presheaf _ _ _

variable {ι : Type u} (U : ι → X.Opens) (F : ∀ i, (U i).toScheme.Modules)
  (θ : ∀ i j, (F i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ⟶
    (F j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)))

/-- The factors of `∏_i ι_{i*}F_i`. -/
abbrev glueKernelP (i : ι) : X.Modules := (pushforward (U i).ι).obj (F i)

/-- The factors of `∏_{(i,j)} ι_{ij*}(F_j|_{U_ij})`. -/
abbrev glueKernelQ (q : ι × ι) : X.Modules :=
  (pushforward (U q.1 ⊓ U q.2).ι).obj
    ((F q.2).restrict (X.homOfLE (inf_le_right : U q.1 ⊓ U q.2 ≤ U q.2)))

/-- Restrict the `j`-th component to `U_ij`. -/
def glueKernelA : ∏ᶜ (glueKernelP U F) ⟶ ∏ᶜ (glueKernelQ U F) :=
  Pi.lift fun q => Pi.π (glueKernelP U F) q.2 ≫
    pushforwardRestrictHom (inf_le_right : U q.1 ⊓ U q.2 ≤ U q.2) (F q.2)

/-- Restrict the `i`-th component to `U_ij`, then apply `θ_ij`. -/
def glueKernelB : ∏ᶜ (glueKernelP U F) ⟶ ∏ᶜ (glueKernelQ U F) :=
  Pi.lift fun q => Pi.π (glueKernelP U F) q.1 ≫
    pushforwardRestrictHom (inf_le_left : U q.1 ⊓ U q.2 ≤ U q.1) (F q.1) ≫
    (pushforward (U q.1 ⊓ U q.2).ι).map (θ q.1 q.2)

/-- The construction of Stacks 00AL: `ker(∏ ι_{i*}F_i ⇉ ∏ ι_{ij*}(F_j|_{U_ij}))`.
`GlueData.glued D` is by definition `glueKernel U D.F (fun i j => (D.φ i j).hom)`. -/
def glueKernel : X.Modules := kernel (glueKernelA U F - glueKernelB U F θ)

/-- The projection `glueKernel ⟶ ι_{i*}F_i` to the `i`-th piece. -/
def glueKernelπ (i : ι) : glueKernel U F θ ⟶ (pushforward (U i).ι).obj (F i) :=
  kernel.ι _ ≫ Pi.π (glueKernelP U F) i

theorem glueKernelπ_condition (i j : ι) :
    glueKernelπ U F θ j ≫ pushforwardRestrictHom (inf_le_right : U i ⊓ U j ≤ U j) (F j) =
      glueKernelπ U F θ i ≫ pushforwardRestrictHom (inf_le_left : U i ⊓ U j ≤ U i) (F i) ≫
        (pushforward (U i ⊓ U j).ι).map (θ i j) := by
  have h := kernel.condition (glueKernelA U F - glueKernelB U F θ)
  rw [Preadditive.comp_sub, sub_eq_zero] at h
  have h' := congrArg (fun f => f ≫ Pi.π (glueKernelQ U F) (i, j)) h
  simp only [glueKernelA, glueKernelB, Category.assoc, Pi.lift_π] at h'
  exact h'

theorem image_preimage_inf_aux (W V : X.Opens) : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V ⊓ W := by
  rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Opens.opensRange_ι, inf_comm]

theorem glueAux_cat12 {C : Type*} [Category C] {M Pj Pj' Pi Pi' E : C}
    (pj : M ⟶ Pj) (rj : Pj ⟶ Pj') (e : Pj' ⟶ E) (pi : M ⟶ Pi) (ri : Pi ⟶ Pi') (o' : Pi' ⟶ Pj')
    (o : Pi ⟶ Pj) (_ : IsIso e) (_ : IsIso rj)
    (h : pj ≫ rj ≫ e = pi ≫ ri ≫ o' ≫ e) (nat : ri ≫ o' = o ≫ rj) : pi ≫ o = pj := by
  rw [← cancel_mono rj, ← cancel_mono e]
  simp only [Category.assoc]
  rw [h, ← reassoc_of% nat]

theorem glueAux_cat13 {C : Type*} [Category C] {A B B' D E : C}
    (r : A ⟶ B) (θ' : B ⟶ E) (a : B ⟶ B') (o : B' ⟶ D) (b : D ⟶ E) (res : A ⟶ B')
    (hθ : θ' = a ≫ o ≫ b) (h : r ≫ a = res) : r ≫ θ' = res ≫ o ≫ b := by
  subst hθ h; simp

/-- The section formula for `α_ij`. -/
theorem pushforwardRestrictHom_right_app (i j : ι) (V : X.Opens) :
    (pushforwardRestrictHom (inf_le_right : U i ⊓ U j ≤ U j) (F j)).app V =
      (F j).presheaf.map (homOfLE ((U j).ι.preimage_mono (inf_le_left : V ⊓ (U i ⊓ U j) ≤ V))).op ≫
        (F j).presheaf.map (eqToHom (preimage_image_eq_homOfLE_image
          (inf_le_right : U i ⊓ U j ≤ U j) ((U i ⊓ U j).ι ⁻¹ᵁ V)
          (image_preimage_inf_aux (U i ⊓ U j) V)).symm).op := by
  rw [pushforwardRestrictHom_app]
  exact (glueAux_map2 (F j).presheaf _ _ _).symm

/-- The section formula for `β_ij`. -/
theorem pushforwardRestrictHom_left_comp_app (i j : ι) (V : X.Opens) :
    (pushforwardRestrictHom (inf_le_left : U i ⊓ U j ≤ U i) (F i) ≫
        (pushforward (U i ⊓ U j).ι).map (θ i j)).app V =
      (F i).presheaf.map (homOfLE ((U i).ι.preimage_mono (inf_le_left : V ⊓ (U i ⊓ U j) ≤ V))).op ≫
        overlapSectionMap inf_le_left inf_le_right (θ i j) (V ⊓ (U i ⊓ U j)) inf_le_right ≫
        (F j).presheaf.map (eqToHom (preimage_image_eq_homOfLE_image
          (inf_le_right : U i ⊓ U j ≤ U j) ((U i ⊓ U j).ι ⁻¹ᵁ V)
          (image_preimage_inf_aux (U i ⊓ U j) V)).symm).op := by
  rw [Hom.comp_app, pushforwardRestrictHom_app, pushforward_map_app]
  exact glueAux_cat13 _ _ _ _ _ _
    (app_eq_overlapSectionMap inf_le_left inf_le_right (θ i j) ((U i ⊓ U j).ι ⁻¹ᵁ V)
      (image_preimage_inf_aux (U i ⊓ U j) V))
    (glueAux_map2 (F i).presheaf _ _ _)

/-- The kernel construction is sectionwise an equalizer of the gluing data. -/
theorem isSectionwiseGlue_glueKernel :
    IsSectionwiseGlue U F θ (glueKernel U F θ) (glueKernelπ U F θ) where
  compat := by
    intro i j V hV
    have hc := glueKernelπ_condition U F θ i j
    have h1 : (glueKernelπ U F θ j).app V ≫
          (pushforwardRestrictHom (inf_le_right : U i ⊓ U j ≤ U j) (F j)).app V =
        (glueKernelπ U F θ i).app V ≫
          (pushforwardRestrictHom (inf_le_left : U i ⊓ U j ≤ U i) (F i) ≫
            (pushforward (U i ⊓ U j).ι).map (θ i j)).app V := by
      rw [← Hom.comp_app, ← Hom.comp_app, hc]
    rw [pushforwardRestrictHom_right_app, pushforwardRestrictHom_left_comp_app] at h1
    have hrj := isIso_map_of_preimage_eq (F j)
      (show (U j).ι ⁻¹ᵁ (V ⊓ (U i ⊓ U j)) = (U j).ι ⁻¹ᵁ V by rw [inf_eq_left.mpr hV])
      (homOfLE ((U j).ι.preimage_mono (inf_le_left : V ⊓ (U i ⊓ U j) ≤ V))).op
    have he : IsIso ((F j).presheaf.map (eqToHom (preimage_image_eq_homOfLE_image
        (inf_le_right : U i ⊓ U j ≤ U j) ((U i ⊓ U j).ι ⁻¹ᵁ V)
        (image_preimage_inf_aux (U i ⊓ U j) V)).symm).op) := inferInstance
    exact glueAux_cat12 _ _ _ _ _ _ _ he hrj h1
      (overlapSectionMap_naturality inf_le_left inf_le_right (θ i j) V _ hV inf_le_left)
  inj := by
    intro V s s' h
    apply sections_kernel_ι_injective _ V
    apply sections_pi_ext (glueKernelP U F) V
    intro i
    exact h i
  glue := by
    intro V t ht
    obtain ⟨x, hx⟩ := sections_pi_exists (glueKernelP U F) V t
    have hzero : (glueKernelA U F - glueKernelB U F θ).app V x = 0 := by
      apply sections_pi_ext (glueKernelQ U F) V
      rintro ⟨i, j⟩
      have hA : glueKernelA U F ≫ Pi.π (glueKernelQ U F) (i, j) = Pi.π (glueKernelP U F) j ≫
          pushforwardRestrictHom (inf_le_right : U i ⊓ U j ≤ U j) (F j) := by
        simp only [glueKernelA, Pi.lift_π]
      have hB : glueKernelB U F θ ≫ Pi.π (glueKernelQ U F) (i, j) = Pi.π (glueKernelP U F) i ≫
          pushforwardRestrictHom (inf_le_left : U i ⊓ U j ≤ U i) (F i) ≫
            (pushforward (U i ⊓ U j).ι).map (θ i j) := by
        simp only [glueKernelB, Pi.lift_π]
      have key : (glueKernelA U F ≫ Pi.π (glueKernelQ U F) (i, j)).app V x =
          (glueKernelB U F θ ≫ Pi.π (glueKernelQ U F) (i, j)).app V x := by
        rw [hA, hB]
        change (pushforwardRestrictHom (inf_le_right : U i ⊓ U j ≤ U j) (F j)).app V
            ((Pi.π (glueKernelP U F) j).app V x) =
          (pushforwardRestrictHom (inf_le_left : U i ⊓ U j ≤ U i) (F i) ≫
            (pushforward (U i ⊓ U j).ι).map (θ i j)).app V ((Pi.π (glueKernelP U F) i).app V x)
        rw [hx j, hx i, pushforwardRestrictHom_right_app, pushforwardRestrictHom_left_comp_app]
        exact congrArg _ (ht i j).symm
      have h0 : ((glueKernelA U F - glueKernelB U F θ) ≫ Pi.π (glueKernelQ U F) (i, j)).app V x = 0 := by
        rw [Preadditive.sub_comp, Hom.sub_app]
        change (glueKernelA U F ≫ Pi.π (glueKernelQ U F) (i, j)).app V x -
          (glueKernelB U F θ ≫ Pi.π (glueKernelQ U F) (i, j)).app V x = 0
        rw [key, sub_self]
      rw [map_zero]
      exact h0
    obtain ⟨s, hs⟩ := sections_kernel_exists _ V x hzero
    refine ⟨s, fun i => ?_⟩
    rw [← hx i, ← hs]
    rfl

end

end AlgebraicGeometry.Scheme.Modules
