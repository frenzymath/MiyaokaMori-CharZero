import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates

/-! # Coordinates of the tautological section along a section of the total space

Let `V = ⨁ A` be the biproduct of finitely many locally free finite type modules on `X`,
`s₀ ∈ Γ(X, V)`, and `σ := totalSpaceSectionEquiv V s₀` the corresponding section of `Tot(V)`
(`σ ≫ π = 𝟙`). The `i`-th coordinate `π^*(pr_i)(τ)` of the tautological section `τ ∈ Γ(Tot V, π^*V)`
(corresponding to `𝟙` under `totalSpaceHomEquiv`), pulled back along `σ` and read through the
canonical isomorphisms `σ^*π^*(A i) ≅ (σ ≫ π)^*(A i) ≅ (𝟙)^*(A i) ≅ A i` (`pullbackComp`,
`pullbackCongr`, `pullbackId`), is the `i`-th coordinate `pr_i(s₀)` of `s₀`. This is used for the
section `s = (f_0, …, f_N) : C → 𝒵` of the twisted affine cone given by the homogeneous coordinate
tuple (§4 of the paper).

Proof:
1. `totalSpaceHomEquiv_naturality_coordinate` (with `T = Tot V`, `j = σ`, `m = 𝟙`): the `i`-th
   coordinate after precomposition with `σ` is `τ_i` pulled back along `σ`, followed by `pullbackComp`.
2. `totalSpaceHomEquiv_congr` (by `subst`): along `σ ≫ π = 𝟙`, `totalSpaceHomEquiv` on
   `Over.mk (σ ≫ π)` is transported to `Over.mk 𝟙` up to a `pullbackCongr`;
   `totalSpaceSectionEquiv_homMk_eq` (unfolding the definition) identifies the resulting morphism with
   `(totalSpaceHomEquiv (Over.mk 𝟙)).symm (pullbackId⁻¹ s₀)`, so `Equiv.apply_symm_apply` gives
   `pullbackId⁻¹ s₀`.
3. Naturality of `pullbackCongr⁻¹` and `pullbackId⁻¹` moves `π^*(pr_i)` onto `s₀`, and `inv ≫ hom = 𝟙`
   cancels. All bridging lemmas (composition, `Hom.app`, naturality, `inv_hom_id`) are stated at the
   level of variables (`Modules.*_val_app_top_apply`) and combined on concrete terms only by
   `Eq.trans`/`congrArg`, without `rw`/`change` (`kabstract`/defeq checks on the concrete terms would
   unfold `pullbackId`/`pullbackComp`/`eqToHom` and time out).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The action of a composite morphism on global sections (a variable-level `rfl` bridge). -/
theorem comp_val_app_top_apply {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((f ≫ g).val.app (Opposite.op ⊤)).hom x = (g.val.app (Opposite.op ⊤)).hom ((f.val.app (Opposite.op ⊤)).hom x) :=
  rfl

/-- The spellings `Hom.app` and `.val.app` agree on global sections (a variable-level `rfl` bridge). -/
theorem hom_app_top_eq {M N : X.Modules} (φ : M ⟶ N) (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    φ.app ⊤ x = (φ.val.app (Opposite.op ⊤)).hom x :=
  rfl

/-- The action of `map` of the identity functor on global sections (a variable-level `rfl` bridge). -/
theorem id_functor_map_val_app_top_apply {M N : X.Modules} (f : M ⟶ N)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((CategoryTheory.Functor.id X.Modules).map f).val.app (Opposite.op ⊤)).hom x =
      (f.val.app (Opposite.op ⊤)).hom x :=
  rfl

/-- Naturality of a natural transformation on global sections (variable level). -/
theorem natTrans_naturality_val_app_top_apply {Y : AlgebraicGeometry.Scheme.{u}}
    {F G : X.Modules ⥤ Y.Modules} (α : F ⟶ G) {M N : X.Modules} (f : M ⟶ N)
    (x : ((F.obj M).val.obj (Opposite.op ⊤) : Type u)) :
    ((G.map f).val.app (Opposite.op ⊤)).hom (((α.app M).val.app (Opposite.op ⊤)).hom x) =
      ((α.app N).val.app (Opposite.op ⊤)).hom (((F.map f).val.app (Opposite.op ⊤)).hom x) := by
  have h := congrArg (fun φ : F.obj M ⟶ G.obj N => (φ.val.app (Opposite.op ⊤)).hom x) (α.naturality f)
  exact h.symm

/-- `inv ≫ hom = 𝟙` for a natural isomorphism, on global sections (variable level). -/
theorem natIso_hom_app_inv_app_val_app_top_apply {Y : AlgebraicGeometry.Scheme.{u}}
    {F G : X.Modules ⥤ Y.Modules} (α : F ≅ G) (M : X.Modules)
    (y : ((G.obj M).val.obj (Opposite.op ⊤) : Type u)) :
    ((α.hom.app M).val.app (Opposite.op ⊤)).hom (((α.inv.app M).val.app (Opposite.op ⊤)).hom y) = y := by
  have h := congrArg (fun φ : G.obj M ⟶ G.obj M => (φ.val.app (Opposite.op ⊤)).hom y) (α.inv_hom_id_app M)
  exact h

/-- The `i`-th coordinate of the section `Σ_j ι_j(f_j)` of the biproduct `⨁ A` is `f_i`. -/
theorem biproduct_π_app_sum_ι_app {n : ℕ} (A : Fin n → X.Modules)
    (f : ∀ j, ((A j).val.obj (Opposite.op ⊤) : Type u)) (i : Fin n) :
    ((biproduct.π A i).val.app (Opposite.op ⊤)).hom
      (∑ j, ((biproduct.ι A j).val.app (Opposite.op ⊤)).hom (f j)) = f i := by
  rw [map_sum, Finset.sum_eq_single i]
  · exact congrArg (fun φ : A i ⟶ A i => (φ.val.app (Opposite.op ⊤)).hom (f i))
      (biproduct.ι_π_self A i)
  · intro j _ hj
    have h := congrArg (fun φ : A j ⟶ A i => (φ.val.app (Opposite.op ⊤)).hom (f j))
      (biproduct.ι_π_ne A hj)
    change ((biproduct.π A i).val.app (Opposite.op ⊤)).hom (((biproduct.ι A j).val.app (Opposite.op ⊤)).hom (f j)) =
      ((0 : A j ⟶ A i).val.app (Opposite.op ⊤)).hom (f j) at h
    exact h.trans rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

end AlgebraicGeometry.Scheme.Modules

/-- Pullback along equal morphisms: `totalSpaceHomEquiv` transported by `pullbackCongr`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_congr {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {S : AlgebraicGeometry.Scheme.{u}}
    {g g' : S ⟶ X} (h : g = g') (m : CategoryTheory.Over.mk g ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk g) m =
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).inv.app V).app ⊤
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk g')
          (CategoryTheory.Over.homMk m.left (by simp [← h]))) := by
  subst h
  have hm : (CategoryTheory.Over.homMk m.left (by simp) :
      CategoryTheory.Over.mk g ⟶ AlgebraicGeometry.Scheme.totalSpace V) = m :=
    CategoryTheory.Over.OverMorphism.ext rfl
  rw [hm]
  rfl

/-- `totalSpaceSectionEquiv V s₀` as a morphism `Over.mk (𝟙 X) ⟶ Tot V`: the inverse of
`totalSpaceHomEquiv` applied to the image of `s₀` in `Γ(X, (𝟙 X)^*V)` under `pullbackId` (unfolding
the definition of `totalSpaceSectionEquiv`). -/
theorem AlgebraicGeometry.Scheme.totalSpaceSectionEquiv_homMk_eq {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (s₀ : (V.val.obj (Opposite.op ⊤) : Type u)) :
    (CategoryTheory.Over.homMk
      ((CategoryTheory.Over.homMk (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv V s₀).1 rfl :
        CategoryTheory.Over.mk ((AlgebraicGeometry.Scheme.totalSpaceSectionEquiv V s₀).1 ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom) ⟶ AlgebraicGeometry.Scheme.totalSpace V) ≫
        CategoryTheory.CategoryStruct.id _).left
      (by simpa using (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv V s₀).2) :
      CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X) ⟶ AlgebraicGeometry.Scheme.totalSpace V) =
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X))).symm
      ((((AlgebraicGeometry.Scheme.Modules.pullbackId X).inv.app V).val.app (Opposite.op ⊤)).hom s₀) := by
  refine CategoryTheory.Over.OverMorphism.ext ?_
  change (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv V s₀).1 ≫
    CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Scheme.totalSpace V).left = _
  rw [CategoryTheory.Category.comp_id]
  rfl

/-- General form: for a global section `s₀` of `V = ⨁ A` with corresponding section `σ` of `Tot V`
(`totalSpaceSectionEquiv`), the `i`-th coordinate of the tautological section pulled back along `σ`,
read through the canonical isomorphisms `pullbackComp`, `pullbackCongr`, `pullbackId`, is the `i`-th
coordinate `π_i(s₀)` of `s₀`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceSectionEquiv_coordinate {X : AlgebraicGeometry.Scheme.{u}}
    {n : ℕ} (A : Fin n → X.Modules) [(⨁ A).IsLocallyFree] [(⨁ A).IsFiniteType]
    (s₀ : ((⨁ A).val.obj (Opposite.op ⊤) : Type u)) (i : Fin n) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp
          (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (⨁ A) s₀).1
          (AlgebraicGeometry.Scheme.totalSpace (⨁ A)).hom).hom.app (A i) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr
          (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (⨁ A) s₀).2).hom.app (A i) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app (A i)).val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (⨁ A) s₀).1
        ((((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace (⨁ A)).hom).map
            (biproduct.π A i)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) (AlgebraicGeometry.Scheme.totalSpace (⨁ A))
            (CategoryTheory.CategoryStruct.id _)))) =
    ((biproduct.π A i).val.app (Opposite.op ⊤)).hom s₀ := by
  have hσ := (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (⨁ A) s₀).2
  -- naturality of the coordinates
  have hA := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate A
    (AlgebraicGeometry.Scheme.totalSpace (⨁ A)) (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (⨁ A) s₀).1
    (CategoryTheory.CategoryStruct.id _) i
  -- transport along `σ ≫ π = 𝟙` and unfold the definition of `σ`
  have hB := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_congr (⨁ A) hσ
    ((CategoryTheory.Over.homMk (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (⨁ A) s₀).1 rfl :
      CategoryTheory.Over.mk ((AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (⨁ A) s₀).1 ≫
        (AlgebraicGeometry.Scheme.totalSpace (⨁ A)).hom) ⟶ AlgebraicGeometry.Scheme.totalSpace (⨁ A)) ≫
      CategoryTheory.CategoryStruct.id _)
  have hleft := AlgebraicGeometry.Scheme.totalSpaceSectionEquiv_homMk_eq (⨁ A) s₀
  rw [hleft, Equiv.apply_symm_apply] at hB
  have hB' := hB.trans (AlgebraicGeometry.Scheme.Modules.hom_app_top_eq
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hσ).inv.app (⨁ A)) _)
  rw [hB'] at hA
  -- naturality of `pullbackCongr` and `pullbackId`
  have hC := AlgebraicGeometry.Scheme.Modules.natTrans_naturality_val_app_top_apply
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hσ).inv (biproduct.π A i)
    ((((AlgebraicGeometry.Scheme.Modules.pullbackId X).inv.app (⨁ A)).val.app (Opposite.op ⊤)).hom s₀)
  have hD := (AlgebraicGeometry.Scheme.Modules.natTrans_naturality_val_app_top_apply
    (AlgebraicGeometry.Scheme.Modules.pullbackId X).inv (biproduct.π A i) s₀).trans
    (congrArg (fun y => (((AlgebraicGeometry.Scheme.Modules.pullbackId X).inv.app (A i)).val.app (Opposite.op ⊤)).hom y)
      (AlgebraicGeometry.Scheme.Modules.id_functor_map_val_app_top_apply (biproduct.π A i) s₀))
  have hA' := hA.symm.trans (hC.trans (congrArg
    (fun y => (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hσ).inv.app (A i)).val.app (Opposite.op ⊤)).hom y)
    hD))
  have h1 := AlgebraicGeometry.Scheme.Modules.natIso_hom_app_inv_app_val_app_top_apply
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hσ) (A i)
    ((((AlgebraicGeometry.Scheme.Modules.pullbackId X).inv.app (A i)).val.app (Opposite.op ⊤)).hom
      (((biproduct.π A i).val.app (Opposite.op ⊤)).hom s₀))
  have h2 := AlgebraicGeometry.Scheme.Modules.natIso_hom_app_inv_app_val_app_top_apply
    (AlgebraicGeometry.Scheme.Modules.pullbackId X) (A i) (((biproduct.π A i).val.app (Opposite.op ⊤)).hom s₀)
  refine (AlgebraicGeometry.Scheme.Modules.comp_val_app_top_apply _ _ _).trans ?_
  refine (AlgebraicGeometry.Scheme.Modules.comp_val_app_top_apply _ _ _).trans ?_
  exact (congrArg (fun y => (((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app (A i)).val.app
      (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackCongr hσ).hom.app (A i)).val.app (Opposite.op ⊤)).hom y)) hA').trans
    ((congrArg (fun y => (((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app (A i)).val.app
      (Opposite.op ⊤)).hom y) h1).trans h2)


end
