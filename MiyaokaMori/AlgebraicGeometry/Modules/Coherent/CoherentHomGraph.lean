import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesInternalHom
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact

/-! # Extending a stalk map to a morphism of coherent sheaves, step 2: the graph of `φ : G|_V → F|_V`

Given `φ ∈ Hom_{O_V}(G|_V, F|_V) = localHomSubmodule G F V` (`V ⊆ X` open, `j := V.ι`), we build
* `pushRestrict F = j_* j^* F` (Mathlib `pushforward`/`restrict`; sections over `W` are `F(V ∩ W)`),
* `α : G ⟶ j_* j^* F`, the adjoint of `φ` (`restrictAdjunction`), `β : F ⟶ j_* j^* F` the unit,
* `k := (α, -β) : G ⊕ F ⟶ j_* j^* F` and the **graph** `G' := ker k = G ×_{j_* j^* F} F`,
  with `ι := pr₁ : G' ⟶ G`, `ψ := pr₂ : G' ⟶ F`,
and prove the stalk statements at a point `ξ ∈ V` (route (b) of the docstring of
`CoherentDevissageSupportSubset_StalkHomSpread.lean`): if `φ` realises `f : G_ξ → F_ξ` on germs
(`f [W, a] = [W, φ_W a]`), then `ι_ξ` is bijective and `ψ_ξ = f ∘ ι_ξ`.

Proof of the stalk statements (all elementwise, no computation of the stalk of a kernel):
`β_ξ` is injective (a germ `[W, t]` with `[W, t|_{V ∩ W}] = 0` vanishes on a neighbourhood
`V ∩ W' ∋ ξ`), `α_ξ = β_ξ ∘ f` (both send `[W, m]` to `[W, φ(m|_{V ∩ W})]`), and the stalk functor is
additive and preserves kernels (`ModulesStalkExact`); for `e ∈ G'_ξ` with image `p = (a, b) ∈ G_ξ ⊕ F_ξ`
we get `0 = k_ξ p = α_ξ a - β_ξ b = β_ξ (f a - b)`, so `b = f a`. Hence `ι_ξ e = a` determines
`p`, hence `e` (`(ker k)_ξ → (G ⊕ F)_ξ` is injective), and every `a` is hit by lifting `(a, f a) ∈ ker k_ξ`.

Coherence and support of `G'` are proved in `…_StalkHomSpread_Coherent.lean` (needs Stacks 01LC,
01IC, 01Y1). Source: Stacks 01Y8 (extension of morphisms of coherent sheaves), via the fibre product
formulation. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.StalkHomSpread

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (G F : X.Modules) {V : X.Opens}

/-- `V.ι ''ᵁ W₀ ≤ V` for an open `W₀` of `V`. -/
theorem image_le_self (W₀ : V.toScheme.Opens) : V.ι ''ᵁ W₀ ≤ V :=
  (V.ι.image_le_opensRange W₀).trans V.opensRange_ι.le

/-- The object of `Over V` given by `V.ι ''ᵁ W₀`. -/
abbrev ovImage (W₀ : V.toScheme.Opens) : CategoryTheory.Over V :=
  CategoryTheory.Over.mk (homOfLE (image_le_self (V := V) W₀))

variable (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule G F V)

/-- The morphism `G|_V ⟶ F|_V` of restricted modules given by `φ ∈ Hom_{O_V}(G|_V, F|_V)`. -/
def restrictHom : G.restrict V.ι ⟶ F.restrict V.ι :=
  SheafOfModules.Hom.mk (PresheafOfModules.homMk
    { app := fun W₀ => AddCommGrpCat.ofHom (φ.1 (ovImage W₀.unop)).toAddMonoidHom
      naturality := fun {W₂ W₁} i => by
        ext m
        exact φ.2 (ovImage W₁.unop) (ovImage W₂.unop)
          (CategoryTheory.Over.homMk (V.ι.opensFunctor.map i.unop) rfl) m }
    (fun W₀ r m => (φ.1 (ovImage W₀.unop)).map_smul ((V.ι.appIso W₀.unop).inv r) m))

theorem restrictHom_app (W₀ : V.toScheme.Opens) (m : Γ(G.restrict V.ι, W₀)) :
    (restrictHom G F φ).app W₀ m = φ.1 (ovImage W₀) m := rfl

/-- `j_* j^* F` for the open immersion `j = V.ι` (sections over `W`: `F(V ∩ W)`). -/
abbrev pushRestrict : X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pushforward V.ι).obj (F.restrict V.ι)

/-- `α : G ⟶ j_* j^* F`, the adjoint of `φ : G|_V ⟶ F|_V`. -/
def alpha : G ⟶ pushRestrict F (V := V) :=
  ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction V.ι).homEquiv G (F.restrict V.ι))
    (restrictHom G F φ)

/-- `β : F ⟶ j_* j^* F`, the unit (restriction of sections to `V ∩ W`). -/
def beta : F ⟶ pushRestrict F (V := V) :=
  (AlgebraicGeometry.Scheme.Modules.restrictAdjunction V.ι).unit.app F

theorem alpha_app (W : X.Opens) (m : Γ(G, W)) :
    (alpha G F φ).app W m =
      φ.1 (ovImage (V.ι ⁻¹ᵁ W)) (G.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op m) := by
  simp only [alpha, Adjunction.homEquiv_unit]
  rfl

theorem beta_app (W : X.Opens) (m : Γ(F, W)) :
    (beta F (V := V)).app W m = F.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op m := rfl

/-- `k = (α, -β) : G ⊕ F ⟶ j_* j^* F`; its kernel is the graph of `φ`, extended to `X`. -/
def kmap : G ⊞ F ⟶ pushRestrict F (V := V) :=
  biprod.desc (alpha G F φ) (-(beta F))

/-- `G' := ker k = G ×_{j_* j^* F} F`. -/
abbrev graph : X.Modules := kernel (kmap G F φ)

/-- `ι : G' ⟶ G`. -/
def graphFst : graph G F φ ⟶ G := kernel.ι (kmap G F φ) ≫ biprod.fst

/-- `ψ : G' ⟶ F`. -/
def graphSnd : graph G F φ ⟶ F := kernel.ι (kmap G F φ) ≫ biprod.snd

/-- Germ formula for the stalk functor: `ψ_x [W, m] = [W, ψ_W m]`. -/
theorem stalkFunctor_map_hom_germ {M N : X.Modules} (ψ : M ⟶ N) (x : X) (W : X.Opens) (hx : x ∈ W)
    (m : Γ(M, W)) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map ψ).hom (M.presheaf.germ W x hx m) =
      N.presheaf.germ W x hx (ψ.app W m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx ψ.mapPresheaf m

/-! ### Stalks at a point `ξ ∈ V` -/

theorem mem_image_preimage_iff (W : X.Opens) (x : X) :
    x ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) ↔ x ∈ V ∧ x ∈ W := by
  rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Opens.opensRange_ι]
  rfl

variable (ξ : X)

/-- The stalk functor is additive. -/
theorem stalkFunctor_additive : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).Additive := by
  have := (AlgebraicGeometry.Scheme.Modules.stalk_preservesFiniteLimits_colimits ξ).1
  have : PreservesBinaryBiproducts (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- `β_ξ` is injective for `ξ ∈ V` (the germ of `t` at `ξ ∈ V` is determined by `t|_{V ∩ W}`). -/
theorem beta_stalk_injective (hξV : ξ ∈ V) :
    Function.Injective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (beta F (V := V))).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨W, hξW, m, rfl⟩ := F.presheaf.exists_germ_eq a
  rw [stalkFunctor_map_hom_germ] at ha
  have h0 : (pushRestrict F (V := V)).presheaf.germ W ξ hξW ((beta F (V := V)).app W m) =
      (pushRestrict F (V := V)).presheaf.germ W ξ hξW 0 := by
    rw [ha]
    exact (map_zero _).symm
  obtain ⟨W', hξW', iU, iV, hW'⟩ := (pushRestrict F (V := V)).presheaf.germ_eq ξ hξW hξW _ _ h0
  rw [map_zero] at hW'
  have hξ'' : ξ ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ W') := (mem_image_preimage_iff W' ξ).mpr ⟨hξV, hξW'⟩
  have hle : V.ι ''ᵁ (V.ι ⁻¹ᵁ W') ≤ W := (V.ι.image_preimage_le W').trans iU.le
  have key : F.presheaf.map (homOfLE hle).op m = 0 := by
    have : F.presheaf.map (homOfLE hle).op m =
        F.presheaf.map (V.ι.opensFunctor.map ((Opens.map V.ι.base).map iU)).op
          (F.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op m) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [this]
    exact hW'
  rw [← F.presheaf.germ_res_apply (homOfLE hle) ξ hξ'' m, key]
  exact map_zero _

/-- `α_ξ = β_ξ ∘ f` when `φ` realises `f` on germs. -/
theorem alpha_stalk_eq (hξV : ξ ∈ V) (f : G.stalk ξ →ₗ[X.presheaf.stalk ξ] F.stalk ξ)
    (hf : ∀ (W : CategoryTheory.Over V) (hξW : ξ ∈ W.left) (a : Γ(G, W.left)),
      f (G.presheaf.germ W.left ξ hξW a) = F.presheaf.germ W.left ξ hξW (φ.1 W a))
    (a : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj G) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (alpha G F φ)).hom a =
      ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (beta F (V := V))).hom (f a) := by
  obtain ⟨W, hξW, m, rfl⟩ := G.presheaf.exists_germ_eq a
  have hξ'' : ξ ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) := (mem_image_preimage_iff W ξ).mpr ⟨hξV, hξW⟩
  set m' : Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ W)) := G.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op m
    with hm'
  have h1 : f (G.presheaf.germ W ξ hξW m) =
      F.presheaf.germ _ ξ hξ'' (φ.1 (ovImage (V.ι ⁻¹ᵁ W)) m') := by
    rw [← G.presheaf.germ_res_apply (homOfLE (V.ι.image_preimage_le W)) ξ hξ'' m]
    exact hf (ovImage (V.ι ⁻¹ᵁ W)) hξ'' m'
  rw [h1, stalkFunctor_map_hom_germ, stalkFunctor_map_hom_germ, alpha_app]
  exact ((pushRestrict F (V := V)).presheaf.germ_res_apply
    (homOfLE (V.ι.image_preimage_le W)) ξ hξ'' (φ.1 (ovImage (V.ι ⁻¹ᵁ W)) m')).symm

/-! ### The stalk of the graph -/

section StalkGraph

theorem hom_apply_of_eq {R : Type u} [Ring R] {M N : ModuleCat.{u} R} {f g : M ⟶ N} (h : f = g)
    (x : M) : f.hom x = g.hom x := by rw [h]

theorem map_k_inl (a : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj G) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ)).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inl).hom a) = ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (alpha G F φ)).hom a := by
  have h : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inl ≫ (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ) = (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (alpha G F φ) := by
    rw [← CategoryTheory.Functor.map_comp, kmap, biprod.inl_desc]
  have := hom_apply_of_eq h a
  rwa [ModuleCat.hom_comp, LinearMap.comp_apply] at this

theorem map_k_inr (b : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj F) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ)).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inr).hom b) = -((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (beta F (V := V))).hom b := by
  have := stalkFunctor_additive ξ
  have h : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inr ≫ (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ) = -(AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (beta F (V := V)) := by
    rw [← CategoryTheory.Functor.map_comp, kmap, biprod.inr_desc, CategoryTheory.Functor.map_neg]
  have := hom_apply_of_eq h b
  rwa [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg, LinearMap.neg_apply] at this

theorem map_fst_inl (a : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj G) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (biprod.fst : G ⊞ F ⟶ G)).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inl).hom a) = a := by
  have h : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (biprod.inl : G ⟶ G ⊞ F) ≫ (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.fst = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id]
  have := hom_apply_of_eq h a
  rwa [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at this

theorem map_fst_inr (b : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj F) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (biprod.fst : G ⊞ F ⟶ G)).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inr).hom b) = 0 := by
  have := stalkFunctor_additive ξ
  have h : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (biprod.inr : F ⟶ G ⊞ F) ≫ (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.fst = 0 := by
    rw [← CategoryTheory.Functor.map_comp, biprod.inr_fst, CategoryTheory.Functor.map_zero]
  have := hom_apply_of_eq h b
  rwa [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at this

theorem map_total (q : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj (G ⊞ F)) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inl).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.fst).hom q) +
      ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inr).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.snd).hom q) = q := by
  have := stalkFunctor_additive ξ
  have h : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (biprod.fst : G ⊞ F ⟶ G) ≫ (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inl +
      (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (biprod.snd : G ⊞ F ⟶ F) ≫ (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inr = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_add, biprod.total, CategoryTheory.Functor.map_id]
  have := hom_apply_of_eq h q
  rwa [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at this

theorem map_k_kernelι (e : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj (graph G F φ)) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ)).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ))).hom e) = 0 := by
  have := stalkFunctor_additive ξ
  have h : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ)) ≫ (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ) = 0 := by
    rw [← CategoryTheory.Functor.map_comp, kernel.condition, CategoryTheory.Functor.map_zero]
  have := hom_apply_of_eq h e
  rwa [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at this

theorem kernelι_stalk_injective :
    Function.Injective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ))).hom := by
  have := (AlgebraicGeometry.Scheme.Modules.stalk_preservesFiniteLimits_colimits ξ).1
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

theorem exists_kernelι_stalk_eq (p : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj (G ⊞ F)) (hp : ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ)).hom p = 0) :
    ∃ e : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj (graph G F φ), ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ))).hom e = p := by
  have := (AlgebraicGeometry.Scheme.Modules.stalk_preservesFiniteLimits_colimits ξ).1
  let q := (ModuleCat.kernelIsoKer ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ))).inv
    (⟨p, LinearMap.mem_ker.mpr hp⟩ :
      LinearMap.ker ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ)).hom)
  refine ⟨(PreservesKernel.iso (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ) (kmap G F φ)).inv q, ?_⟩
  have h1 := hom_apply_of_eq (PreservesKernel.iso_inv_ι (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ) (kmap G F φ)) q
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1]
  exact ModuleCat.kernelIsoKer_inv_kernel_ι_apply _ _

theorem graphFst_stalk_apply (e : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj (graph G F φ)) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (graphFst G F φ)).hom e =
      ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (biprod.fst : G ⊞ F ⟶ G)).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ))).hom e) := by
  rw [graphFst, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem graphSnd_stalk_apply (e : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj (graph G F φ)) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (graphSnd G F φ)).hom e =
      ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (biprod.snd : G ⊞ F ⟶ F)).hom (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ))).hom e) := by
  rw [graphSnd, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

variable (hξV : ξ ∈ V) (f : G.stalk ξ →ₗ[X.presheaf.stalk ξ] F.stalk ξ)
  (hf : ∀ (W : CategoryTheory.Over V) (hξW : ξ ∈ W.left) (a : Γ(G, W.left)),
    f (G.presheaf.germ W.left ξ hξW a) = F.presheaf.germ W.left ξ hξW (φ.1 W a))

include hξV hf

/-- `ψ_ξ = f ∘ ι_ξ` on the stalk of the graph. -/
theorem graphSnd_stalk_eq (e : (AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).obj (graph G F φ)) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (graphSnd G F φ)).hom e = f (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (graphFst G F φ)).hom e) := by
  rw [graphFst_stalk_apply, graphSnd_stalk_apply]
  set p := ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ))).hom e with hp
  have hk : ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kmap G F φ)).hom p = 0 := map_k_kernelι G F φ ξ e
  rw [← map_total G F ξ p, map_add, map_k_inl, map_k_inr, alpha_stalk_eq G F φ ξ hξV f hf,
    ← sub_eq_add_neg, sub_eq_zero] at hk
  exact (beta_stalk_injective F ξ hξV hk).symm

/-- `ι_ξ` is bijective on the stalk of the graph. -/
theorem graphFst_stalk_bijective : Function.Bijective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (graphFst G F φ)).hom := by
  constructor
  · intro e₁ e₂ h
    apply kernelι_stalk_injective G F φ ξ
    have h2 := graphSnd_stalk_eq G F φ ξ hξV f hf e₁
    have h3 := graphSnd_stalk_eq G F φ ξ hξV f hf e₂
    rw [graphSnd_stalk_apply] at h2 h3
    have h' := h
    rw [graphFst_stalk_apply, graphFst_stalk_apply] at h'
    rw [← map_total G F ξ
        (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ))).hom e₁),
      ← map_total G F ξ
        (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map (kernel.ι (kmap G F φ))).hom e₂),
      h2, h3, h', h]
  · intro a
    have := stalkFunctor_additive ξ
    have h2 := map_k_inr G F φ ξ (f a)
    have h3 := map_fst_inr G F ξ (f a)
    obtain ⟨e, he⟩ := exists_kernelι_stalk_eq G F φ ξ
      (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inl).hom a +
        ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map biprod.inr).hom (f a)) (by
        rw [map_add, map_k_inl, h2, alpha_stalk_eq G F φ ξ hξV f hf, add_neg_cancel])
    refine ⟨e, ?_⟩
    rw [graphFst_stalk_apply, he, map_add, map_fst_inl, h3, add_zero]

end StalkGraph

end MiyaokaMori.StalkHomSpread

end
