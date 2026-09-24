import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift

/-! # Short exact sequences with locally free quotient split locally

A short exact sequence of `O_X`-modules whose quotient is finite locally free splits locally: every
point `x` has an open neighbourhood `U` on which the restricted sequence is isomorphic to
`F|_U → F|_U ⊕ H|_U → H|_U`.

Reference: the standard local argument (as in Stacks 01CA).

Proof route:
1. `S.X₃` locally free of finite type ⇒ there are `U₀ ∋ x` and
   `e₀ : (restrictFunctor U₀.ι).obj S.X₃ ≅ free I` with `I` finite
   (`exists_pullback_iso_free_of_isLocallyFree` + `finite_index_of_restrict_iso_free` +
   `restrictFunctorIsoPullback`).
2. Basis elements `b_i := ιFree i ≫ e₀.inv : unit ⟶ (restrictFunctor U₀.ι).obj S.X₃`, with values
   `s_i := b_i.app ⊤ 1 ∈ Γ(S.X₃, U₀.ι ''ᵁ ⊤)` on `⊤`.
3. `S.g` epi ⇒ locally surjective on sections (`epi_iff_locally_surjective_sections`): each `s_i` lifts
   to `u_i ∈ Γ(S.X₂, V_i)` on some open neighbourhood `V_i` of `x`. Put `W := U₀ ⊓ ⨅ i, V_i` (`I` is
   finite; `⨅` over empty `I` is `⊤`, hence the intersection with `U₀`).
4. Let `j : W ⟶ U₀`, `F := restrictFunctor j`, `G := restrictFunctor U₀.ι ⋙ F`. The isomorphism
   `e_W : G.obj S.X₃ ≅ free I` is `F.mapIso e₀` composed with `mapFreeIso F I η`,
   `η := (restrictUnitIso j).symm`. Restricting the `u_i` to the opens of `W` gives a family of
   sections `sec_i` of `G.obj S.X₂`; `τ := freeHomEquiv.symm sec`, `σ := e_W.hom ≫ τ`.
5. `σ ≫ G.map S.g = 𝟙` ⟺ `τ ≫ G.map S.g = e_W.inv`; by the universal property of the free sheaf it
   suffices to compare on each `ιFree i`; both sides are morphisms `unit ⟶ G.obj S.X₃`, which
   `unitHomEquiv` turns into equalities of families of sections, both equal to the restriction of
   `s_i` on every open `Y ⊆ W`.
6. Transport the right inverse along `G ≅ pullback W.ι` (`restrictFunctorComp`,
   `restrictFunctorCongr`, `restrictFunctorIsoPullback`) by naturality.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

namespace MiyaokaMori.LocallySplit

section Helpers

variable {Y' Y : Scheme.{u}} (f : Y' ⟶ Y) [IsOpenImmersion f] {P Q : Y.Modules} (φ : P ⟶ Q)

/-- The component on an open `U` of a morphism restricted along an open immersion is the component of
the original morphism on `f ''ᵁ U`. -/
theorem restrictFunctor_map_app (U : Y'.Opens) :
    ((Scheme.Modules.restrictFunctor f).map φ).app U = φ.app (f ''ᵁ U) := rfl

/-- The restriction maps of a sheaf restricted along an open immersion are those of the original
sheaf. -/
theorem restrictFunctor_obj_map {U V : Y'.Opens} (h : V ≤ U) (t : Γ(P, f ''ᵁ U)) :
    ((Scheme.Modules.restrictFunctor f).obj P).presheaf.map (homOfLE h).op t =
      P.presheaf.map (homOfLE (Scheme.Hom.image_mono f h)).op t := rfl

/-- `(restrictUnitIso f).inv` sends `1` to `1` (its components are the ring isomorphisms
`(f.appIso W).inv`). -/
theorem restrictUnitIso_inv_app_one (W : Y'.Opens) :
    ((Scheme.Modules.restrictUnitIso f).inv.app W) (1 : Γ(Y', W)) = (1 : Γ(Y, f ''ᵁ W)) :=
  map_one (f.appIso W).inv.hom

/-- The restriction maps of the structure sheaf `unit` preserve `1`. -/
theorem unit_presheaf_map_one {W W' : Y.Opens} (hW : W' ≤ W) :
    (Scheme.Modules.presheaf (SheafOfModules.unit Y.ringCatSheaf)).map (homOfLE hW).op
        (1 : Γ(Y, W)) = (1 : Γ(Y, W')) :=
  map_one (Y.presheaf.map (homOfLE hW).op).hom

/-- `Hom.app` commutes with restriction. -/
theorem app_map {W W' : Y.Opens} (hW : W' ≤ W) (a : Γ(P, W)) :
    φ.app W' (P.presheaf.map (homOfLE hW).op a) = Q.presheaf.map (homOfLE hW).op (φ.app W a) := by
  have := congr($(φ.mapPresheaf.naturality (homOfLE hW).op) a)
  simpa using this

/-- The value of `unitHomEquiv` on an open `W`: where `1` is sent. -/
theorem unitHomEquiv_val (ψ : SheafOfModules.unit Y.ringCatSheaf ⟶ P) (W : Y.Opens) :
    (P.unitHomEquiv ψ).val (op W) = Scheme.Modules.Hom.app ψ W (1 : Γ(Y, W)) := rfl

theorem unitHomEquiv_symm_app_one (s : P.sections) (W : Y.Opens) :
    Scheme.Modules.Hom.app (P.unitHomEquiv.symm s) W (1 : Γ(Y, W)) = s.val (op W) :=
  congrArg (fun z => z.val (op W)) (P.unitHomEquiv.apply_symm_apply s)

/-- The family of sections obtained from a section over `⊤` (restrict to each open). -/
def sectionOfTop (a : Γ(P, ⊤)) : P.sections :=
  PresheafOfModules.sectionsMk (fun W => (P.presheaf.map (homOfLE le_top).op a : Γ(P, W.unop)))
    (by
      intro W W' k
      change P.presheaf.map k (P.presheaf.map _ a) = P.presheaf.map _ a
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

theorem sectionOfTop_val (a : Γ(P, ⊤)) (W : Y.Opens) :
    (sectionOfTop a).val (op W) = P.presheaf.map (homOfLE le_top).op a := rfl

end Helpers

set_option backward.isDefEq.respectTransparency false in
/-- General form: if `g : M ⟶ N` is an epimorphism and `N` is trivialized on `U₀ ∋ x` as a free sheaf
of finite rank, then on a smaller neighbourhood `W ≤ U₀` of `x` the morphism `g` has a right inverse
(expressed with `restrictFunctor U₀.ι ⋙ restrictFunctor (X.homOfLE hW)`). -/
theorem exists_le_rightInverse_of_epi_of_iso_free {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) [Epi g] (U₀ : X.Opens) (x : X) (hx : x ∈ U₀) (I : Type u) [Finite I]
    (e₀ : (Scheme.Modules.restrictFunctor U₀.ι).obj N ≅
      SheafOfModules.free (R := U₀.toScheme.ringCatSheaf) I) :
    ∃ (W : X.Opens) (hW : W ≤ U₀) (_ : x ∈ W)
      (σ : (Scheme.Modules.restrictFunctor U₀.ι ⋙
          Scheme.Modules.restrictFunctor (X.homOfLE hW)).obj N ⟶
        (Scheme.Modules.restrictFunctor U₀.ι ⋙
          Scheme.Modules.restrictFunctor (X.homOfLE hW)).obj M),
      σ ≫ (Scheme.Modules.restrictFunctor U₀.ι ⋙
          Scheme.Modules.restrictFunctor (X.homOfLE hW)).map g = 𝟙 _ := by
  classical
  let R₀ : X.Modules ⥤ U₀.toScheme.Modules := Scheme.Modules.restrictFunctor U₀.ι
  -- the basis elements and their values on ⊤
  let b : I → (SheafOfModules.unit U₀.toScheme.ringCatSheaf ⟶ R₀.obj N) :=
    fun i => SheafOfModules.ιFree i ≫ e₀.inv
  let s : I → Γ(N, U₀.ι ''ᵁ ⊤) := fun i =>
    Scheme.Modules.Hom.app (b i) ⊤ (1 : Γ(U₀.toScheme, ⊤))
  have hloc := (Scheme.Modules.epi_iff_locally_surjective_sections g).mp inferInstance
  have hxU : x ∈ U₀.ι ''ᵁ ⊤ := by rw [Scheme.Opens.ι_image_top]; exact hx
  choose V hVU hxV u hu using fun i => hloc (U₀.ι ''ᵁ ⊤) (s i) x hxU
  let W : X.Opens := U₀ ⊓ ⨅ i, V i
  have hWU : W ≤ U₀ := inf_le_left
  have hWV : ∀ i, W ≤ V i := fun i => inf_le_right.trans (iInf_le _ i)
  have hxW : x ∈ W := ⟨hx, by
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV⟩
  let j : W.toScheme ⟶ U₀.toScheme := X.homOfLE hWU
  let F : U₀.toScheme.Modules ⥤ W.toScheme.Modules := Scheme.Modules.restrictFunctor j
  let G : X.Modules ⥤ W.toScheme.Modules := R₀ ⋙ F
  have himg : ∀ (Y : W.toScheme.Opens), U₀.ι ''ᵁ (j ''ᵁ Y) ≤ W := fun Y => by
    have h1 : (j ≫ U₀.ι) ''ᵁ Y = W.ι ''ᵁ Y := by simp only [j, Scheme.homOfLE_ι]
    rw [← Scheme.Hom.comp_image, h1]
    exact Scheme.Opens.ι_image_le W Y
  -- restrict the lifts `u i` to global sections on `W`, then expand into families of sections
  let t : I → Γ(G.obj M, ⊤) := fun i =>
    (M.presheaf.map (homOfLE ((himg ⊤).trans (hWV i))).op (u i) : Γ(M, U₀.ι ''ᵁ (j ''ᵁ ⊤)))
  let sec : I → (G.obj M).sections := fun i => sectionOfTop (t i)
  let τ : SheafOfModules.free (R := W.toScheme.ringCatSheaf) I ⟶ G.obj M :=
    (SheafOfModules.freeHomEquiv _).symm sec
  let η : SheafOfModules.unit W.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit U₀.toScheme.ringCatSheaf) :=
    (Scheme.Modules.restrictUnitIso j).symm
  have hF : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction j).leftAdjoint_preservesColimits.{u, u}
  have : PreservesColimitsOfShape (Discrete I) F := hF.preservesColimitsOfShape
  let eW : G.obj N ≅ SheafOfModules.free (R := W.toScheme.ringCatSheaf) I :=
    F.mapIso e₀ ≪≫ (SheafOfModules.mapFreeIso F I η).symm
  refine ⟨W, hWU, hxW, eW.hom ≫ τ, ?_⟩
  rw [Category.assoc, ← Iso.eq_inv_comp, Category.comp_id]
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I)
  intro i
  simp only [SheafOfModules.freeCofan_inj]
  have hL : SheafOfModules.ιFree i ≫ τ = (G.obj M).unitHomEquiv.symm (sec i) := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp [τ]
  have hR : SheafOfModules.ιFree i ≫ eW.inv = η.hom ≫ F.map (b i) := by
    simp only [eW, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
    rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc, ← F.map_comp]
  rw [← Category.assoc, hL, hR]
  apply (G.obj N).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro Yop
  induction Yop using Opposite.rec with | op Y => ?_
  rw [unitHomEquiv_val, unitHomEquiv_val, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, unitHomEquiv_symm_app_one,
    sectionOfTop_val]
  -- right side: η.hom = (restrictUnitIso j).inv sends 1 to 1; then naturality of b i
  have hη : Scheme.Modules.Hom.app η.hom Y (1 : Γ(W.toScheme, Y)) =
      (1 : Γ(U₀.toScheme, j ''ᵁ Y)) :=
    restrictUnitIso_inv_app_one j Y
  rw [hη, restrictFunctor_map_app]
  have hb : Scheme.Modules.Hom.app (b i) (j ''ᵁ Y) (1 : Γ(U₀.toScheme, j ''ᵁ Y)) =
      (R₀.obj N).presheaf.map (homOfLE le_top).op (s i) := by
    rw [← unit_presheaf_map_one (le_top : j ''ᵁ Y ≤ ⊤), app_map]
  -- left side: the components of G.map g are those of g (`restrictFunctor_map_app`,
  -- `restrictFunctor_obj_map` are rfl); the whole computation takes place on X
  have h₂ : U₀.ι ''ᵁ (j ''ᵁ Y) ≤ U₀.ι ''ᵁ (j ''ᵁ ⊤) :=
    Scheme.Hom.image_mono U₀.ι (Scheme.Hom.image_mono j le_top)
  have h₁ : U₀.ι ''ᵁ (j ''ᵁ Y) ≤ U₀.ι ''ᵁ ⊤ := ((himg Y).trans (hWV i)).trans (hVU i)
  have hl : Scheme.Modules.Hom.app g (U₀.ι ''ᵁ (j ''ᵁ Y))
      (M.presheaf.map (homOfLE h₂).op
        (M.presheaf.map (homOfLE ((himg ⊤).trans (hWV i))).op (u i))) =
      N.presheaf.map (homOfLE h₁).op (s i) := by
    rw [app_map, app_map, hu i, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hr : (R₀.obj N).presheaf.map (homOfLE (le_top : j ''ᵁ Y ≤ ⊤)).op (s i) =
      N.presheaf.map (homOfLE h₁).op (s i) :=
    restrictFunctor_obj_map U₀.ι le_top (s i)
  exact (hl.trans hr.symm).trans hb.symm

end MiyaokaMori.LocallySplit

theorem AlgebraicGeometry.Scheme.Modules.shortExact_locallySplit {X : AlgebraicGeometry.Scheme.{u}}
    {S : CategoryTheory.ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₃.IsLocallyFree] [S.X₃.IsFiniteType] (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (σ : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj S.X₃ ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj S.X₂),
      σ ≫ (AlgebraicGeometry.Scheme.Modules.pullback U.ι).map S.g = CategoryTheory.CategoryStruct.id _ := by
  obtain ⟨U₀, I, hxU₀, ⟨e⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree S.X₃ x
  have : Finite I := Scheme.Modules.finite_index_of_restrict_iso_free S.X₃ U₀ I e x hxU₀
  have : Epi S.g := hS.epi_g
  let e₀ : (Scheme.Modules.restrictFunctor U₀.ι).obj S.X₃ ≅
      SheafOfModules.free (R := U₀.toScheme.ringCatSheaf) I :=
    (Scheme.Modules.restrictFunctorIsoPullback U₀.ι).app S.X₃ ≪≫ e
  obtain ⟨W, hW, hxW, σ, hσ⟩ :=
    MiyaokaMori.LocallySplit.exists_le_rightInverse_of_epi_of_iso_free S.g U₀ x hxU₀ I e₀
  -- transport the right inverse along `G ≅ pullback W.ι` by naturality
  let Φ : Scheme.Modules.restrictFunctor U₀.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE hW) ≅
      Scheme.Modules.pullback W.ι :=
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hW) U₀.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hW) ≪≫
      Scheme.Modules.restrictFunctorIsoPullback W.ι
  refine ⟨W, hxW, Φ.inv.app S.X₃ ≫ σ ≫ Φ.hom.app S.X₂, ?_⟩
  have hnat := Φ.hom.naturality S.g
  rw [Category.assoc, Category.assoc, ← hnat, ← Category.assoc σ, hσ, Category.id_comp,
    Iso.inv_hom_id_app]

end
