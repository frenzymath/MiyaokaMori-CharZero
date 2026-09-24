import MiyaokaMori.Prelude

/-! # The stalk of a pullback is the extension of scalars of the stalk

Let `g : X ⟶ Y` be a morphism of schemes, `M` an `O_Y`-module on `Y` and `x ∈ X`. The canonical
linear map `modulePullbackStalkTensorMap g M x : O_{X,x} ⊗_{O_{Y,g x}} M_{g x} → (g^*M)_x`
(induced on stalks by the unit of the pullback–pushforward adjunction, then extended along
`g.stalkMap x`) is bijective. Hence there is an `O_{X,x}`-linear isomorphism
`(g^*M)_x ≅ O_{X,x} ⊗_{O_{Y,g x}} M_{g x}`, whose inverse sends the image of the unit (the pullback of
the germ of a section `s`) to `1 ⊗ s_{g x}`. No coherence, finite presentation, flatness or local
freeness is needed.

Proof:
1. Skyscraper modules: for `x ∈ X` and an `O_{X,x}`-module `N`, Mathlib's additive skyscraper
   `skyscraperPresheaf x N`, with scalars restricted along the germs of the structure sheaf, is a
   sheaf of modules `moduleSkyscraper X x N` on `X`; its sections on an open containing `x` are
   canonically `N` (`moduleSkyscraperSectionEquiv`), and trivial on opens not containing `x`.
2. Stalk–skyscraper adjunction (module version of Stacks `sheaves.tex`,
   `lemma-stalk-skyscraper-adjoint`): `Hom_{O_X}(M', moduleSkyscraper X x N) ≃ Hom_{O_{X,x}}(M'_x, N)`
   (`moduleSkyscraperHomEquiv`); pushforward version:
   `Hom_{O_Y}(M, g_*(moduleSkyscraper X x N)) ≃` semilinear maps `M_{g x} →ₛₗ[g.stalkMap x] N`
   (`modulePushforwardSkyscraperHomEquiv`).
3. Composing the two Hom isomorphisms of 2 with the pullback–pushforward adjunction gives
   `Hom_{O_{X,x}}((g^*M)_x, N) ≃ (M_{g x} →ₛₗ[g.stalkMap x] N)`, and this isomorphism is
   "precomposition with the stalk unit" (`modulePullbackStalkHomEquiv_apply`). So `(g^*M)_x` with its
   stalk unit satisfies the universal property of the extension of scalars
   `O_{X,x} ⊗_{O_{Y,g x}} M_{g x}`.
4. Take `N = O_{X,x} ⊗_{O_{Y,g x}} M_{g x}` and the tensor unit `m ↦ 1 ⊗ m` to get the inverse map;
   the two composites are the identity by induction on generators of the tensor product and by the
   uniqueness in the universal property (Stacks `sheaves.tex`, `lemma-stalk-pullback-modules`).

Sources: Stacks Project, `sheaves.tex`, `lemma-stalk-pullback-modules` and
`lemma-stalk-skyscraper-adjoint`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StalkSkyscraperPresheafAdjunctionAuxs
open scoped Classical TensorProduct

namespace MiyaokaMori.PullbackStalkTensor

open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false

/- ### 1. Skyscraper sheaves of modules -/

private abbrev skyscraperAdditive (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :=
  skyscraperPresheaf (X := (X : TopCat.{u})) x (AddCommGrpCat.of N)

private def skyscraperSectionEquiv (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U) :
    (skyscraperAdditive X x N).obj (op U) ≃+ N :=
  (eqToIso (if_pos hx)).addCommGroupIsoToAddEquiv

private theorem skyscraperSection_subsingleton (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∉ U) :
    Subsingleton ((skyscraperAdditive X x N).obj (op U)) := by
  simp only [skyscraperAdditive, skyscraperPresheaf_obj]
  rw [if_neg hx]
  constructor
  intro a b
  have h : (𝟙 (⊤_ AddCommGrpCat)) =
      (0 : (⊤_ AddCommGrpCat ⟶ ⊤_ AddCommGrpCat)) :=
    terminalIsTerminal.hom_ext _ _
  have ha := ConcreteCategory.congr_hom h a
  have hb := ConcreteCategory.congr_hom h b
  have ha' : a = 0 := by simpa using ha
  have hb' : b = 0 := by simpa using hb
  exact ha'.trans hb'.symm

private instance skyscraperSectionModule (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) :
    Module (X.presheaf.obj (op U)) ((skyscraperAdditive X x N).obj (op U)) := by
  by_cases hx : x ∈ U
  · letI : Module (X.presheaf.obj (op U)) N :=
      Module.compHom N (X.presheaf.germ U x hx).hom
    exact (skyscraperSectionEquiv X x N U hx).module (X.presheaf.obj (op U))
  · letI := skyscraperSection_subsingleton X x N U hx
    exact
      { smul := fun _ s ↦ s
        one_smul := fun _ ↦ Subsingleton.elim _ _
        mul_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        smul_zero := fun _ ↦ Subsingleton.elim _ _
        smul_add := fun _ _ _ ↦ Subsingleton.elim _ _
        add_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        zero_smul := fun _ ↦ Subsingleton.elim _ _ }

private theorem skyscraperSectionEquiv_smul (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U)
    (r : X.presheaf.obj (op U)) (s : (skyscraperAdditive X x N).obj (op U)) :
    skyscraperSectionEquiv X x N U hx (r • s) =
      X.presheaf.germ U x hx (r : X.presheaf.obj (op U)) •
        skyscraperSectionEquiv X x N U hx s := by
  change skyscraperSectionEquiv X x N U hx
    (@SMul.smul _ _ (skyscraperSectionModule X x N U).toSMul r s) = _
  letI : Module (X.presheaf.obj (op U)) N :=
    Module.compHom N (X.presheaf.germ U x hx).hom
  have hinst : skyscraperSectionModule X x N U =
      (skyscraperSectionEquiv X x N U hx).module (X.presheaf.obj (op U)) := by
    simp [skyscraperSectionModule, hx]
  rw [hinst]
  exact (skyscraperSectionEquiv X x N U hx).apply_symm_apply _

private instance skyscraperSectionModuleRing (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) :
    Module (X.ringCatSheaf.obj.obj (op U)) ((skyscraperAdditive X x N).obj (op U)) := by
  by_cases hx : x ∈ U
  · letI : Module (X.ringCatSheaf.obj.obj (op U)) N :=
      Module.compHom N (X.presheaf.germ U x hx).hom
    exact (skyscraperSectionEquiv X x N U hx).module (X.ringCatSheaf.obj.obj (op U))
  · letI := skyscraperSection_subsingleton X x N U hx
    exact
      { smul := fun _ s ↦ s
        one_smul := fun _ ↦ Subsingleton.elim _ _
        mul_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        smul_zero := fun _ ↦ Subsingleton.elim _ _
        smul_add := fun _ _ _ ↦ Subsingleton.elim _ _
        add_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        zero_smul := fun _ ↦ Subsingleton.elim _ _ }

private theorem skyscraperSectionEquiv_smulRing (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U)
    (r : X.ringCatSheaf.obj.obj (op U))
    (s : (skyscraperAdditive X x N).obj (op U)) :
    skyscraperSectionEquiv X x N U hx (r • s) =
      X.presheaf.germ U x hx r • skyscraperSectionEquiv X x N U hx s := by
  change skyscraperSectionEquiv X x N U hx
    (@SMul.smul _ _ (skyscraperSectionModuleRing X x N U).toSMul r s) = _
  letI : Module (X.ringCatSheaf.obj.obj (op U)) N :=
    Module.compHom N (X.presheaf.germ U x hx).hom
  have hinst : skyscraperSectionModuleRing X x N U =
      (skyscraperSectionEquiv X x N U hx).module (X.ringCatSheaf.obj.obj (op U)) := by
    simp [skyscraperSectionModuleRing, hx]
  rw [hinst]
  exact (skyscraperSectionEquiv X x N U hx).apply_symm_apply _

private theorem skyscraperSectionEquiv_restrict (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U V : X.Opens)
    (i : V ⟶ U) (hx : x ∈ V) (s : (skyscraperAdditive X x N).obj (op U)) :
    skyscraperSectionEquiv X x N V hx ((skyscraperAdditive X x N).map i.op s) =
      skyscraperSectionEquiv X x N U (i.le hx) s := by
  have h : (skyscraperAdditive X x N).map i.op ≫ eqToHom (if_pos hx) =
      eqToHom (if_pos (i.le hx)) := by
    simp only [skyscraperAdditive, skyscraperPresheaf_map, dif_pos hx]
    exact eqToHom_trans _ _
  exact CategoryTheory.congr_fun h s

private instance skyscraperSectionModuleOp (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) ((skyscraperAdditive X x N).obj U) :=
  by simpa only [op_unop] using (skyscraperSectionModule X x N U.unop)

private instance skyscraperSectionModuleRingOp (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((skyscraperAdditive X x N).obj U) :=
  by simpa only [op_unop] using (skyscraperSectionModuleRing X x N U.unop)

private theorem skyscraper_map_smul (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (r : X.ringCatSheaf.obj.obj U)
    (s : (skyscraperAdditive X x N).obj U) :
    (skyscraperAdditive X x N).map i (r • s) =
      X.ringCatSheaf.obj.map i r • (skyscraperAdditive X x N).map i s := by
  by_cases hx : x ∈ V.unop
  · apply (skyscraperSectionEquiv X x N V.unop hx).injective
    have h₁ := skyscraperSectionEquiv_restrict X x N U.unop V.unop i.unop hx (r • s)
    have h₂ := skyscraperSectionEquiv_restrict X x N U.unop V.unop i.unop hx s
    simp only [skyscraperAdditive, skyscraperPresheaf_map, dif_pos hx,
      ↓reduceDIte, eqToHom_trans_assoc, Category.assoc, eqToHom_trans] at h₂
    rw [← op_unop i]
    simp only [skyscraperPresheaf_map, dif_pos hx, ↓reduceDIte,
      eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
    calc
      _ = skyscraperSectionEquiv X x N U.unop (leOfHom i.unop hx) (r • s) := by
        simpa only [skyscraperAdditive, skyscraperPresheaf_map, dif_pos hx,
          ↓reduceDIte, eqToHom_trans_assoc, Category.assoc, eqToHom_trans] using h₁
      _ = X.presheaf.germ U.unop x (leOfHom i.unop hx) r •
          skyscraperSectionEquiv X x N U.unop (leOfHom i.unop hx) s :=
        skyscraperSectionEquiv_smulRing X x N U.unop (leOfHom i.unop hx) r s
      _ = _ := by
        rw [skyscraperSectionEquiv_smulRing X x N V.unop hx]
        rw [← h₂]
        change _ = (X.presheaf.germ V.unop x hx)
          (X.presheaf.map i.unop.op (r : X.presheaf.obj (op U.unop))) • _
        rw [← X.presheaf.germ_res_apply i.unop x hx r]
  · letI := skyscraperSection_subsingleton X x N V.unop hx
    exact Subsingleton.elim _ _

/-- The skyscraper module sheaf with the stalk-module `N` at the arbitrary point `x`.
Its action on a containing open is induced by the actual structure-sheaf germ. -/
def moduleSkyscraper (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules where
  val := PresheafOfModules.ofPresheaf (skyscraperAdditive X x N)
    (by
      intro U V i r s
      exact skyscraper_map_smul X x N i r s)
  isSheaf := skyscraperPresheaf_isSheaf x (AddCommGrpCat.of N)

/-- Forgetting the module structure gives exactly Mathlib's additive skyscraper. -/
theorem moduleSkyscraper_presheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (moduleSkyscraper X x N).presheaf =
      skyscraperPresheaf (X := (X : TopCat.{u})) x (AddCommGrpCat.of N) := by
  exact PresheafOfModules.ofPresheaf_presheaf _ _

private theorem moduleSkyscraper_val_presheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (moduleSkyscraper X x N).val.presheaf =
      skyscraperPresheaf (X := (X : TopCat.{u})) x (AddCommGrpCat.of N) := by
  simpa only [Scheme.Modules.presheaf] using moduleSkyscraper_presheaf X x N

/-- Canonical evaluation identifies sections on an open containing `x` with `N`. -/
def moduleSkyscraperSectionEquiv (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U) :
  (moduleSkyscraper X x N).presheaf.obj (op U) ≃+ N :=
  by
    have hU : (moduleSkyscraper X x N).val.presheaf.obj (op U) =
        (skyscraperAdditive X x N).obj (op U) :=
      congrArg (fun F => F.obj (op U)) (moduleSkyscraper_val_presheaf X x N)
    exact (eqToIso hU).addCommGroupIsoToAddEquiv.trans
      (skyscraperSectionEquiv X x N U hx)

/-- Evaluation is the canonical equality morphism used by the additive stalk adjunction. -/
theorem moduleSkyscraperSectionEquiv_apply (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U)
    (s : (moduleSkyscraper X x N).presheaf.obj (op U)) :
    moduleSkyscraperSectionEquiv X x N U hx s =
      (eqToHom (if_pos hx) :
        (skyscraperPresheaf x (AddCommGrpCat.of N)).obj (op U) ⟶ AddCommGrpCat.of N) s := by
  let hU := congrArg (fun F => F.obj (op U)) (moduleSkyscraper_val_presheaf X x N)
  change (skyscraperSectionEquiv X x N U hx)
      ((eqToIso hU).hom s) = _
  rfl

/-- The section action evaluates to the stalk action along the structure-sheaf germ. -/
theorem moduleSkyscraperSectionEquiv_smul (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U)
    (r : X.presheaf.obj (op U))
    (s : (moduleSkyscraper X x N).presheaf.obj (op U)) :
    moduleSkyscraperSectionEquiv X x N U hx (r • s) =
      X.presheaf.germ U x hx r • moduleSkyscraperSectionEquiv X x N U hx s := by
  let hU := congrArg (fun F => F.obj (op U)) (moduleSkyscraper_val_presheaf X x N)
  let s' := (eqToIso hU).hom s
  change (skyscraperSectionEquiv X x N U hx)
      ((eqToIso hU).hom (r • s)) = _
  convert skyscraperSectionEquiv_smul X x N U hx r s' using 1 <;> rfl

/-- Evaluation commutes with restriction between neighborhoods of the point. -/
theorem moduleSkyscraperSectionEquiv_restrict (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U V : X.Opens)
    (i : V ⟶ U) (hx : x ∈ V)
    (s : (moduleSkyscraper X x N).presheaf.obj (op U)) :
    moduleSkyscraperSectionEquiv X x N V hx
      ((moduleSkyscraper X x N).presheaf.map i.op s) =
      moduleSkyscraperSectionEquiv X x N U (i.le hx) s := by
  let hU := congrArg (fun F => F.obj (op U)) (moduleSkyscraper_val_presheaf X x N)
  let hV := congrArg (fun F => F.obj (op V)) (moduleSkyscraper_val_presheaf X x N)
  let s' := (eqToIso hU).hom s
  change (skyscraperSectionEquiv X x N V hx)
      ((eqToIso hV).hom ((moduleSkyscraper X x N).val.presheaf.map i.op s)) = _
  convert skyscraperSectionEquiv_restrict X x N U V i hx s' using 1 <;> rfl

/-- On an open not containing the point, the actual terminal section group is subsingleton. -/
theorem moduleSkyscraperSection_subsingleton (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∉ U) :
    Subsingleton ((moduleSkyscraper X x N).presheaf.obj (op U)) := by
  change Subsingleton ((moduleSkyscraper X x N).val.presheaf.obj (op U))
  rw [moduleSkyscraper_val_presheaf X x N]
  exact skyscraperSection_subsingleton X x N U hx

/- ### 2. The adjunction between stalks and skyscrapers -/

private theorem toSkyscraperPresheaf_eval
    (X : Scheme.{u}) (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (N : AddCommGrpCat.{u}) (l : F.stalk x ⟶ N)
    (U : X.Opens) (hx : x ∈ U) (s : F.obj (op U)) :
    (eqToHom (if_pos hx) : (skyscraperPresheaf x N).obj (op U) ⟶ N)
        ((toSkyscraperPresheaf x l).app (op U) s) = l (F.germ U x hx s) := by
  have h : (toSkyscraperPresheaf x l).app (op U) ≫ eqToHom (if_pos hx) =
      F.germ U x hx ≫ l := by
    simp only [toSkyscraperPresheaf_app, hx, ↓reduceDIte, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact CategoryTheory.congr_fun h s

private theorem fromStalk_germ_eval
    (X : Scheme.{u}) (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (N : AddCommGrpCat.{u}) (φ : F ⟶ skyscraperPresheaf x N)
    (U : X.Opens) (hx : x ∈ U) (s : F.obj (op U)) :
    fromStalk x φ (F.germ U x hx s) =
      (eqToHom (if_pos hx) : (skyscraperPresheaf x N).obj (op U) ⟶ N)
        (φ.app (op U) s) :=
  CategoryTheory.congr_fun (germ_fromStalk x φ U hx) s

private def moduleSkyscraperHomFromStalk
    (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (l : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N) :
    M ⟶ moduleSkyscraper X x N := by
  let p : M.presheaf ⟶ (moduleSkyscraper X x N).presheaf :=
    toSkyscraperPresheaf x (AddCommGrpCat.ofHom l.toAddMonoidHom)
  refine ⟨PresheafOfModules.homMk p ?_⟩
  intro U r m
  by_cases hx : x ∈ U.unop
  · have heval (s : Γ(M, U.unop)) :
        moduleSkyscraperSectionEquiv X x N U.unop hx (p.app U s) =
          l (M.presheaf.germ U.unop x hx s) :=
      toSkyscraperPresheaf_eval X x M.presheaf (AddCommGrpCat.of N)
        (AddCommGrpCat.ofHom l.toAddMonoidHom) U.unop hx s
    apply (moduleSkyscraperSectionEquiv X x N U.unop hx).injective
    let r' : X.presheaf.obj (op U.unop) := r
    have h1 := heval (r' • (show Γ(M, U.unop) from m))
    have h2 := heval (show Γ(M, U.unop) from m)
    calc
      moduleSkyscraperSectionEquiv X x N U.unop hx
          (p.app U (r • m)) =
        l (M.presheaf.germ U.unop x hx (r' • m)) := by
          convert h1 using 1 <;> rfl
      _ = X.presheaf.germ U.unop x hx r' •
          l (M.presheaf.germ U.unop x hx m) := by
        erw [PresheafOfModules.germ_smul (R := X.presheaf) M.val]
        exact l.map_smul _ _
      _ = X.presheaf.germ U.unop x hx r' •
          moduleSkyscraperSectionEquiv X x N U.unop hx (p.app U m) := by
        rw [h2]
      _ = _ := by
        convert (moduleSkyscraperSectionEquiv_smul X x N U.unop hx r'
          (p.app U (show Γ(M, U.unop) from m))).symm using 1 <;> rfl
  · exact (moduleSkyscraperSection_subsingleton X x N U.unop hx).elim _ _

private theorem moduleSkyscraperHomFromStalk_apply
    (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (l : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N)
    (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    moduleSkyscraperSectionEquiv X x N U hx
        ((moduleSkyscraperHomFromStalk X x M N l).app U m) =
      l (M.presheaf.germ U x hx m) :=
  toSkyscraperPresheaf_eval X x M.presheaf (AddCommGrpCat.of N)
    (AddCommGrpCat.ofHom l.toAddMonoidHom) U hx m

private def moduleSkyscraperHomToStalk
    (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (φ : M ⟶ moduleSkyscraper X x N) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N := by
  let q : M.presheaf.stalk x ⟶ AddCommGrpCat.of N :=
    fromStalk x (show M.presheaf ⟶ skyscraperPresheaf x (AddCommGrpCat.of N) from φ.mapPresheaf)
  refine { toFun := q, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    exact map_add (ConcreteCategory.hom q) a b
  intro r m
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, b, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a]
  have heval (s : Γ(M, V)) : q (M.presheaf.germ V x hxV s) =
      moduleSkyscraperSectionEquiv X x N V hxV (φ.app V s) :=
    fromStalk_germ_eval X x M.presheaf (AddCommGrpCat.of N) φ.mapPresheaf V hxV s
  have hcalc := heval ((X.presheaf.map (homOfLE hVU).op) a • b)
  erw [PresheafOfModules.germ_smul (R := X.presheaf) M.val,
    Scheme.Modules.Hom.app_smul, moduleSkyscraperSectionEquiv_smul] at hcalc
  rw [← heval] at hcalc
  simpa only [Scheme.Modules.presheaf, RingHom.id_apply] using hcalc

private theorem moduleSkyscraperHomToStalk_germ
    (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
  (φ : M ⟶ moduleSkyscraper X x N)
    (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    moduleSkyscraperHomToStalk X x M N φ (M.presheaf.germ U x hx m) =
      moduleSkyscraperSectionEquiv X x N U hx (φ.app U m) :=
  by
    dsimp [moduleSkyscraperHomToStalk]
    rw [moduleSkyscraperSectionEquiv_apply]
    exact fromStalk_germ_eval X x M.presheaf (AddCommGrpCat.of N) φ.mapPresheaf U hx m

/-- The stalk functor is left adjoint to the actual module skyscraper at any point. -/
def moduleSkyscraperHomEquiv (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N) ≃
      (M ⟶ moduleSkyscraper X x N) where
  toFun := moduleSkyscraperHomFromStalk X x M N
  invFun := moduleSkyscraperHomToStalk X x M N
  left_inv l := by
    apply LinearMap.ext
    intro m
    dsimp [moduleSkyscraperHomToStalk, moduleSkyscraperHomFromStalk]
    exact CategoryTheory.congr_fun
      (fromStalk_to_skyscraper x (AddCommGrpCat.ofHom l.toAddMonoidHom)) m
  right_inv φ := by
    apply (Scheme.Modules.toPresheaf X).map_injective
    dsimp [moduleSkyscraperHomFromStalk, moduleSkyscraperHomToStalk]
    exact to_skyscraper_fromStalk x φ.mapPresheaf

/-- On an open containing the point, a stalk-linear map acts by first taking the germ. -/
theorem moduleSkyscraperHomEquiv_apply (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (l : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N)
    (U : X.Opens) (hx : x ∈ U) (m : M.val.obj (op U)) :
    moduleSkyscraperSectionEquiv X x N U hx
        ((moduleSkyscraperHomEquiv X x M N l).app U m) =
      l (M.presheaf.germ U x hx m) :=
  moduleSkyscraperHomFromStalk_apply X x M N l U hx m

/-- The inverse Hom correspondence evaluates every germ using the original sheaf morphism. -/
theorem moduleSkyscraperHomEquiv_symm_germ (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (φ : M ⟶ moduleSkyscraper X x N)
    (U : X.Opens) (hx : x ∈ U) (m : M.val.obj (op U)) :
    (moduleSkyscraperHomEquiv X x M N).symm φ (M.presheaf.germ U x hx m) =
      moduleSkyscraperSectionEquiv X x N U hx (φ.app U m) :=
  moduleSkyscraperHomToStalk_germ X x M N φ U hx m

/- ### 3. Pushforward of skyscrapers and semilinear stalk maps -/

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (x : X)
  (N : ModuleCat.{u} (X.presheaf.stalk x))

set_option backward.isDefEq.respectTransparency false

private theorem pushforwardSkyscraper_eval_smul (U : Y.Opens) (hx : f x ∈ U)
    (r : Y.presheaf.obj (op U))
    (s : ((Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N)).presheaf.obj
      (op U)) :
    moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx (r • s) =
      f.stalkMap x (Y.presheaf.germ U (f x) hx r) •
        moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx s := by
  change moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx
    (f.app U r • (show (moduleSkyscraper X x N).presheaf.obj (op (f ⁻¹ᵁ U)) from s)) = _
  rw [moduleSkyscraperSectionEquiv_smul, Scheme.Hom.germ_stalkMap_apply]

private def pushforwardSkyscraperFromStalkPresheaf
    (q : M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] N) :
    M.presheaf ⟶
      ((Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N)).presheaf :=
  toSkyscraperPresheaf (f x) (AddCommGrpCat.ofHom q.toAddMonoidHom)

private theorem pushforwardSkyscraperFromStalkPresheaf_eval
    (q : M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] N)
    (U : Y.Opens) (hx : f x ∈ U) (m : M.val.obj (op U)) :
    moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx
        ((pushforwardSkyscraperFromStalkPresheaf f M x N q).app (op U) m) =
      q (M.presheaf.germ U (f x) hx m) := by
  have h :
      (toSkyscraperPresheaf (f x) (AddCommGrpCat.ofHom q.toAddMonoidHom)).app (op U) ≫
          eqToHom (if_pos hx) =
        M.presheaf.germ U (f x) hx ≫ AddCommGrpCat.ofHom q.toAddMonoidHom := by
    simp only [toSkyscraperPresheaf_app, hx, ↓reduceDIte, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact CategoryTheory.congr_fun h m

private def pushforwardSkyscraperFromStalk
    (q : M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] N) :
    M ⟶ (Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N) := by
  refine ⟨PresheafOfModules.homMk (pushforwardSkyscraperFromStalkPresheaf f M x N q) ?_⟩
  intro U r m
  by_cases hx : f x ∈ U.unop
  · have hx' : x ∈ f ⁻¹ᵁ U.unop := (Scheme.Hom.mem_preimage f).2 hx
    apply (moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U.unop) hx').injective
    change _ = moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U.unop) hx'
      (f.app U.unop r •
        (show (moduleSkyscraper X x N).presheaf.obj (op (f ⁻¹ᵁ U.unop)) from
          (pushforwardSkyscraperFromStalkPresheaf f M x N q).app U m))
    calc
      moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U.unop) hx'
          ((pushforwardSkyscraperFromStalkPresheaf f M x N q).app U (r • m)) =
          q (M.presheaf.germ U.unop (f x) hx (r • m)) := by
            simpa only [op_unop] using
              pushforwardSkyscraperFromStalkPresheaf_eval f M x N q U.unop hx' (r • m)
      _ = q (Y.presheaf.germ U.unop (f x) hx r •
          M.presheaf.germ U.unop (f x) hx m) := by
            simpa only [Scheme.Modules.presheaf] using congrArg q
              (PresheafOfModules.germ_smul (R := Y.presheaf) M.val
                (f x) U.unop hx r m)
      _ = f.stalkMap x (Y.presheaf.germ U.unop (f x) hx r) •
          q (M.presheaf.germ U.unop (f x) hx m) := q.map_smulₛₗ _ _
      _ = f.stalkMap x (Y.presheaf.germ U.unop (f x) hx r) •
          moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U.unop) hx'
            ((pushforwardSkyscraperFromStalkPresheaf f M x N q).app U m) := by
            rw [show q (M.presheaf.germ U.unop (f x) hx m) = _ by
              simpa only [op_unop] using
                (pushforwardSkyscraperFromStalkPresheaf_eval f M x N q U.unop hx' m).symm]
      _ = moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U.unop) hx'
          (f.app U.unop r •
            (show (moduleSkyscraper X x N).presheaf.obj (op (f ⁻¹ᵁ U.unop)) from
              (pushforwardSkyscraperFromStalkPresheaf f M x N q).app U m)) := by
            rw [moduleSkyscraperSectionEquiv_smul,
              Scheme.Hom.germ_stalkMap_apply]
  · have hx' : x ∉ f ⁻¹ᵁ U.unop := by
      intro hx'
      exact hx ((Scheme.Hom.mem_preimage f).1 hx')
    letI := moduleSkyscraperSection_subsingleton X x N (f ⁻¹ᵁ U.unop) hx'
    haveI : Subsingleton
        (((Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N)).val.presheaf.obj U) := by
      change Subsingleton ((moduleSkyscraper X x N).presheaf.obj
        (op (f ⁻¹ᵁ U.unop)))
      exact moduleSkyscraperSection_subsingleton X x N (f ⁻¹ᵁ U.unop) hx'
    exact Subsingleton.elim _ _

private theorem pushforwardSkyscraperFromStalk_eval
    (q : M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] N)
    (U : Y.Opens) (hx : f x ∈ U) (m : M.val.obj (op U)) :
    moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx
        ((pushforwardSkyscraperFromStalk f M x N q).app U m) =
      q (M.presheaf.germ U (f x) hx m) :=
  pushforwardSkyscraperFromStalkPresheaf_eval f M x N q U hx m

private def pushforwardSkyscraperToStalkAddHom
    (a : M ⟶ (Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N)) :
    M.presheaf.stalk (f x) →+ N :=
  (fromStalk (f x) (show M.presheaf ⟶ skyscraperPresheaf (f x) (AddCommGrpCat.of N)
    from a.mapPresheaf)).hom

private theorem pushforwardSkyscraperToStalkAddHom_germ
    (a : M ⟶ (Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N))
    (U : Y.Opens) (hx : f x ∈ U) (m : M.val.obj (op U)) :
    pushforwardSkyscraperToStalkAddHom f M x N a (M.presheaf.germ U (f x) hx m) =
      moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx (a.app U m) :=
  CategoryTheory.congr_fun (germ_fromStalk (f x) a.mapPresheaf U hx) m

private theorem pushforwardSkyscraperToStalkAddHom_smul
    (a : M ⟶ (Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N))
    (r : Y.presheaf.stalk (f x)) (m : M.presheaf.stalk (f x)) :
    pushforwardSkyscraperToStalkAddHom f M x N a (r • m) =
      f.stalkMap x r • pushforwardSkyscraperToStalkAddHom f M x N a m := by
  obtain ⟨U, hxU, b, rfl⟩ := Y.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, n, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  rw [← Y.presheaf.germ_res_apply (homOfLE hVU) (f x) hxV b]
  erw [← PresheafOfModules.germ_smul (R := Y.presheaf) M.val,
    pushforwardSkyscraperToStalkAddHom_germ, Scheme.Modules.Hom.app_smul,
    pushforwardSkyscraper_eval_smul, pushforwardSkyscraperToStalkAddHom_germ]

private def pushforwardSkyscraperToStalk
    (a : M ⟶ (Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N)) :
    M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] N where
  toAddHom := pushforwardSkyscraperToStalkAddHom f M x N a
  map_smul' := pushforwardSkyscraperToStalkAddHom_smul f M x N a

/-- Maps to the actual pushforward skyscraper are semilinear maps from the source stalk. -/
def modulePushforwardSkyscraperHomEquiv :
    (M ⟶ (Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N)) ≃
      (M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] N) where
  toFun := pushforwardSkyscraperToStalk f M x N
  invFun := pushforwardSkyscraperFromStalk f M x N
  left_inv a := by
    apply Scheme.Modules.hom_ext
    intro U
    ext m
    by_cases hx : f x ∈ U
    · apply (moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx).injective
      rw [pushforwardSkyscraperFromStalk_eval]
      exact pushforwardSkyscraperToStalkAddHom_germ f M x N a U hx m
    · have hx' : x ∉ f ⁻¹ᵁ U := by
        intro hx'
        exact hx ((Scheme.Hom.mem_preimage f).1 hx')
      haveI : Subsingleton
          (((Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N)).presheaf.obj (op U)) := by
        rw [Scheme.Modules.pushforward_obj_obj]
        exact moduleSkyscraperSection_subsingleton X x N (f ⁻¹ᵁ U) hx'
      exact Subsingleton.elim _ _
  right_inv q := by
    ext m
    obtain ⟨U, hx, n, rfl⟩ := M.presheaf.exists_germ_eq m
    change pushforwardSkyscraperToStalkAddHom f M x N
      (pushforwardSkyscraperFromStalk f M x N q) (M.presheaf.germ U (f x) hx n) = _
    rw [pushforwardSkyscraperToStalkAddHom_germ, pushforwardSkyscraperFromStalk_eval]

/-- The equivalence evaluates a germ by applying the original map on its section. -/
theorem modulePushforwardSkyscraperHomEquiv_germ
    (a : M ⟶ (Scheme.Modules.pushforward f).obj (moduleSkyscraper X x N))
    (U : Y.Opens) (hx : f x ∈ U) (m : M.val.obj (op U)) :
    modulePushforwardSkyscraperHomEquiv f M x N a (M.presheaf.germ U (f x) hx m) =
      moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx (a.app U m) :=
  pushforwardSkyscraperToStalkAddHom_germ f M x N a U hx m

/-- The inverse on an open containing `f x` applies the semilinear map to its germ. -/
theorem modulePushforwardSkyscraperHomEquiv_symm_apply
    (q : M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] N)
    (U : Y.Opens) (hx : f x ∈ U) (m : M.val.obj (op U)) :
    moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hx
        (((modulePushforwardSkyscraperHomEquiv f M x N).symm q).app U m) =
      q (M.presheaf.germ U (f x) hx m) :=
  pushforwardSkyscraperFromStalk_eval f M x N q U hx m

/-- Recovering a module-sheaf morphism from its semilinear stalk map is a left inverse. -/
theorem modulePushforwardSkyscraperHomEquiv_leftInverse :
    Function.LeftInverse (modulePushforwardSkyscraperHomEquiv f M x N).symm
      (modulePushforwardSkyscraperHomEquiv f M x N) :=
  (modulePushforwardSkyscraperHomEquiv f M x N).left_inv

/-- Taking the stalk map of the constructed module-sheaf morphism is a right inverse. -/
theorem modulePushforwardSkyscraperHomEquiv_rightInverse :
    Function.RightInverse (modulePushforwardSkyscraperHomEquiv f M x N).symm
      (modulePushforwardSkyscraperHomEquiv f M x N) :=
  (modulePushforwardSkyscraperHomEquiv f M x N).right_inv

end Pushforward

/- ### 4. The inverse of the tensor-to-pullback-stalk map -/

section Inverse

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (x : X)

attribute [local instance] modulePullbackStalkAlgebra

set_option backward.isDefEq.respectTransparency false

/-- Linear maps out of the original pullback stalk correspond to semilinear maps
out of the original module stalk, using the actual pullback adjunction. -/
def modulePullbackStalkHomEquiv (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (modulePullbackStalk f M x →ₗ[X.presheaf.stalk x] N) ≃
      (M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] N) :=
  (moduleSkyscraperHomEquiv X x ((Scheme.Modules.pullback f).obj M) N).trans
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M
        (moduleSkyscraper X x N)).trans
      (modulePushforwardSkyscraperHomEquiv f M x N))

/-- The Hom correspondence is exactly precomposition by the original stalk unit. -/
@[simp]
theorem modulePullbackStalkHomEquiv_apply (N : ModuleCat.{u} (X.presheaf.stalk x))
    (l : modulePullbackStalk f M x →ₗ[X.presheaf.stalk x] N)
    (m : M.presheaf.stalk (f x)) :
    modulePullbackStalkHomEquiv f M x N l m =
      l (modulePullbackStalkUnit f M x m) := by
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
  change modulePushforwardSkyscraperHomEquiv f M x N
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M
      (moduleSkyscraper X x N)
      (moduleSkyscraperHomEquiv X x ((Scheme.Modules.pullback f).obj M) N l))
    (M.presheaf.germ U (f x) hxU m) = _
  rw [modulePushforwardSkyscraperHomEquiv_germ]
  change moduleSkyscraperSectionEquiv X x N (f ⁻¹ᵁ U) hxU
    ((moduleSkyscraperHomEquiv X x ((Scheme.Modules.pullback f).obj M) N l).app
      (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m)) = _
  rw [moduleSkyscraperHomEquiv_apply]
  exact congrArg l (modulePullbackStalkUnitAddHom_germ f M x U hxU m).symm

/-- The scalar-extension unit for the actual local-ring homomorphism. -/
def modulePullbackStalkTensorUnit :
    M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom] modulePullbackStalkTensor f M x := by
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    modulePullbackStalkAlgebra f x
  refine {
    toFun := fun m => (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] m
    map_add' := fun m n => TensorProduct.tmul_add _ m n
    map_smul' := ?_ }
  intro r m
  change (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] (r • m) =
    f.stalkMap x r • ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] m)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  change (r • (1 : X.presheaf.stalk x)) ⊗ₜ[Y.presheaf.stalk (f x)] m =
    ((f.stalkMap x).hom r * 1) ⊗ₜ[Y.presheaf.stalk (f x)] m
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]

/-- The scalar-extension unit sends a stalk element to its tensor with one. -/
@[simp]
theorem modulePullbackStalkTensorUnit_apply (m : M.presheaf.stalk (f x)) :
    modulePullbackStalkTensorUnit f M x m =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] m := rfl

/-- The existing tensor map takes the tensor unit to the original pullback unit. -/
@[simp]
theorem modulePullbackStalkTensorMap_unit (m : M.presheaf.stalk (f x)) :
    modulePullbackStalkTensorMap f M x (modulePullbackStalkTensorUnit f M x m) =
      modulePullbackStalkUnit f M x m := by
  rw [modulePullbackStalkTensorUnit_apply, modulePullbackStalkTensorMap_tmul, one_smul]

/-- The inverse is the unique linear map corresponding to the actual tensor unit. -/
def modulePullbackStalkTensorInverse :
    modulePullbackStalk f M x →ₗ[X.presheaf.stalk x] modulePullbackStalkTensor f M x :=
  (modulePullbackStalkHomEquiv f M x
    (ModuleCat.of (X.presheaf.stalk x) (modulePullbackStalkTensor f M x))).symm
      (modulePullbackStalkTensorUnit f M x)

/-- The inverse sends the original pullback unit to the tensor with one. -/
@[simp]
theorem modulePullbackStalkTensorInverse_unit (m : M.presheaf.stalk (f x)) :
    modulePullbackStalkTensorInverse f M x (modulePullbackStalkUnit f M x m) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] m := by
  have h := congrArg
    (fun q : M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom]
      modulePullbackStalkTensor f M x ↦ q m)
    ((modulePullbackStalkHomEquiv f M x
      (ModuleCat.of (X.presheaf.stalk x) (modulePullbackStalkTensor f M x))).apply_symm_apply
        (modulePullbackStalkTensorUnit f M x))
  change modulePullbackStalkHomEquiv f M x
    (ModuleCat.of (X.presheaf.stalk x) (modulePullbackStalkTensor f M x))
    (modulePullbackStalkTensorInverse f M x) m = _ at h
  rw [modulePullbackStalkHomEquiv_apply] at h
  exact h

/-- Tensor generation and the unit formula prove the left-inverse identity. -/
theorem modulePullbackStalkTensorInverse_leftInverse :
    Function.LeftInverse (modulePullbackStalkTensorInverse f M x)
      (modulePullbackStalkTensorMap f M x) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s m =>
    rw [modulePullbackStalkTensorMap_tmul, _root_.map_smul, modulePullbackStalkTensorInverse_unit]
    exact (TensorProduct.tmul_eq_smul_one_tmul s m).symm
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- The Hom correspondence detects equality of linear maps, giving the right inverse. -/
theorem modulePullbackStalkTensorInverse_rightInverse :
    Function.RightInverse (modulePullbackStalkTensorInverse f M x)
      (modulePullbackStalkTensorMap f M x) := by
  have h : (modulePullbackStalkTensorMap f M x).comp
      (modulePullbackStalkTensorInverse f M x) = LinearMap.id := by
    apply (modulePullbackStalkHomEquiv f M x
      (ModuleCat.of (X.presheaf.stalk x) (modulePullbackStalk f M x))).injective
    apply LinearMap.ext
    intro m
    rw [modulePullbackStalkHomEquiv_apply, modulePullbackStalkHomEquiv_apply,
      LinearMap.comp_apply, modulePullbackStalkTensorInverse_unit,
      modulePullbackStalkTensorMap_tmul, one_smul, LinearMap.id_apply]
  intro z
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun h z

/-- The existing canonical tensor-to-pullback-stalk map is bijective for arbitrary modules. -/
theorem modulePullbackStalkTensorMap_bijective :
    Function.Bijective (modulePullbackStalkTensorMap f M x) :=
  ⟨(modulePullbackStalkTensorInverse_leftInverse f M x).injective,
    (modulePullbackStalkTensorInverse_rightInverse f M x).surjective⟩

/-- The linear equivalence whose forward map is the original tensor-to-stalk map. -/
def modulePullbackStalkTensorEquiv :
    modulePullbackStalkTensor f M x ≃ₗ[X.presheaf.stalk x] modulePullbackStalk f M x where
  toLinearMap := modulePullbackStalkTensorMap f M x
  invFun := modulePullbackStalkTensorInverse f M x
  left_inv := modulePullbackStalkTensorInverse_leftInverse f M x
  right_inv := modulePullbackStalkTensorInverse_rightInverse f M x

/-- The forward linear map is the canonical map built from the original adjunction unit. -/
@[simp]
theorem modulePullbackStalkTensorEquiv_toLinearMap :
    (modulePullbackStalkTensorEquiv f M x).toLinearMap =
      modulePullbackStalkTensorMap f M x := rfl

/-- The inverse of the equivalence is the map supplied by the stalk Hom correspondence. -/
@[simp]
theorem modulePullbackStalkTensorEquiv_symm_apply (z : modulePullbackStalk f M x) :
    (modulePullbackStalkTensorEquiv f M x).symm z =
      modulePullbackStalkTensorInverse f M x z := rfl

end Inverse

end MiyaokaMori.PullbackStalkTensor

end
