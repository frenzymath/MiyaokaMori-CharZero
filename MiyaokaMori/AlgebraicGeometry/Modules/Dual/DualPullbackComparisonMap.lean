import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFrames

/-! # The natural map `f^*(F^∨) ⟶ (f^*F)^∨`

For `f : X ⟶ Y` and `F : Y.Modules` we construct the canonical morphism
`Psi f F : f^*(F^∨) ⟶ (f^*F)^∨` as the adjoint transpose (`pullbackPushforwardAdjunction`) of a
morphism `Theta f F : F^∨ ⟶ f_*((f^*F)^∨)`, which is defined on sections: a compatible family of
functionals `φ` on `F` over `V ⊆ Y` is sent to the compatible family of functionals on `f^*F` over
`f⁻¹V` given as follows. Write `T V := j_* O_{f⁻¹V}` (`j : f⁻¹V → X` the open immersion). The family
`φ` gives `hat φ : F ⟶ f_*(T V)`, `s ↦ f^♯(φ(s|_{W ∩ V}))`; its adjoint transpose is
`Phi φ : f^*F ⟶ T V`, and `theta φ` is the family `W' ↦ (s ↦ (Phi φ)_{W'}(s))` for `W' ⊆ f⁻¹V`
(sections of `T V` over `W' ⊆ f⁻¹V` are sections of `O_X` over `W'`).

The two facts used downstream are
* `Psi_app_unit`: `Psi` composed with the adjunction unit is `Theta` on sections, and
* `dualCoord_theta_dualFrame`: `theta` sends the dual frame `e^∨` of a frame `e` of `F` on `V` to
  the functionals that are `δᵢⱼ` on the pulled-back frame `unit(e)` of `f^*F` on `f⁻¹V`.

Source: Stacks 01CM/01CN (pullback of the dual of a finite locally free module).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MiyaokaMori.ModuleDualSectionEquiv

noncomputable section

namespace MiyaokaMori.DualPullback

-- `res`/`res_res`/`res_self`/`res_smul` are the `Scheme.Modules` ones.
open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section ResO

variable {W U : X.Opens} (h : W ≤ U)

lemma resO_mul (a b : Γ(X, U)) : resO h (a * b) = resO h a * resO h b := map_mul _ a b
lemma resO_add (a b : Γ(X, U)) : resO h (a + b) = resO h a + resO h b := map_add _ a b
lemma resO_one : resO h (1 : Γ(X, U)) = 1 := map_one _
lemma resO_zero : resO h (0 : Γ(X, U)) = 0 := map_zero _

end ResO

section Opens

variable (V : Y.Opens)

/-- `imPre f V W' = j ''ᵁ (j ⁻¹ᵁ W')` for `j = (f ⁻¹ᵁ V).ι`; this is `W' ⊓ f⁻¹V`. -/
abbrev imPre (W' : X.Opens) : X.Opens := (f ⁻¹ᵁ V).ι ''ᵁ ((f ⁻¹ᵁ V).ι ⁻¹ᵁ W')

lemma mem_imPre_iff (W' : X.Opens) (x : X) : x ∈ imPre f V W' ↔ x ∈ f ⁻¹ᵁ V ∧ x ∈ W' := by
  rw [imPre, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact Iff.rfl

lemma imPre_le_self (W' : X.Opens) : imPre f V W' ≤ W' :=
  fun x hx => ((mem_imPre_iff f V W' x).mp hx).2

lemma imPre_le_pre (W' : X.Opens) : imPre f V W' ≤ f ⁻¹ᵁ V :=
  fun x hx => ((mem_imPre_iff f V W' x).mp hx).1

lemma le_imPre {W' : X.Opens} (h : W' ≤ f ⁻¹ᵁ V) : W' ≤ imPre f V W' :=
  fun x hx => (mem_imPre_iff f V W' x).mpr ⟨h hx, hx⟩

lemma imPre_mono {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) : imPre f V W₁ ≤ imPre f V W₂ :=
  fun x hx => (mem_imPre_iff f V W₂ x).mpr
    ⟨((mem_imPre_iff f V W₁ x).mp hx).1, h ((mem_imPre_iff f V W₁ x).mp hx).2⟩

lemma imPre_le_preimage_inf (W : Y.Opens) : imPre f V (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) := fun x hx =>
  ⟨((mem_imPre_iff f V _ x).mp hx).2, ((mem_imPre_iff f V _ x).mp hx).1⟩

lemma imPre_mono_left {V' : Y.Opens} (h : V' ≤ V) (W' : X.Opens) : imPre f V' W' ≤ imPre f V W' :=
  fun x hx => (mem_imPre_iff f V W' x).mpr
    ⟨h ((mem_imPre_iff f V' W' x).mp hx).1, ((mem_imPre_iff f V' W' x).mp hx).2⟩

/-- `T f V = j_* O_{f⁻¹V}` for `j = (f ⁻¹ᵁ V).ι`. Its sections over `W'` are
`Γ(X, imPre f V W')` (`toX`/`ofX`), and `r • t = r|_{imPre} * t` (`T_smul`). -/
def T : X.Modules :=
  (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
    (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)

/-- A section of `T f V` over `W'` as a section of `O_X` over `imPre f V W'` (definitionally). -/
abbrev toX {W' : X.Opens} (t : Γ(T f V, W')) : Γ(X, imPre f V W') := t

/-- A section of `O_X` over `imPre f V W'` as a section of `T f V` over `W'` (definitionally). -/
abbrev ofX {W' : X.Opens} (t : Γ(X, imPre f V W')) : Γ(T f V, W') := t

lemma T_smul (W' : X.Opens) (r : Γ(X, W')) (t : Γ(T f V, W')) :
    r • t = ofX f V (resO (imPre_le_self f V W') r * toX f V t) := rfl

lemma T_res {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) (t : Γ(T f V, W₂)) :
    res (T f V) h t = ofX f V (resO (imPre_mono f V h) (toX f V t)) := rfl

lemma T_add (W' : X.Opens) (t t' : Γ(T f V, W')) : toX f V (t + t') = toX f V t + toX f V t' := rfl

/-- Multiplication by `a ∈ Γ(X, f⁻¹V)` on sections of `T f V` over `W'`. -/
def mulTLin (a : Γ(X, f ⁻¹ᵁ V)) (W' : X.Opens) : Γ(T f V, W') →ₗ[Γ(X, W')] Γ(T f V, W') where
  toFun t := ofX f V (resO (imPre_le_pre f V W') a * toX f V t)
  map_add' t t' := by
    change (resO (imPre_le_pre f V W') a * (toX f V t + toX f V t') : Γ(X, imPre f V W')) =
      resO (imPre_le_pre f V W') a * toX f V t + resO (imPre_le_pre f V W') a * toX f V t'
    exact mul_add _ _ _
  map_smul' r t := by
    change (resO (imPre_le_pre f V W') a * (resO (imPre_le_self f V W') r * toX f V t) :
        Γ(X, imPre f V W')) =
      (resO (imPre_le_self f V W') r * (resO (imPre_le_pre f V W') a * toX f V t) :
        Γ(X, imPre f V W'))
    ring

lemma mulTLin_apply (a : Γ(X, f ⁻¹ᵁ V)) (W' : X.Opens) (t : Γ(T f V, W')) :
    mulTLin f V a W' t = ofX f V (resO (imPre_le_pre f V W') a * toX f V t) := rfl

/-- Multiplication by `a ∈ Γ(X, f⁻¹V)` on `T f V`. -/
def mulT (a : Γ(X, f ⁻¹ᵁ V)) : T f V ⟶ T f V :=
  homOfLin (mulTLin f V a) (by
    intro W₁ W₂ h t
    change (resO (imPre_le_pre f V W₁) a * resO (imPre_mono f V h) (toX f V t) :
        Γ(X, imPre f V W₁)) =
      resO (imPre_mono f V h) (resO (imPre_le_pre f V W₂) a * toX f V t)
    rw [resO_mul, resO_resO])

lemma mulT_app (a : Γ(X, f ⁻¹ᵁ V)) (W' : X.Opens) (t : Γ(T f V, W')) :
    (mulT f V a).app W' t = ofX f V (resO (imPre_le_pre f V W') a * toX f V t) := rfl

/-- Restriction `T f V ⟶ T f V'` on sections over `W'`, for `V' ≤ V`. -/
def rhoTLin {V' : Y.Opens} (h : V' ≤ V) (W' : X.Opens) : Γ(T f V, W') →ₗ[Γ(X, W')] Γ(T f V', W') where
  toFun t := ofX f V' (resO (imPre_mono_left f V h W') (toX f V t))
  map_add' t t' := map_add _ _ _
  map_smul' r t := by
    change (resO (imPre_mono_left f V h W') (resO (imPre_le_self f V W') r * toX f V t) :
        Γ(X, imPre f V' W')) =
      resO (imPre_le_self f V' W') r * resO (imPre_mono_left f V h W') (toX f V t)
    rw [resO_mul, resO_resO]

lemma rhoTLin_apply {V' : Y.Opens} (h : V' ≤ V) (W' : X.Opens) (t : Γ(T f V, W')) :
    rhoTLin f V h W' t = ofX f V' (resO (imPre_mono_left f V h W') (toX f V t)) := rfl

/-- Restriction `T f V ⟶ T f V'` for `V' ≤ V`. -/
def rhoT {V' : Y.Opens} (h : V' ≤ V) : T f V ⟶ T f V' :=
  homOfLin (rhoTLin f V h) (by
    intro W₁ W₂ h' t
    change (resO (imPre_mono_left f V h W₁) (resO (imPre_mono f V h') (toX f V t)) :
        Γ(X, imPre f V' W₁)) =
      resO (imPre_mono f V' h') (resO (imPre_mono_left f V h W₂) (toX f V t))
    rw [resO_resO, resO_resO])

lemma rhoT_app {V' : Y.Opens} (h : V' ≤ V) (W' : X.Opens) (t : Γ(T f V, W')) :
    (rhoT f V h).app W' t = ofX f V' (resO (imPre_mono_left f V h W') (toX f V t)) := rfl

end Opens

section Hat

variable (F : Y.Modules) (V : Y.Opens)

/-- A section of `f_*(T f V)` over `W` as a section of `O_X` over `imPre f V (f⁻¹W)`. -/
abbrev toPX {W : Y.Opens} (t : Γ((Scheme.Modules.pushforward f).obj (T f V), W)) :
    Γ(X, imPre f V (f ⁻¹ᵁ W)) := t

/-- A section of `O_X` over `imPre f V (f⁻¹W)` as a section of `f_*(T f V)` over `W`. -/
abbrev ofPX {W : Y.Opens} (t : Γ(X, imPre f V (f ⁻¹ᵁ W))) :
    Γ((Scheme.Modules.pushforward f).obj (T f V), W) := t

/-- Scalars act on `Γ(f_*(T f V), W)` through `f^♯`. -/
lemma pushforward_T_smul (W : Y.Opens) (r : Γ(Y, W))
    (t : Γ((Scheme.Modules.pushforward f).obj (T f V), W)) :
    r • t = ofPX f V (resO (imPre_le_self f V (f ⁻¹ᵁ W)) (f.app W r) * toPX f V t) := rfl

lemma pushforward_T_res {W' W : Y.Opens} (h : W' ≤ W)
    (t : Γ((Scheme.Modules.pushforward f).obj (T f V), W)) :
    res ((Scheme.Modules.pushforward f).obj (T f V)) h t =
      ofPX f V (resO (imPre_mono f V ((Opens.map f.base).map (homOfLE h)).le) (toPX f V t)) := rfl

lemma appLE_resO {W : Y.Opens} {Z : X.Opens} (hZ : Z ≤ f ⁻¹ᵁ (W ⊓ V)) (r : Γ(Y, W)) :
    f.appLE (W ⊓ V) Z hZ (resO inf_le_left r) =
      resO (hZ.trans ((Opens.map f.base).map (homOfLE inf_le_left)).le) (f.app W r) := by
  change (Y.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op ≫ f.appLE (W ⊓ V) Z hZ) r = _
  rw [Scheme.Hom.map_appLE]
  rfl

/-- The value of `hat φ` on a section, as a section of `O_X` over `imPre f V (f⁻¹W)`:
`f^♯(φ_{W ⊓ V}(s|_{W ⊓ V}))`. -/
def hatX (φ : LocalDualSections Y F V) (W : Y.Opens) (s : Γ(F, W)) : Γ(X, imPre f V (f ⁻¹ᵁ W)) :=
  f.appLE (W ⊓ V) (imPre f V (f ⁻¹ᵁ W)) (imPre_le_preimage_inf f V W)
    (φ.1 (Over.mk (homOfLE inf_le_right)) (res F inf_le_left s))

/-- The sectionwise definition of `hat φ : F ⟶ f_*(T f V)`. -/
def hatLin (φ : LocalDualSections Y F V) (W : Y.Opens) :
    Γ(F, W) →ₗ[Γ(Y, W)] Γ((Scheme.Modules.pushforward f).obj (T f V), W) where
  toFun s := ofPX f V (hatX f F V φ W s)
  map_add' s t := by
    change hatX f F V φ W (s + t) = hatX f F V φ W s + hatX f F V φ W t
    unfold hatX
    rw [res_add, map_add, map_add]
  map_smul' r s := by
    rw [pushforward_T_smul]
    change hatX f F V φ W (r • s) = resO _ (f.app W r) * hatX f F V φ W s
    unfold hatX
    rw [res_smul, LinearMap.map_smul, smul_eq_mul, map_mul, appLE_resO]

lemma hatLin_apply (φ : LocalDualSections Y F V) (W : Y.Opens) (s : Γ(F, W)) :
    hatLin f F V φ W s = ofPX f V (hatX f F V φ W s) := rfl

lemma hatX_res (φ : LocalDualSections Y F V) {W' W : Y.Opens} (h : W' ≤ W) (s : Γ(F, W)) :
    hatX f F V φ W' (res F h s) =
      resO (imPre_mono f V ((Opens.map f.base).map (homOfLE h)).le) (hatX f F V φ W s) := by
  unfold hatX
  have h1 : res F inf_le_left (res F h s) =
      res F (leOfHom (Over.mk (homOfLE (inf_le_inf_right V h : W' ⊓ V ≤ W ⊓ V))).hom)
        (res F (inf_le_left : W ⊓ V ≤ W) s) := by
    rw [res_res, res_res]
  rw [h1]
  have h2 := φ.2 (Over.mk (homOfLE (inf_le_right : W' ⊓ V ≤ V)))
    (Over.mk (homOfLE (inf_le_right : W ⊓ V ≤ V)))
    (Over.homMk (homOfLE (inf_le_inf_right V h)) (by simp)) (res F inf_le_left s)
  change φ.1 (Over.mk (homOfLE inf_le_right)) (res F (inf_le_inf_right V h) (res F inf_le_left s)) =
    resO (inf_le_inf_right V h) (φ.1 (Over.mk (homOfLE inf_le_right)) (res F inf_le_left s)) at h2
  rw [h2]
  change (Y.presheaf.map (homOfLE (inf_le_inf_right V h)).op ≫ f.appLE (W' ⊓ V) _ _) _ =
    (f.appLE (W ⊓ V) _ _ ≫ X.presheaf.map (homOfLE _).op) _
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

lemma hatLin_res (φ : LocalDualSections Y F V) {W' W : Y.Opens} (h : W' ≤ W) (s : Γ(F, W)) :
    hatLin f F V φ W' (res F h s) =
      res ((Scheme.Modules.pushforward f).obj (T f V)) h (hatLin f F V φ W s) := by
  rw [hatLin_apply, hatLin_apply, pushforward_T_res]
  change hatX f F V φ W' (res F h s) = resO _ (hatX f F V φ W s)
  exact hatX_res f F V φ h s

/-- `hat φ : F ⟶ f_*(T f V)`. -/
def hat (φ : LocalDualSections Y F V) : F ⟶ (Scheme.Modules.pushforward f).obj (T f V) :=
  homOfLin (hatLin f F V φ) (fun h s => hatLin_res f F V φ h s)

lemma hat_app (φ : LocalDualSections Y F V) (W : Y.Opens) (s : Γ(F, W)) :
    (hat f F V φ).app W s = ofPX f V (hatX f F V φ W s) := rfl

lemma hat_add (φ ψ : LocalDualSections Y F V) : hat f F V (φ + ψ) = hat f F V φ + hat f F V ψ := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rw [Scheme.Modules.Hom.add_app]
  change hatX f F V (φ + ψ) W s = hatX f F V φ W s + hatX f F V ψ W s
  unfold hatX
  rw [add_apply', map_add]

lemma hat_smul (r : Γ(Y, V)) (φ : LocalDualSections Y F V) :
    hat f F V (r • φ) = hat f F V φ ≫ (Scheme.Modules.pushforward f).map (mulT f V (f.app V r)) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rw [Scheme.Modules.Hom.comp_app]
  change hatX f F V (r • φ) W s =
    resO (imPre_le_pre f V (f ⁻¹ᵁ W)) (f.app V r) * hatX f F V φ W s
  unfold hatX
  rw [smul_apply', map_mul]
  congr 1
  change (Y.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op ≫ f.appLE (W ⊓ V) _ _) r = _
  rw [Scheme.Hom.map_appLE]
  rfl

lemma hat_restrict {V' : Y.Opens} (h : V' ≤ V) (φ : LocalDualSections Y F V) :
    hat f F V' (localDualRestrict F (homOfLE h) φ) =
      hat f F V φ ≫ (Scheme.Modules.pushforward f).map (rhoT f V h) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rw [Scheme.Modules.Hom.comp_app]
  change hatX f F V' (localDualRestrict F (homOfLE h) φ) W s =
    resO (imPre_mono_left f V h (f ⁻¹ᵁ W)) (hatX f F V φ W s)
  unfold hatX
  rw [localDualRestrict_apply']
  have h1 : res F (inf_le_left : W ⊓ V' ≤ W) s =
      res F (inf_le_inf_left W h : W ⊓ V' ≤ W ⊓ V) (res F (inf_le_left : W ⊓ V ≤ W) s) := by
    rw [res_res]
  rw [h1]
  have h2 := φ.2 ((Over.map (homOfLE h)).obj (Over.mk (homOfLE (inf_le_right : W ⊓ V' ≤ V'))))
    (Over.mk (homOfLE (inf_le_right : W ⊓ V ≤ V)))
    (Over.homMk (homOfLE (inf_le_inf_left W h)) (by simp)) (res F inf_le_left s)
  change φ.1 ((Over.map (homOfLE h)).obj (Over.mk (homOfLE (inf_le_right : W ⊓ V' ≤ V'))))
      (res F (inf_le_inf_left W h) (res F inf_le_left s)) =
    resO (inf_le_inf_left W h) (φ.1 (Over.mk (homOfLE inf_le_right)) (res F inf_le_left s)) at h2
  rw [h2]
  change (Y.presheaf.map (homOfLE (inf_le_inf_left W h)).op ≫ f.appLE (W ⊓ V') _ _) _ =
    (f.appLE (W ⊓ V) _ _ ≫ X.presheaf.map (homOfLE _).op) _
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end Hat

section Phi

variable (F : Y.Modules) (V : Y.Opens)

/-- The adjoint transpose `Phi φ : f^*F ⟶ T f V` of `hat φ`. -/
def Phi (φ : LocalDualSections Y F V) : (Scheme.Modules.pullback f).obj F ⟶ T f V :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F (T f V)).symm (hat f F V φ)

lemma unit_comp_pushforward_map_Phi (φ : LocalDualSections Y F V) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F ≫
      (Scheme.Modules.pushforward f).map (Phi f F V φ) = hat f F V φ := by
  have := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F (T f V)).apply_symm_apply
    (hat f F V φ)
  rw [Adjunction.homEquiv_unit] at this
  exact this

/-- `Phi φ` on the image of the adjunction unit is `hat φ`. -/
lemma Phi_app_unit (φ : LocalDualSections Y F V) (W : Y.Opens) (s : Γ(F, W)) :
    (Phi f F V φ).app (f ⁻¹ᵁ W)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app W s) =
      ofX f V (hatX f F V φ W s) := by
  have h := congrArg (fun g => g.app W s) (unit_comp_pushforward_map_Phi f F V φ)
  exact h

lemma Phi_add (φ ψ : LocalDualSections Y F V) : Phi f F V (φ + ψ) = Phi f F V φ + Phi f F V ψ := by
  unfold Phi
  rw [hat_add, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    Functor.map_add, Preadditive.add_comp]

lemma Phi_smul (r : Γ(Y, V)) (φ : LocalDualSections Y F V) :
    Phi f F V (r • φ) = Phi f F V φ ≫ mulT f V (f.app V r) := by
  unfold Phi
  rw [hat_smul, Adjunction.homEquiv_naturality_right_symm]

lemma Phi_restrict {V' : Y.Opens} (h : V' ≤ V) (φ : LocalDualSections Y F V) :
    Phi f F V' (localDualRestrict F (homOfLE h) φ) = Phi f F V φ ≫ rhoT f V h := by
  unfold Phi
  rw [hat_restrict, Adjunction.homEquiv_naturality_right_symm]

end Phi

section Theta

variable (F : Y.Modules) (V : Y.Opens)

/-- `sectionEquiv⁻¹` commutes with restriction. -/
lemma sectionEquiv_symm_res' {M : Y.Modules} {W' W : Y.Opens} (h : W' ≤ W)
    (ψ : Γ(moduleSheafDual M, W)) :
    (sectionEquiv M W').symm (res (moduleSheafDual M) h ψ) =
      localDualRestrict M (homOfLE h) ((sectionEquiv M W).symm ψ) := by
  have := sectionEquiv_restrict M (homOfLE h) ((sectionEquiv M W).symm ψ)
  rw [LinearEquiv.apply_symm_apply] at this
  change (sectionEquiv M W').symm (res (moduleSheafDual M) h ψ) = _
  rw [show res (moduleSheafDual M) h ψ = _ from this, LinearEquiv.symm_apply_apply]

/-- The functional `s ↦ (Phi φ)_{W'}(s)` on `Γ(f^*F, W')` for `W' ⊆ f⁻¹V`. -/
def thetaFun (φ : LocalDualSections Y F V) (W' : Over (f ⁻¹ᵁ V)) :
    LocalFunctional X ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) W' where
  toFun s := resO (le_imPre f V (leOfHom W'.hom)) (toX f V ((Phi f F V φ).app W'.left s))
  map_add' s t := by
    rw [map_add, T_add, resO_add]
  map_smul' r s := by
    rw [Scheme.Modules.Hom.app_smul]
    change resO (le_imPre f V (leOfHom W'.hom))
        (resO (imPre_le_self f V W'.left) r * toX f V ((Phi f F V φ).app W'.left s)) =
      r * resO (le_imPre f V (leOfHom W'.hom)) (toX f V ((Phi f F V φ).app W'.left s))
    rw [resO_mul, resO_resO, resO_self]

lemma thetaFun_apply (φ : LocalDualSections Y F V) (W' : Over (f ⁻¹ᵁ V))
    (s : Γ((Scheme.Modules.pullback f).obj F, W'.left)) :
    thetaFun f F V φ W' s =
      resO (le_imPre f V (leOfHom W'.hom)) (toX f V ((Phi f F V φ).app W'.left s)) := rfl

lemma thetaFun_mem (φ : LocalDualSections Y F V) :
    thetaFun f F V φ ∈ localDualSubmodule X ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) := by
  intro W₁ W₂ i s
  rw [thetaFun_apply, thetaFun_apply]
  have h := PresheafOfModules.naturality_apply (Phi f F V φ).val i.left.op s
  change (Phi f F V φ).app W₁.left (((Scheme.Modules.pullback f).obj F).presheaf.map i.left.op s) =
    res (T f V) (leOfHom i.left) ((Phi f F V φ).app W₂.left s) at h
  rw [h, T_res]
  change resO _ (resO (imPre_mono f V (leOfHom i.left)) (toX f V ((Phi f F V φ).app W₂.left s))) =
    resO (leOfHom i.left) (resO _ (toX f V ((Phi f F V φ).app W₂.left s)))
  rw [resO_resO, resO_resO]

/-- `theta φ`: the compatible family of functionals on `f^*F` over `f⁻¹V` induced by `φ`. -/
def theta (φ : LocalDualSections Y F V) :
    LocalDualSections X ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) :=
  ⟨thetaFun f F V φ, thetaFun_mem f F V φ⟩

lemma theta_apply (φ : LocalDualSections Y F V) (W' : Over (f ⁻¹ᵁ V))
    (s : Γ((Scheme.Modules.pullback f).obj F, W'.left)) :
    (theta f F V φ).1 W' s =
      resO (le_imPre f V (leOfHom W'.hom)) (toX f V ((Phi f F V φ).app W'.left s)) := rfl

lemma theta_add (φ ψ : LocalDualSections Y F V) :
    theta f F V (φ + ψ) = theta f F V φ + theta f F V ψ := by
  apply Subtype.ext
  funext W'
  apply LinearMap.ext
  intro s
  change (theta f F V (φ + ψ)).1 W' s = (theta f F V φ).1 W' s + (theta f F V ψ).1 W' s
  rw [theta_apply, theta_apply, theta_apply, Phi_add, Scheme.Modules.Hom.add_app]
  change resO _ (toX f V ((Phi f F V φ).app W'.left s + (Phi f F V ψ).app W'.left s)) = _
  rw [T_add, resO_add]

lemma theta_smul (r : Γ(Y, V)) (φ : LocalDualSections Y F V) :
    theta f F V (r • φ) = f.app V r • theta f F V φ := by
  apply Subtype.ext
  funext W'
  apply LinearMap.ext
  intro s
  change (theta f F V (r • φ)).1 W' s = resO (leOfHom W'.hom) (f.app V r) * (theta f F V φ).1 W' s
  rw [theta_apply, theta_apply, Phi_smul, Scheme.Modules.Hom.comp_app]
  change resO (le_imPre f V (leOfHom W'.hom))
      (resO (imPre_le_pre f V W'.left) (f.app V r) * toX f V ((Phi f F V φ).app W'.left s)) =
    resO (leOfHom W'.hom) (f.app V r) *
      resO (le_imPre f V (leOfHom W'.hom)) (toX f V ((Phi f F V φ).app W'.left s))
  rw [resO_mul, resO_resO]

lemma theta_restrict {V' : Y.Opens} (h : V' ≤ V) (φ : LocalDualSections Y F V) :
    theta f F V' (localDualRestrict F (homOfLE h) φ) =
      localDualRestrict ((Scheme.Modules.pullback f).obj F)
        (homOfLE ((Opens.map f.base).map (homOfLE h)).le) (theta f F V φ) := by
  apply Subtype.ext
  funext W'
  apply LinearMap.ext
  intro s
  rw [localDualRestrict_apply']
  change (theta f F V' (localDualRestrict F (homOfLE h) φ)).1 W' s =
    (theta f F V φ).1 ((Over.map (homOfLE _)).obj W') s
  rw [theta_apply, theta_apply, Phi_restrict, Scheme.Modules.Hom.comp_app]
  change resO (le_imPre f V' (leOfHom W'.hom))
      (resO (imPre_mono_left f V h W'.left) (toX f V ((Phi f F V φ).app W'.left s))) =
    resO (le_imPre f V ((leOfHom W'.hom).trans ((Opens.map f.base).map (homOfLE h)).le))
      (toX f V ((Phi f F V φ).app W'.left s))
  rw [resO_resO]

/-- `Theta f F : F^∨ ⟶ f_*((f^*F)^∨)`, defined on sections through `sectionEquiv` and `theta`. -/
def ThetaLin : Γ(moduleSheafDual F, V) →ₗ[Γ(Y, V)]
    Γ((Scheme.Modules.pushforward f).obj (moduleSheafDual ((Scheme.Modules.pullback f).obj F)), V) where
  toFun σ := show Γ((Scheme.Modules.pushforward f).obj
      (moduleSheafDual ((Scheme.Modules.pullback f).obj F)), V) from
    sectionEquiv ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) (theta f F V ((sectionEquiv F V).symm σ))
  map_add' σ τ := by
    change sectionEquiv _ _ (theta f F V ((sectionEquiv F V).symm (σ + τ))) =
      sectionEquiv _ _ (theta f F V ((sectionEquiv F V).symm σ)) +
      sectionEquiv _ _ (theta f F V ((sectionEquiv F V).symm τ))
    rw [map_add, theta_add, map_add]
  map_smul' r σ := by
    change sectionEquiv _ _ (theta f F V ((sectionEquiv F V).symm (r • σ))) =
      f.app V r • sectionEquiv _ _ (theta f F V ((sectionEquiv F V).symm σ))
    rw [LinearEquiv.map_smul, theta_smul, LinearEquiv.map_smul]

lemma ThetaLin_apply (σ : Γ(moduleSheafDual F, V)) :
    ThetaLin f F V σ = show Γ((Scheme.Modules.pushforward f).obj
      (moduleSheafDual ((Scheme.Modules.pullback f).obj F)), V) from
    sectionEquiv ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V)
      (theta f F V ((sectionEquiv F V).symm σ)) := rfl

lemma ThetaLin_res {V' : Y.Opens} (h : V' ≤ V) (σ : Γ(moduleSheafDual F, V)) :
    ThetaLin f F V' (res (moduleSheafDual F) h σ) =
      res ((Scheme.Modules.pushforward f).obj (moduleSheafDual ((Scheme.Modules.pullback f).obj F)))
        h (ThetaLin f F V σ) := by
  rw [ThetaLin_apply, ThetaLin_apply]
  change sectionEquiv _ _ (theta f F V' ((sectionEquiv F V').symm (res (moduleSheafDual F) h σ))) =
    res (moduleSheafDual ((Scheme.Modules.pullback f).obj F))
      ((Opens.map f.base).map (homOfLE h)).le
      (sectionEquiv _ _ (theta f F V ((sectionEquiv F V).symm σ)))
  rw [sectionEquiv_symm_res', theta_restrict]
  exact (sectionEquiv_restrict ((Scheme.Modules.pullback f).obj F)
    (homOfLE ((Opens.map f.base).map (homOfLE h)).le) _).symm

end Theta

section Psi

variable (F : Y.Modules)

/-- `Theta f F : F^∨ ⟶ f_*((f^*F)^∨)`. -/
def Theta : moduleSheafDual F ⟶
    (Scheme.Modules.pushforward f).obj (moduleSheafDual ((Scheme.Modules.pullback f).obj F)) :=
  homOfLin (ThetaLin f F) (fun h σ => ThetaLin_res f F _ h σ)

lemma Theta_app (V : Y.Opens) (σ : Γ(moduleSheafDual F, V)) :
    (Theta f F).app V σ = ThetaLin f F V σ := rfl

/-- The natural map `Psi f F : f^*(F^∨) ⟶ (f^*F)^∨`, the adjoint transpose of `Theta f F`. -/
def Psi : (Scheme.Modules.pullback f).obj (moduleSheafDual F) ⟶
    moduleSheafDual ((Scheme.Modules.pullback f).obj F) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (Theta f F)

lemma unit_comp_pushforward_map_Psi :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (moduleSheafDual F) ≫
      (Scheme.Modules.pushforward f).map (Psi f F) = Theta f F := by
  have := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply (Theta f F)
  rw [Adjunction.homEquiv_unit] at this
  exact this

/-- `Psi` on the image of the adjunction unit is `Theta` on sections. -/
lemma Psi_app_unit (V : Y.Opens) (σ : Γ(moduleSheafDual F, V)) :
    (Psi f F).app (f ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (moduleSheafDual F)).app V σ) =
      (show Γ(moduleSheafDual ((Scheme.Modules.pullback f).obj F), f ⁻¹ᵁ V) from ThetaLin f F V σ) := by
  have h := congrArg (fun g => g.app V σ) (unit_comp_pushforward_map_Psi f F)
  exact h

end Psi

section Frame

variable (F : Y.Modules) {V : Y.Opens} {I : Type u} [Fintype I]

/-- The pulled-back frame vectors `unit(eᵢ) ∈ Γ(f^*F, f⁻¹V)`. -/
def unitFrame (e : I → Γ(F, V)) (i : I) : Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V (e i)

variable {e : I → Γ(F, V)} (he : IsFrameOn F e)
include he

open Classical in
/-- `theta` sends the dual frame vector `eᵢ^∨` to a functional which is `δᵢⱼ` on `unit(eⱼ)`. -/
lemma dualCoord_theta_dualFrame (i j : I) :
    dualCoord (unitFrame f F e) le_rfl (theta f F V (dualFrame he i)) j = if j = i then 1 else 0 := by
  unfold dualCoord
  rw [theta_apply, res_self]
  change resO (le_imPre f V le_rfl) (toX f V ((Phi f F V (dualFrame he i)).app (f ⁻¹ᵁ V)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V (e j)))) = _
  rw [Phi_app_unit]
  change resO (le_imPre f V le_rfl) (f.appLE (V ⊓ V) _ (imPre_le_preimage_inf f V V)
    ((dualFrame he i).1 (Over.mk (homOfLE inf_le_right)) (res F inf_le_left (e j)))) = _
  have h1 : (dualFrame he i).1 (Over.mk (homOfLE (inf_le_right : V ⊓ V ≤ V)))
      (res F inf_le_left (e j)) =
      resO (inf_le_right : V ⊓ V ≤ V) (dualCoord e le_rfl (dualFrame he i) j) := by
    unfold dualCoord
    rw [res_self]
    exact apply_res (dualFrame he i) (Over.mk (homOfLE inf_le_right)) (e j)
  rw [h1, dualCoord_dualFrame]
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj]
    change X.presheaf.map _ (f.appLE _ _ _ (Y.presheaf.map _ 1)) = 1
    rw [map_one, map_one, map_one]
  · rw [if_neg hj, if_neg hj]
    change X.presheaf.map _ (f.appLE _ _ _ (Y.presheaf.map _ 0)) = 0
    rw [map_zero, map_zero, map_zero]

end Frame

end MiyaokaMori.DualPullback

end
