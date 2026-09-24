import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaUniversalDerivation
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.InverseImagePresheafSections

/-! # Kähler differentials and open immersion squares

Statement: consider a commutative square `f' ≫ h = g ≫ f` (`f : X → S`, `f' : X' → S'`, with
`g : X' → X` and `h : S' → S` open immersions). Then there is an isomorphism of `O_{X'}`-modules
`Ω_{X/S}|_{X'} ≅ Ω_{X'/S'}` (`Omega.restrictIso`, where the restriction is
`Scheme.Modules.restrict g`, whose sections over `W ⊆ X'` are `Γ(g(W), Ω_{X/S})`), compatible with
the universal derivations: the forward map sends `d_{X/S}((g^♯)⁻¹ a)` to `d_{X'/S'}(a)`
(`restrictHom_app_d`) and the inverse sends `d_{X'/S'}(a)` to `d_{X/S}((g^♯)⁻¹ a)`
(`restrictInv_app_d`), for `a ∈ Γ(X', W)`. Moreover, the adjoint transpose
`Ω_{X/S} → g_*Ω_{X'/S'}` (`squareToPushforward`, `d a ↦ d(g^♯ a)`) is bijective on sections over
opens `g(W)` inside the image of `g` (`squareToPushforward_app_bijective`). The universal property
is also given in elementwise form: the derivation corresponding to `ψ : Ω_{X/S} → F` is `ψ ∘ d`
(`homEquivDerivation_d`), and two morphisms agreeing on all `d a` are equal (`Omega.hom_ext`).

Proof:
1. (Universal property, elementwise.) `Omega.homEquivDerivation` is the sheafification adjunction
   followed by the universal property of presheaf Kähler differentials; the adjunction `homEquiv` is
   natural in the right variable (`Adjunction.homEquiv_naturality_right`), so the derivation
   corresponding to `ψ` is the derivation corresponding to the identity (the universal derivation
   `d`) followed by `ψ`. Hence `homEquiv.symm D` takes the value `D a` on `d a`, and injectivity of
   `homEquiv` gives `hom_ext`.
2. (`Ω_{X/S} → g_*Ω_{X'/S'}`.) `U ↦ d_{X'/S'}(g⁻¹U) ∘ g^♯(U)` is a derivation from `O_X` to
   `g_*Ω_{X'/S'}`: Leibniz and compatibility with restriction come from `g^♯` being a natural ring
   homomorphism; it vanishes on the image of `f⁻¹O_S`: elements of the image have the form
   `f.appLE V U r`, and `g^♯(f.appLE V U r) = f'.appLE (h⁻¹V) (g⁻¹U) (h^♯ r)` (commutativity of the
   square + `appLE_comp_appLE`), which is killed by `d_{X'/S'}`. The universal property gives
   `Ω_{X/S} → g_*Ω_{X'/S'}`, and the adjunction `restrict g ⊣ g_*` (`restrictAdjunction`) gives
   `restrictHom`. This step does not use that the maps are open immersions (apart from the adjunction).
3. (`Ω_{X'/S'} → Ω_{X/S}|_{X'}`.) `W ↦ d_{X/S}(g(W)) ∘ (g.appIso W)⁻¹` is a derivation from `O_{X'}`
   to `Ω_{X/S}|_{X'}`; it vanishes on the image of `f'⁻¹O_{S'}`: elements of the image have the form
   `f'.appLE V' W r`, and `(g.appIso W)⁻¹(f'.appLE V' W r) = f.appLE (h(V')) (g(W)) ((h.appIso V')⁻¹ r)`
   (both sides equal `(g ≫ f).appLE` after composing with the isomorphisms `appIso`), which is
   killed by `d_{X/S}` (this uses that `h` is an open immersion). The universal property gives
   `restrictInv`.
4. (Mutual inverses.) `restrictInv ≫ restrictHom = 1`: by `hom_ext`, on `d a`:
   `d a ↦ d((g.appIso)⁻¹a) ↦ res(d(g^♯((g.appIso)⁻¹ a))) = d a` (`appIso_inv_app_presheafMap`).
   `restrictHom ≫ restrictInv = 1`: via the (injective) adjoint transpose this becomes the equality
   of two morphisms `Ω_{X/S} → g_*(Ω_{X/S}|_{X'})`, and by `hom_ext`:
   `d a ↦ d(g^♯ a) ↦ d((g.appIso)⁻¹ g^♯ a) = d(a|_{g g⁻¹U}) = (d a)|_{g g⁻¹ U} = unit(d a)`
   (`app_appIso_inv`, `d_map`).
5. (Bijectivity on sections.) The section map of `restrictHom` on `W` is the section map of
   `squareToPushforward` on `g(W)` followed by the restriction isomorphism (`eqToHom` for
   `g⁻¹g(W) = W`); the former is a component of an isomorphism, so the latter is bijective.

Reference: Stacks 01US (the idea of the proof: both sides have the same universal property).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

local notation "dΩ[" f "]" => Omega.homEquivDerivation f (Omega f) (𝟙 (Omega f))

theorem Omega.homEquivDerivation_d {X S : Scheme.{u}} (f : X ⟶ S) {F : X.Modules}
    (ψ : Omega f ⟶ F) (W : X.Opens) (a : Γ(X, W)) :
    (Omega.homEquivDerivation f F ψ).d (X := op W) a =
      ψ.app W ((Omega.homEquivDerivation f (Omega f) (𝟙 _)).d (X := op W) a) := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right
    (𝟙 (Omega f)) ψ
  erw [Category.id_comp] at h
  have h' : PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) ψ =
      PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) (𝟙 (Omega f)) ≫
        (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map ψ := h
  change ((PresheafOfModules.DifferentialsConstruction.derivation'
    (Scheme.inverseImageStructureMap f)).postcomp
      (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) ψ)).d a = _
  refine (congrArg (fun t => ((PresheafOfModules.DifferentialsConstruction.derivation'
    (Scheme.inverseImageStructureMap f)).postcomp (N := F.val) t).d (X := op W) a) h').trans ?_
  rfl


theorem Omega.homEquivDerivation_symm_d {X S : Scheme.{u}} (f : X ⟶ S) {F : X.Modules}
    (D : (F.val).Derivation' (Scheme.inverseImageStructureMap f)) (W : X.Opens) (a : Γ(X, W)) :
    ((Omega.homEquivDerivation f F).symm D).app W ((dΩ[f]).d (X := op W) a) = D.d (X := op W) a := by
  rw [← Omega.homEquivDerivation_d, Equiv.apply_symm_apply]

theorem Omega.hom_ext {X S : Scheme.{u}} (f : X ⟶ S) {F : X.Modules} (ψ₁ ψ₂ : Omega f ⟶ F)
    (h : ∀ (W : X.Opens) (a : Γ(X, W)), ψ₁.app W ((dΩ[f]).d (X := op W) a) =
      ψ₂.app W ((dΩ[f]).d (X := op W) a)) : ψ₁ = ψ₂ := by
  apply (Omega.homEquivDerivation f F).injective
  ext W a
  exact (Omega.homEquivDerivation_d f ψ₁ W.unop a).trans
    ((h W.unop a).trans (Omega.homEquivDerivation_d f ψ₂ W.unop a).symm)

theorem Omega.appLE_congr_hom {X S : Scheme.{u}} {k k' : X ⟶ S} (hk : k = k') (V : S.Opens)
    (W : X.Opens) (e₁ : W ≤ k ⁻¹ᵁ V) (e₂ : W ≤ k' ⁻¹ᵁ V) : k.appLE V W e₁ = k'.appLE V W e₂ := by
  subst hk; rfl

/-- The square `f' ≫ h = g ≫ f` gives an `f`-derivation from `O_X` to `g_*Ω_{X'/S'}`. -/
def Omega.squarePushDerivation {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X)
    (h : S' ⟶ S) (w : f' ≫ h = g ≫ f) :
    (((Scheme.Modules.pushforward g).obj (Omega f')).val).Derivation'
      (Scheme.inverseImageStructureMap f) where
  d {U} := ((dΩ[f']).d (X := op (g ⁻¹ᵁ U.unop))).comp (g.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    exact (congrArg ((dΩ[f']).d (X := op (g ⁻¹ᵁ U.unop))) (map_mul (g.app U.unop).hom a b)).trans
      ((dΩ[f']).d_mul (X := op (g ⁻¹ᵁ U.unop)) _ _)
  d_map {U V} i x := by
    have hn : (g.app V.unop).hom (X.presheaf.map i x) =
        X'.presheaf.map ((Opens.map g.base).map i.unop).op ((g.app U.unop).hom x) :=
      congrArg (fun t => t.hom x) (g.naturality i)
    exact (congrArg ((dΩ[f']).d (X := op (g ⁻¹ᵁ V.unop))) hn).trans
      ((dΩ[f']).d_map (X := op (g ⁻¹ᵁ U.unop)) ((Opens.map g.base).map i.unop).op _)
  d_app {U} a := by
    obtain ⟨V, e, r, hr⟩ := Scheme.inverseImageStructureMap_app_eq_appLE f U.unop a
    have e' : g ⁻¹ᵁ U.unop ≤ f' ⁻¹ᵁ (h ⁻¹ᵁ V) := by
      intro x hx
      have hx' : (g ≫ f) x ∈ V := e hx
      rw [← w] at hx'
      exact hx'
    have hk : (g.app U.unop).hom ((f.appLE V U.unop e).hom r) =
        (f'.appLE (h ⁻¹ᵁ V) (g ⁻¹ᵁ U.unop) e').hom ((h.app V).hom r) := by
      have h1 : f.appLE V U.unop e ≫ g.app U.unop = h.app V ≫ f'.appLE (h ⁻¹ᵁ V) (g ⁻¹ᵁ U.unop) e' := by
        rw [g.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
        exact (Omega.appLE_congr_hom w.symm _ _ _ e').trans (Scheme.Hom.comp_appLE f' h V _ e')
      exact congrArg (fun t => t.hom r) h1
    exact (congrArg ((dΩ[f']).d (X := op (g ⁻¹ᵁ U.unop)))
      ((congrArg (g.app U.unop).hom hr).trans hk)).trans (Omega.derivation_appLE f' _ _ _ e' _)


theorem Omega.square_image_le {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X)
    (h : S' ⟶ S) (w : f' ≫ h = g ≫ f) [IsOpenImmersion g] [IsOpenImmersion h]
    {W : X'.Opens} {V' : S'.Opens} (e : W ≤ f' ⁻¹ᵁ V') : g ''ᵁ W ≤ f ⁻¹ᵁ (h ''ᵁ V') := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨f' y, e hy, ?_⟩
  change (f' ≫ h) y = (g ≫ f) y
  rw [w]

theorem Omega.square_appLE_appIso_inv {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X)
    (h : S' ⟶ S) (w : f' ≫ h = g ≫ f) [IsOpenImmersion g] [IsOpenImmersion h]
    {W : X'.Opens} {V' : S'.Opens} (e : W ≤ f' ⁻¹ᵁ V') :
    f'.appLE V' W e ≫ (g.appIso W).inv =
      (h.appIso V').inv ≫ f.appLE (h ''ᵁ V') (g ''ᵁ W) (Omega.square_image_le f f' g h w e) := by
  rw [← cancel_epi (h.appIso V').hom, ← cancel_mono (g.appIso W).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  exact Omega.appLE_congr_hom w _ _ _ _

/-- Open immersion square: the `f'`-derivation from `O_{X'}` to `Ω_{X/S}|_{X'}`. -/
def Omega.squareRestrictDerivation {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X)
    (h : S' ⟶ S) (w : f' ≫ h = g ≫ f) [IsOpenImmersion g] [IsOpenImmersion h] :
    (((Omega f).restrict g).val).Derivation' (Scheme.inverseImageStructureMap f') where
  d {W} := ((dΩ[f]).d (X := op (g ''ᵁ W.unop))).comp (g.appIso W.unop).inv.hom.toAddMonoidHom
  d_mul {W} a b := by
    exact (congrArg ((dΩ[f]).d (X := op (g ''ᵁ W.unop)))
      (map_mul (g.appIso W.unop).inv.hom a b)).trans
      ((dΩ[f]).d_mul (X := op (g ''ᵁ W.unop)) _ _)
  d_map {W₁ W₂} i x := by
    have hn : (g.appIso W₂.unop).inv.hom (X'.presheaf.map i x) =
        X.presheaf.map (g.opensFunctor.op.map i) ((g.appIso W₁.unop).inv.hom x) :=
      congrArg (fun t => t.hom x) (g.appIso_inv_naturality i)
    exact (congrArg ((dΩ[f]).d (X := op (g ''ᵁ W₂.unop))) hn).trans
      ((dΩ[f]).d_map (X := op (g ''ᵁ W₁.unop)) (g.opensFunctor.op.map i) _)
  d_app {W} a := by
    obtain ⟨V', e, r, hr⟩ := Scheme.inverseImageStructureMap_app_eq_appLE f' W.unop a
    have hk : (g.appIso W.unop).inv.hom ((f'.appLE V' W.unop e).hom r) =
        (f.appLE (h ''ᵁ V') (g ''ᵁ W.unop) (Omega.square_image_le f f' g h w e)).hom
          ((h.appIso V').inv.hom r) :=
      congrArg (fun t => t.hom r) (Omega.square_appLE_appIso_inv f f' g h w e)
    exact (congrArg ((dΩ[f]).d (X := op (g ''ᵁ W.unop)))
      ((congrArg (g.appIso W.unop).inv.hom hr).trans hk)).trans
      (Omega.derivation_appLE f _ _ _ _ _)


section Square
variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X)
    (h : S' ⟶ S) (w : f' ≫ h = g ≫ f) [IsOpenImmersion g] [IsOpenImmersion h]

/-- `Ω_{X/S} → g_*Ω_{X'/S'}`. -/
def Omega.squareToPushforward : Omega f ⟶ (Scheme.Modules.pushforward g).obj (Omega f') :=
  (Omega.homEquivDerivation f _).symm (Omega.squarePushDerivation f f' g h w)

/-- `Ω_{X/S}|_{X'} → Ω_{X'/S'}`. -/
def Omega.restrictHom : (Omega f).restrict g ⟶ Omega f' :=
  ((Scheme.Modules.restrictAdjunction g).homEquiv _ _).symm (Omega.squareToPushforward f f' g h w)

/-- `Ω_{X'/S'} → Ω_{X/S}|_{X'}`. -/
def Omega.restrictInv : Omega f' ⟶ (Omega f).restrict g :=
  (Omega.homEquivDerivation f' _).symm (Omega.squareRestrictDerivation f f' g h w)

theorem Omega.restrictInv_app_d (W : X'.Opens) (a : Γ(X', W)) :
    (Omega.restrictInv f f' g h w).app W ((dΩ[f']).d (X := op W) a) =
      (dΩ[f]).d (X := op (g ''ᵁ W)) ((g.appIso W).inv.hom a) :=
  Omega.homEquivDerivation_symm_d f' _ W a

omit [IsOpenImmersion g] [IsOpenImmersion h] in
theorem Omega.squareToPushforward_app_d (U : X.Opens) (a : Γ(X, U)) :
    (Omega.squareToPushforward f f' g h w).app U ((dΩ[f]).d (X := op U) a) =
      (dΩ[f']).d (X := op (g ⁻¹ᵁ U)) ((g.app U).hom a) :=
  Omega.homEquivDerivation_symm_d f _ U a

omit [IsOpenImmersion h] in
theorem Omega.restrictHom_app_d (W : X'.Opens) (a : Γ(X', W)) :
    (Omega.restrictHom f f' g h w).app W
      ((dΩ[f]).d (X := op (g ''ᵁ W)) ((g.appIso W).inv.hom a)) = (dΩ[f']).d (X := op W) a := by
  have h1 : Omega.restrictHom f f' g h w =
      (Scheme.Modules.restrictFunctor g).map (Omega.squareToPushforward f f' g h w) ≫
        (Scheme.Modules.restrictAdjunction g).counit.app (Omega f') :=
    Adjunction.homEquiv_counit _ _ _ _
  have h2 : (Omega.restrictHom f f' g h w).app W
      ((dΩ[f]).d (X := op (g ''ᵁ W)) ((g.appIso W).inv.hom a)) =
      (Omega f').presheaf.map (eqToHom (g.preimage_image_eq W).symm).op
        ((Omega.squareToPushforward f f' g h w).app (g ''ᵁ W)
          ((dΩ[f]).d (X := op (g ''ᵁ W)) ((g.appIso W).inv.hom a))) := by
    rw [h1]; rfl
  rw [h2, Omega.squareToPushforward_app_d]
  refine ((dΩ[f']).d_map (X := op (g ⁻¹ᵁ g ''ᵁ W)) (eqToHom (g.preimage_image_eq W).symm).op _).symm.trans ?_
  refine congrArg ((dΩ[f']).d (X := op W)) ?_
  exact congrArg (fun t => t.hom a) (g.appIso_inv_app_presheafMap W)


theorem Omega.restrictInv_restrictHom :
    Omega.restrictInv f f' g h w ≫ Omega.restrictHom f f' g h w = 𝟙 _ := by
  apply Omega.hom_ext
  intro W a
  rw [Scheme.Modules.Hom.comp_app]
  exact (congrArg ((Omega.restrictHom f f' g h w).app W) (Omega.restrictInv_app_d f f' g h w W a)).trans
    (Omega.restrictHom_app_d f f' g h w W a)

theorem Omega.restrictHom_restrictInv :
    Omega.restrictHom f f' g h w ≫ Omega.restrictInv f f' g h w = 𝟙 _ := by
  apply ((Scheme.Modules.restrictAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  have h0 : ((Scheme.Modules.restrictAdjunction g).homEquiv _ _) (Omega.restrictHom f f' g h w) =
      Omega.squareToPushforward f f' g h w := Equiv.apply_symm_apply _ _
  rw [h0, Adjunction.homEquiv_unit]
  apply Omega.hom_ext
  intro U a
  rw [Scheme.Modules.Hom.comp_app]
  refine (congrArg ((Omega.restrictInv f f' g h w).app (g ⁻¹ᵁ U))
    (Omega.squareToPushforward_app_d f f' g h w U a)).trans ?_
  refine (Omega.restrictInv_app_d f f' g h w (g ⁻¹ᵁ U) _).trans ?_
  have hk : (g.appIso (g ⁻¹ᵁ U)).inv.hom ((g.app U).hom a) =
      X.presheaf.map (homOfLE (g.image_preimage_le U)).op a :=
    congrArg (fun t => t.hom a) (g.app_appIso_inv U)
  refine (congrArg ((dΩ[f]).d (X := op (g ''ᵁ g ⁻¹ᵁ U))) hk).trans ?_
  exact (dΩ[f]).d_map (X := op U) (homOfLE (g.image_preimage_le U)).op a


/-- The general form of Stacks 01US: `Ω_{X/S}|_{X'} ≅ Ω_{X'/S'}` for an open immersion square. -/
def Omega.restrictIso : (Omega f).restrict g ≅ Omega f' where
  hom := Omega.restrictHom f f' g h w
  inv := Omega.restrictInv f f' g h w
  hom_inv_id := Omega.restrictHom_restrictInv f f' g h w
  inv_hom_id := Omega.restrictInv_restrictHom f f' g h w


/-- `Ω_{X/S} → g_*Ω_{X'/S'}` is bijective on sections over opens inside the image of `g`. -/
theorem Omega.squareToPushforward_app_bijective (W : X'.Opens) :
    Function.Bijective ((Omega.squareToPushforward f f' g h w).app (g ''ᵁ W)) := by
  have h1 : Omega.restrictHom f f' g h w =
      (Scheme.Modules.restrictFunctor g).map (Omega.squareToPushforward f f' g h w) ≫
        (Scheme.Modules.restrictAdjunction g).counit.app (Omega f') :=
    Adjunction.homEquiv_counit _ _ _ _
  have h2 : (Omega.restrictHom f f' g h w).app W =
      (Omega.squareToPushforward f f' g h w).app (g ''ᵁ W) ≫
        (Omega f').presheaf.map (eqToHom (g.preimage_image_eq W).symm).op := by
    rw [h1]; rfl
  have i1 : IsIso (Omega.restrictHom f f' g h w) := (Omega.restrictIso f f' g h w).isIso_hom
  have i2 : IsIso ((Omega.restrictHom f f' g h w).app W) := inferInstance
  rw [h2] at i2
  have i4 : IsIso ((Omega f').presheaf.map (eqToHom (g.preimage_image_eq W).symm).op) :=
    Functor.map_isIso _ _
  have i3 : IsIso ((Omega.squareToPushforward f f' g h w).app (g ''ᵁ W)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ i4 i2
  exact ConcreteCategory.bijective_of_isIso _

end Square
end AlgebraicGeometry
