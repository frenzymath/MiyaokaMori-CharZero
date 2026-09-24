import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent

/-! # The tilde–Γ adjunction on an affine scheme

The tilde–Γ adjunction of Mathlib (`AlgebraicGeometry.tilde.adjunction`, on `Spec R`) transported to an
arbitrary affine scheme `X` along `X.isoSpec : X ≅ Spec Γ(X, ⊤)`. For `P : ModuleCat Γ(X, ⊤)` put
`T P := (isoSpec.hom)^* (tilde P)`; then

* `adj : (tilde ⋙ pullback isoSpec.hom) ⊣ (pushforward isoSpec.hom ⋙ moduleSpecΓFunctor)` (composite of the
  two adjunctions), with `homEquiv_apply`: a map `α : T P ⟶ N` corresponds to `p ↦ α.app ⊤ (unitEl P p)`;
* `unitEl P : P → Γ(T P, ⊤)` is bijective (`unitEl_bijective`) and `Γ(X, ⊤)`-linear (`unitEl_smul`,
  `unitEl_add`) for the *standard* module structure on `Γ(T P, ⊤)`;
* `T_hom_ext`: maps out of `T P` are determined by their values on `unitEl P p`;
* for quasi-coherent `N`, the counit `T (Γ N) ⟶ N` is an isomorphism (`isIso_counit_app`); consequences:
  `hom_ext_of_app_top` (maps out of a quasi-coherent module on an affine scheme are determined by their
  action on global sections) and `exists_hom_of_linear` (every `Γ(X, ⊤)`-linear map on global sections out of
  a quasi-coherent module is induced by a morphism of modules).

The bookkeeping lemma is `toTop_smul`: the `Γ(X, ⊤)`-module structure of Mathlib's `moduleSpecΓFunctor`
(scalars go through `ΓSpecIso⁻¹` and `isoSpec.hom.appTop`) agrees with the standard one on `Γ(N, ⊤)`, because
`X.toSpecΓ.appTop = (ΓSpecIso Γ(X, ⊤)).hom` (`Scheme.toSpecΓ_appTop`).

Source: Stacks 01I6 / 01I8 (quasi-coherent modules on an affine scheme are `M~`, and `Hom(M~, N) = Hom_R(M, Γ N)`),
Hartshorne II.5.4–5.5. Used for the sections of pullbacks on affine opens (Stacks 01I9).
No global instances are registered; the
`IsEquivalence` / `IsQuasicoherent` / `IsIso` facts are theorems to be installed locally with `haveI`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.AffineTilde

open AlgebraicGeometry

/-- Pullback along an isomorphism of schemes is an equivalence of module categories
(inverse: pullback along the inverse; the unit and counit come from `pullbackComp`/`pullbackId`). -/
def pullbackEquivOfIso {Y Z : Scheme.{u}} (e : Y ≅ Z) : Z.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId Z).symm ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id.symm ≪≫
      (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId Y)

theorem isEquivalence_pullback_hom {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (Scheme.Modules.pullback e.hom).IsEquivalence :=
  (pullbackEquivOfIso e).isEquivalence_functor

/-- `e_* ≅ (e⁻¹)^*` for an isomorphism `e` (uniqueness of right adjoints of `e^*`). -/
def pushforwardIsoPullbackInv {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    Scheme.Modules.pushforward e.hom ≅ Scheme.Modules.pullback e.inv :=
  (Scheme.Modules.pullbackPushforwardAdjunction e.hom).rightAdjointUniq
    (pullbackEquivOfIso e).toAdjunction

theorem isEquivalence_pushforward_hom {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (Scheme.Modules.pushforward e.hom).IsEquivalence :=
  have : (Scheme.Modules.pullback e.inv).IsEquivalence := isEquivalence_pullback_hom e.symm
  Functor.isEquivalence_of_iso (pushforwardIsoPullbackInv e).symm

/-- Pushforward along an isomorphism preserves quasi-coherence (it is a pullback along the inverse,
and pullbacks preserve quasi-coherence: `isQuasicoherent_pullback`, Stacks 01BG). -/
theorem isQuasicoherent_pushforward_hom {Y Z : Scheme.{u}} (e : Y ≅ Z) (N : Y.Modules)
    [N.IsQuasicoherent] : ((Scheme.Modules.pushforward e.hom).obj N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
    ((pushforwardIsoPullbackInv e).app N).symm inferInstance

variable {X : Scheme.{u}} [IsAffine X]

/-- `M~` transported to the affine scheme `X`: `T P = (isoSpec.hom)^* (tilde P)`. -/
abbrev T (P : ModuleCat.{u} Γ(X, ⊤)) : X.Modules :=
  (tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.isoSpec.hom).obj P

/-- Global sections transported: `ΓS N = Γ(Spec Γ(X,⊤), (isoSpec.hom)_* N)` as a `Γ(X, ⊤)`-module in
Mathlib's sense (`moduleSpecΓFunctor`). Its carrier is definitionally `Γ(N, ⊤)`. -/
abbrev ΓS (N : X.Modules) : ModuleCat.{u} Γ(X, ⊤) :=
  (Scheme.Modules.pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor).obj N

/-- The transported tilde–Γ adjunction on the affine scheme `X`. -/
def adj : (tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.isoSpec.hom) ⊣
    (Scheme.Modules.pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor) :=
  (tilde.adjunction).comp (Scheme.Modules.pullbackPushforwardAdjunction X.isoSpec.hom)

/-- The identity map from the transported sections module to `Γ(N, ⊤)` (kept as a `def` so that the
two module structures stay syntactically apart). -/
def toTop (N : X.Modules) (x : ΓS N) : Γ(N, ⊤) := x

/-- The transported scalar action agrees with the standard one:
`a • x` in `ΓS N` is `(isoSpec.hom.appTop (ΓSpecIso⁻¹ a)) • x = a • x` in `Γ(N, ⊤)`. -/
theorem toTop_smul (N : X.Modules) (a : Γ(X, ⊤))
    (x : Γ((Scheme.Modules.pushforward X.isoSpec.hom).obj N, ⊤)) :
    toTop N (a • x) = a • toTop N x := by
  rw [Scheme.Modules.smul_Spec_def]
  change ((X.isoSpec.hom.appTop ((Spec Γ(X, ⊤)).presheaf.map (Opens.leTop ⊤).op
    ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a)) : Γ(X, ⊤)) • (toTop N x) : Γ(N, ⊤)) = a • toTop N x
  have h1 : (Opens.leTop (⊤ : (Spec Γ(X, ⊤)).Opens)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  simp

theorem toTop_smul' (N : X.Modules) (a : Γ(X, ⊤)) (x : ΓS N) :
    toTop N (a • x) = a • toTop N x :=
  toTop_smul N a x

/-- The `Γ(X, ⊤)`-linear identification of `ΓS N` with `Γ(N, ⊤)` (identity on elements). -/
def secTop (N : X.Modules) : ΓS N ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤) where
  toFun := toTop N
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := toTop_smul' N a x
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unit of `adj` at `P`, as a map of elements `P → Γ(T P, ⊤)`. -/
def unitEl (P : ModuleCat.{u} Γ(X, ⊤)) (p : P) : Γ(T P, ⊤) := toTop (T P) ((adj.unit.app P).hom p)

/-- The adjunction formula: `adj.homEquiv α` is `p ↦ α.app ⊤ (unitEl P p)`. -/
theorem homEquiv_apply (P : ModuleCat.{u} Γ(X, ⊤)) (N : X.Modules) (α : T P ⟶ N) (p : P) :
    toTop N ((adj.homEquiv P N α).hom p) = α.app ⊤ (unitEl P p) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- Maps out of `T P` are determined by their values on the unit elements. -/
theorem T_hom_ext {P : ModuleCat.{u} Γ(X, ⊤)} {N : X.Modules} {α β : T P ⟶ N}
    (h : ∀ p, α.app ⊤ (unitEl P p) = β.app ⊤ (unitEl P p)) : α = β := by
  apply (adj.homEquiv P N).injective
  ext p
  exact (homEquiv_apply P N α p).trans ((h p).trans (homEquiv_apply P N β p).symm)

/-- The unit of `adj` is an isomorphism (both `tilde` and `(isoSpec.hom)^*` are fully faithful). -/
theorem isIso_unit_app (P : ModuleCat.{u} Γ(X, ⊤)) : IsIso (adj.unit.app P) :=
  have := isEquivalence_pullback_hom X.isoSpec
  inferInstance

theorem unitEl_bijective (P : ModuleCat.{u} Γ(X, ⊤)) : Function.Bijective (unitEl P) :=
  have := isIso_unit_app P
  ConcreteCategory.bijective_of_isIso (adj.unit.app P)

theorem unitEl_smul (P : ModuleCat.{u} Γ(X, ⊤)) (a : Γ(X, ⊤)) (p : P) :
    unitEl P (a • p) = a • unitEl P p := by
  unfold unitEl
  rw [LinearMap.map_smul]
  exact toTop_smul' (T P) a _

theorem unitEl_add (P : ModuleCat.{u} Γ(X, ⊤)) (p q : P) :
    unitEl P (p + q) = unitEl P p + unitEl P q := by
  unfold unitEl
  rw [LinearMap.map_add]
  rfl

theorem unitEl_zero (P : ModuleCat.{u} Γ(X, ⊤)) : unitEl P 0 = 0 := by
  unfold unitEl
  rw [LinearMap.map_zero]
  rfl

/-- For quasi-coherent `N` the counit `T (ΓS N) ⟶ N` is an isomorphism
(Mathlib `isIso_fromTildeΓ_of_isQuasicoherent` on `Spec Γ(X, ⊤)`, plus the pullback–pushforward
adjunction along the isomorphism `isoSpec.hom`). -/
theorem isIso_counit_app (N : X.Modules) [N.IsQuasicoherent] : IsIso (adj.counit.app N) := by
  unfold adj
  rw [Adjunction.comp_counit_app]
  have := isEquivalence_pushforward_hom X.isoSpec
  have := isQuasicoherent_pushforward_hom X.isoSpec N
  have h1 : IsIso (tilde.adjunction.counit.app ((Scheme.Modules.pushforward X.isoSpec.hom).obj N)) :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
      ((Scheme.Modules.pushforward X.isoSpec.hom).obj N) inferInstance
  have h2 : IsIso ((Scheme.Modules.pullback X.isoSpec.hom).map
      (tilde.adjunction.counit.app ((Scheme.Modules.pushforward X.isoSpec.hom).obj N))) :=
    inferInstance
  have h3 : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction X.isoSpec.hom).counit.app N) :=
    inferInstance
  exact IsIso.comp_isIso

/-- The counit acts on global sections as the inverse of the unit (triangle identity). -/
theorem counit_app_top_unitEl (N : X.Modules) (x : ΓS N) :
    (adj.counit.app N).app ⊤ (unitEl (ΓS N) x) = toTop N x := by
  have h := adj.right_triangle_components N
  have h2 := congrArg (fun f => toTop N ((ModuleCat.Hom.hom f) x)) h
  simp only [Functor.comp_map, Functor.comp_obj, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h2
  exact h2

/-- Maps out of a quasi-coherent module on an affine scheme are determined by their effect on
global sections. -/
theorem hom_ext_of_app_top {N G : X.Modules} [N.IsQuasicoherent] {β₁ β₂ : N ⟶ G}
    (h : ∀ x : Γ(N, ⊤), β₁.app ⊤ x = β₂.app ⊤ x) : β₁ = β₂ := by
  have : IsIso (adj.counit.app N) := isIso_counit_app N
  rw [← cancel_epi (adj.counit.app N)]
  apply T_hom_ext
  intro p
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change β₁.app ⊤ ((adj.counit.app N).app ⊤ (unitEl (ΓS N) p)) =
    β₂.app ⊤ ((adj.counit.app N).app ⊤ (unitEl (ΓS N) p))
  rw [counit_app_top_unitEl]
  exact h _

theorem inv_counit_app_top (N : X.Modules) [N.IsQuasicoherent] (x : ΓS N) :
    haveI := isIso_counit_app N
    (inv (adj.counit.app N)).app ⊤ (toTop N x) = unitEl (ΓS N) x := by
  have := isIso_counit_app N
  rw [← counit_app_top_unitEl N x, Scheme.Modules.inv_app]
  exact IsIso.hom_inv_id_apply ((adj.counit.app N).app ⊤) (unitEl (ΓS N) x)

/-- Every `Γ(X, ⊤)`-linear map on global sections out of a quasi-coherent module on an affine scheme
comes from a morphism of modules (version quantified over the transported module `ΓS N`). -/
theorem exists_hom_of_linear' {N G : X.Modules} [N.IsQuasicoherent]
    (l : Γ(N, ⊤) →ₗ[Γ(X, ⊤)] Γ(G, ⊤)) :
    ∃ β : N ⟶ G, ∀ x : ΓS N, β.app ⊤ (toTop N x) = l (toTop N x) := by
  have : IsIso (adj.counit.app N) := isIso_counit_app N
  let l' : ΓS N ⟶ ΓS G :=
    ModuleCat.ofHom (R := Γ(X, ⊤)) (X := ΓS N) (Y := ΓS G)
      ((secTop G).symm.toLinearMap ∘ₗ l ∘ₗ (secTop N).toLinearMap)
  refine ⟨inv (adj.counit.app N) ≫ (adj.homEquiv (ΓS N) G).symm l', fun x => ?_⟩
  rw [Scheme.Modules.Hom.comp_app]
  change ((adj.homEquiv (ΓS N) G).symm l').app ⊤ ((inv (adj.counit.app N)).app ⊤ (toTop N x)) =
    l (toTop N x)
  rw [inv_counit_app_top, ← homEquiv_apply, Equiv.apply_symm_apply]
  rfl

/-- Every `Γ(X, ⊤)`-linear map on global sections out of a quasi-coherent module on an affine scheme
comes from a morphism of modules. -/
theorem exists_hom_of_linear {N G : X.Modules} [N.IsQuasicoherent]
    (l : Γ(N, ⊤) →ₗ[Γ(X, ⊤)] Γ(G, ⊤)) :
    ∃ β : N ⟶ G, ∀ x : Γ(N, ⊤), β.app ⊤ x = l x := by
  obtain ⟨β, hβ⟩ := exists_hom_of_linear' l
  exact ⟨β, fun x => hβ x⟩

end AlgebraicGeometry.Scheme.Modules.AffineTilde

end
