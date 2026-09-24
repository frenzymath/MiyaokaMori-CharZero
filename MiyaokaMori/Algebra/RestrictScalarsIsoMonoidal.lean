import MiyaokaMori.Prelude
import MiyaokaMori.CategoryTheory.PresheafModulesPushforwardMonoidal

/-! # Restriction of scalars along a ring isomorphism is strong monoidal

* `ModuleCat` level: if `f : R →+* S` and `g : S →+* R` are mutually inverse, then the `ε` and `μ` of
  the lax monoidal structure on `ModuleCat.restrictScalars f` (Mathlib's
  `ModuleCat/Monoidal/Adjunction.lean`, obtained from `extendScalars` by doctrinal adjunction) are
  isomorphisms.
* Presheaves of modules: if `α : R ⟶ R'` (presheaves of commutative rings) is an isomorphism, then
  `PresheafOfModules.restrictScalarsC α` is strong monoidal.

Proof:
* `ε` on `𝟙_ = R` is `r ↦ f r` (`ModuleCat.restrictScalars_η`), with inverse `s ↦ g s`; `R`-linearity
  comes from `g (f r * s) = r * g s`.
* `μ` on pure tensors is `m ⊗ₜ[R] n ↦ m ⊗ₜ[S] n` (`ModuleCat.restrictScalars_μ_tmul`). Its inverse is
  built with `TensorProduct.liftAddHom`: the pairing `(m, n) ↦ m ⊗ₜ[R] n` is **`S`-balanced** because
  every `s : S` is of the form `f r` (`hfg`) and `f r • m` is **definitionally** `r • m` after
  restriction of scalars, so `TensorProduct.smul_tmul` gives the balancing; `R`-linearity is checked
  on pure tensors likewise.
* Presheaf level, open set by open set: `PresheafOfModules.toPresheaf` reflects isomorphisms, so a
  morphism all of whose components are isomorphisms is one; then `Functor.Monoidal.ofLaxMonoidal`.

Mathlib only has the `LaxMonoidal` structure on `ModuleCat.restrictScalars f`, not the statement that
it is strong monoidal when `f` is an isomorphism (`restrictScalarsEquivalenceOfRingEquiv` carries no
monoidal data).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u u' v'

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal

noncomputable section

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (g : S →+* R)

/-- The inverse of `ε` for restriction of scalars along a ring isomorphism: `s ↦ g s`. -/
def restrictScalarsEpsInv (hgf : ∀ r, g (f r) = r) :
    (ModuleCat.restrictScalars.{u} f).obj (𝟙_ (ModuleCat.{u} S)) ⟶ 𝟙_ (ModuleCat.{u} R) :=
  ModuleCat.homEquiv.symm
    { toFun := fun s => g s
      map_add' := fun s s' => g.map_add s s'
      map_smul' := fun (r : R) (s : S) => by
        show g (f r * s) = r * g s
        rw [map_mul, hgf] }

theorem restrictScalars_isIso_ε (hgf : ∀ r, g (f r) = r) (hfg : ∀ s, f (g s) = s) :
    IsIso (ε (ModuleCat.restrictScalars.{u} f)) := by
  refine ⟨restrictScalarsEpsInv f g hgf, ?_, ?_⟩
  · refine ModuleCat.hom_ext (LinearMap.ext fun (r : R) => ?_)
    show g ((ε (ModuleCat.restrictScalars f)).hom r) = r
    rw [ModuleCat.restrictScalars_η, hgf]
  · refine ModuleCat.hom_ext (LinearMap.ext fun (s : S) => ?_)
    show (ε (ModuleCat.restrictScalars f)).hom (g s) = s
    rw [ModuleCat.restrictScalars_η]
    exact hfg _

/-- The biadditive pairing `(m, n) ↦ m ⊗ₜ[R] n` with values in the `R`-tensor product of the
restricted modules. -/
def muInvAux (M N : ModuleCat.{u} S) :
    M →+ N →+ (TensorProduct R ((ModuleCat.restrictScalars.{u} f).obj M)
      ((ModuleCat.restrictScalars.{u} f).obj N)) :=
  AddMonoidHom.mk'
    (fun m => AddMonoidHom.mk' (fun n => TensorProduct.tmul R m n)
      (fun n₁ n₂ => TensorProduct.tmul_add _ _ _))
    (fun m₁ m₂ => by ext n; exact TensorProduct.add_tmul _ _ _)

/-- `muInvAux` is `S`-balanced. Key point: every `s : S` is some `f r`, and `f r • m` is
**definitionally** `r • m` after restriction of scalars, which reduces to `TensorProduct.smul_tmul`. -/
theorem muInvAux_balanced (hfg : ∀ s, f (g s) = s) (M N : ModuleCat.{u} S)
    (s : S) (m : M) (n : N) :
    muInvAux f M N (s • m) n = muInvAux f M N m (s • n) := by
  obtain ⟨r, rfl⟩ : ∃ r : R, f r = s := ⟨g s, hfg s⟩
  exact TensorProduct.smul_tmul (R := R)
    (M := ((ModuleCat.restrictScalars.{u} f).obj M))
    (N := ((ModuleCat.restrictScalars.{u} f).obj N)) r m n

/-- The underlying additive map `M ⊗[S] N →+ M ⊗[R] N` of the inverse of `μ`. -/
def muInvHom (hfg : ∀ s, f (g s) = s) (M N : ModuleCat.{u} S) :
    (M ⊗ N : ModuleCat.{u} S) →+
      TensorProduct R ((ModuleCat.restrictScalars.{u} f).obj M)
        ((ModuleCat.restrictScalars.{u} f).obj N) :=
  TensorProduct.liftAddHom (muInvAux f M N) (muInvAux_balanced f g hfg M N)

theorem muInvHom_tmul (hfg : ∀ s, f (g s) = s) (M N : ModuleCat.{u} S) (m : M) (n : N) :
    muInvHom f g hfg M N (TensorProduct.tmul S m n) = muInvAux f M N m n :=
  TensorProduct.liftAddHom_tmul _ _ m n

theorem muInvHom_smul (hfg : ∀ s, f (g s) = s) (M N : ModuleCat.{u} S) (r : R)
    (x : (M ⊗ N : ModuleCat.{u} S)) :
    muInvHom f g hfg M N (f r • x) = r • muInvHom f g hfg M N x := by
  refine TensorProduct.induction_on x ?_ (fun m n => ?_) (fun x y hx hy => ?_)
  · rw [smul_zero, map_zero, smul_zero]
  · rw [TensorProduct.smul_tmul' (R := S) (f r) m n, muInvHom_tmul, muInvHom_tmul]
    exact (TensorProduct.smul_tmul' (R := R)
      (M := ((ModuleCat.restrictScalars.{u} f).obj M))
      (N := ((ModuleCat.restrictScalars.{u} f).obj N)) r m n).symm
  · rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The inverse of `μ` for restriction of scalars along a ring isomorphism. -/
def restrictScalarsMuInv (hfg : ∀ s, f (g s) = s) (M N : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars.{u} f).obj (M ⊗ N) ⟶
      (ModuleCat.restrictScalars.{u} f).obj M ⊗ (ModuleCat.restrictScalars.{u} f).obj N :=
  ModuleCat.homEquiv.symm
    { toFun := fun x => muInvHom f g hfg M N x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => muInvHom_smul f g hfg M N r x }

theorem mu_muInvHom (hfg : ∀ s, f (g s) = s) (M N : ModuleCat.{u} S)
    (x : (M ⊗ N : ModuleCat.{u} S)) :
    (μ (ModuleCat.restrictScalars.{u} f) M N).hom (muInvHom f g hfg M N x) = x := by
  refine TensorProduct.induction_on x ?_ (fun m n => ?_) (fun x y hx hy => ?_)
  · rw [map_zero, map_zero]
    rfl
  · rw [muInvHom_tmul]
    exact ModuleCat.restrictScalars_μ_tmul f M N m n
  · rw [map_add, map_add, hx, hy]
    rfl

theorem restrictScalars_isIso_μ (hfg : ∀ s, f (g s) = s) (M N : ModuleCat.{u} S) :
    IsIso (μ (ModuleCat.restrictScalars.{u} f) M N) := by
  refine ⟨restrictScalarsMuInv f g hfg M N, ?_, ?_⟩
  · refine ModuleCat.MonoidalCategory.tensor_ext (fun m n => ?_)
    show (restrictScalarsMuInv f g hfg M N).hom
        ((μ (ModuleCat.restrictScalars.{u} f) M N).hom (TensorProduct.tmul R m n))
      = TensorProduct.tmul R m n
    exact (congrArg (fun z => (restrictScalarsMuInv f g hfg M N).hom z)
      (ModuleCat.restrictScalars_μ_tmul f M N m n)).trans (muInvHom_tmul f g hfg M N m n)
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact mu_muInvHom f g hfg M N x

end ModuleCat

namespace PresheafOfModules

/-- A morphism of presheaves of modules whose components are isomorphisms is an isomorphism
(`toPresheaf` reflects isomorphisms). -/
theorem isIso_of_isIso_app {C : Type u'} [Category.{v'} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} R} (φ : M ⟶ N)
    (h : ∀ X, IsIso (φ.app X)) : IsIso φ := by
  have happ : ∀ X, IsIso (((PresheafOfModules.toPresheaf.{u} R).map φ).app X) := by
    intro X
    have : IsIso (φ.app X) := h X
    show IsIso ((CategoryTheory.forget₂ (ModuleCat _) Ab).map (φ.app X))
    infer_instance
  have : IsIso ((PresheafOfModules.toPresheaf.{u} R).map φ) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso φ (PresheafOfModules.toPresheaf.{u} R)

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{u}} (α : R ⟶ R')

/-- Restriction of scalars along an isomorphism of presheaves of commutative rings is **strong**
monoidal. -/
noncomputable instance restrictScalarsC_monoidal [IsIso α] :
    (PresheafOfModules.restrictScalarsC.{u} α).Monoidal := by
  have hgf : ∀ (X : Cᵒᵖ) (r : R.obj X), (CategoryTheory.inv α).app X ((α.app X) r) = r := by
    intro X r
    exact congrArg (fun (β : R ⟶ R) => (β.app X) r) (IsIso.hom_inv_id α)
  have hfg : ∀ (X : Cᵒᵖ) (s : R'.obj X), (α.app X) ((CategoryTheory.inv α).app X s) = s := by
    intro X s
    exact congrArg (fun (β : R' ⟶ R') => (β.app X) s) (IsIso.inv_hom_id α)
  have hε : IsIso (ε (PresheafOfModules.restrictScalarsC.{u} α)) := by
    refine PresheafOfModules.isIso_of_isIso_app _ (fun X => ?_)
    exact ModuleCat.restrictScalars_isIso_ε (α.app X).hom ((CategoryTheory.inv α).app X).hom
      (hgf X) (hfg X)
  have hμ : ∀ M N, IsIso (μ (PresheafOfModules.restrictScalarsC.{u} α) M N) := by
    intro M N
    refine PresheafOfModules.isIso_of_isIso_app _ (fun X => ?_)
    exact ModuleCat.restrictScalars_isIso_μ (α.app X).hom ((CategoryTheory.inv α).app X).hom
      (hfg X) (M.obj X) (N.obj X)
  exact Functor.Monoidal.ofLaxMonoidal _

end PresheafOfModules

end
