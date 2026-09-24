import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion

/-! # Base change of global sections along `Spec φ` (Stacks 01I9, Spec version)

Let `φ : A → B` be a ring map, `g = Spec φ : Spec B → Spec A`, and `N` a quasi-coherent module on
`Spec A`. The adjunction unit on global sections `η : Γ(N, ⊤) → Γ(g^*N, ⊤)` is `A`-linear (with
`Γ(g^*N, ⊤)` viewed over `A` through `φ`), and its transpose
`τ : B ⊗_A Γ(N, ⊤) → Γ(g^*N, ⊤)`, `b ⊗ s ↦ b · η(s)`, is an isomorphism
(`SpecBaseChange.isIso_τ` / `bijective_τ`).

Proof (two adjunctions and Mathlib's tilde equivalence; no computation of the sheafification of
`g^*` is needed). Let `T := B ⊗_A Γ(N, ⊤)`.
1. By `tilde ⊣ Γ` on `Spec B` (Mathlib `tilde.adjunction`), `τ` corresponds to `χ : T~ → g^*N`.
2. By `N ≅ Γ(N)~` (`N` quasi-coherent, Mathlib `isIso_fromTildeΓ_of_isQuasicoherent`), `tilde ⊣ Γ` on
   `Spec A`, and the `A`-linear map `ι' : Γ(N, ⊤) → T → Γ(T~, ⊤) = Γ(g_* T~, ⊤)` (`s ↦ 1 ⊗ s`, then
   `toOpen`), we get `ψ' : N → g_* T~`, and by `g^* ⊣ g_*` a morphism `ψ : g^*N → T~`.
3. `ψ ≫ χ = 1`: by `g^* ⊣ g_*` this is `ψ' ≫ g_*χ = η`; by `N ≅ Γ(N)~` and `tilde ⊣ Γ` it reduces to
   an identity on global sections, checked elementwise.
4. `χ ≫ ψ = 1`: by `tilde ⊣ Γ` this is `τ ≫ Γ(ψ) = toOpen`; by `B ⊗_A – ⊣ restriction of scalars`
   it reduces to an identity of `A`-linear maps, checked elementwise.
5. Hence `χ` is an isomorphism, and so is `τ = toOpen ≫ Γ(χ)`.

The key scalar compatibility (`smul_pushforward`): the action of `A` on `Γ(g_* Q, U) = Γ(Q, g⁻¹U)`
(the `Module R Γ(M, U)` instance of Mathlib's `Tilde`) is the action of `B` through `φ`, by
naturality of `ΓSpecIso` for `Spec φ`.

References: Stacks 01I9 (schemes-lemma-widetilde-pullback); Hartshorne II.5.2(e). The proof here
replaces the direct computation of Stacks by the adjunction characterization.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

namespace SpecBaseChange

open AlgebraicGeometry

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-- The action of `A` on `Γ(g_* Q, U) = Γ(Q, g⁻¹U)` (the `Module R Γ(M, U)` instance of Mathlib's
`Tilde`) is the action of `B` through `φ`. The `A`-action instance on `Γ((g_* Q), U)` is written
explicitly on the left for `rw`. -/
theorem smul_pushforward' (Q : (Spec B).Modules) (U : (Spec A).Opens) (a : A)
    (x : Γ(Q, Spec.map φ ⁻¹ᵁ U)) :
    (a • (show Γ((pushforward (Spec.map φ)).obj Q, U) from x) : Γ((pushforward (Spec.map φ)).obj Q, U)) =
      (φ a • x : Γ(Q, Spec.map φ ⁻¹ᵁ U)) := by
  rw [smul_Spec_def, smul_Spec_def]
  change (((Spec.map φ).app U ((Spec A).presheaf.map U.leTop.op ((Scheme.ΓSpecIso A).inv a))) • x :
    Γ(Q, Spec.map φ ⁻¹ᵁ U)) = _
  congr 1
  have h1 := ConcreteCategory.congr_hom ((Spec.map φ).naturality U.leTop.op) ((Scheme.ΓSpecIso A).inv a)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  rw [h1]
  have h2 := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  rw [h2]
  rfl

/-- As above, with the `A`-action instance on `Γ(g_* Q, U)` written explicitly on the left. -/
theorem smul_pushforward (Q : (Spec B).Modules) (U : (Spec A).Opens) (a : A)
    (x : Γ(Q, Spec.map φ ⁻¹ᵁ U)) :
    @HSMul.hSMul A Γ((pushforward (Spec.map φ)).obj Q, U) Γ((pushforward (Spec.map φ)).obj Q, U)
      instHSMul a x = φ a • x :=
  smul_pushforward' φ Q U a x

/-- `Γ_A(g_* Q) → (Γ_B Q with scalars restricted along φ)`; the underlying map is restriction along
`g⁻¹⊤ = ⊤`. -/
def resDown (Q : (Spec B).Modules) :
    ModuleCat.of A Γ((pushforward (Spec.map φ)).obj Q, ⊤) ⟶
      (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B Γ(Q, ⊤)) :=
  ModuleCat.ofHom (X := ModuleCat.of A Γ((pushforward (Spec.map φ)).obj Q, ⊤))
    (Y := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B Γ(Q, ⊤)))
    ({ toFun := fun x => Q.presheaf.map (homOfLE (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)).op x
       map_add' := fun x y => map_add _ x y
       map_smul' := fun a x => by
         have h1 := congrArg (fun y : Γ(Q, Spec.map φ ⁻¹ᵁ ⊤) =>
           Q.presheaf.map (homOfLE (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)).op y) (smul_pushforward φ Q ⊤ a x)
         exact h1.trans (map_smul_Spec _ (φ a) x) } :
      Γ((pushforward (Spec.map φ)).obj Q, ⊤) →ₗ[A]
        (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B Γ(Q, ⊤)))

/-- `(Γ_B Q with scalars restricted along φ) → Γ_A(g_* Q)`, the inverse of `resDown`. -/
def resUp (Q : (Spec B).Modules) :
    (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B Γ(Q, ⊤)) ⟶
      ModuleCat.of A Γ((pushforward (Spec.map φ)).obj Q, ⊤) :=
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B Γ(Q, ⊤)))
    (Y := ModuleCat.of A Γ((pushforward (Spec.map φ)).obj Q, ⊤))
    ({ toFun := fun x => Q.presheaf.map (homOfLE (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤)).op x
       map_add' := fun x y => map_add _ x y
       map_smul' := fun a x => by
         have h1 : Q.presheaf.map (homOfLE (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤)).op (φ a • x) =
             φ a • Q.presheaf.map (homOfLE (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤)).op x :=
           map_smul_Spec _ (φ a) x
         exact h1.trans (smul_pushforward φ Q ⊤ a _).symm } :
      (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B Γ(Q, ⊤)) →ₗ[A]
        Γ((pushforward (Spec.map φ)).obj Q, ⊤))

variable (N : (Spec A).Modules)

/-- `Γ(N, ⊤)` as an `A`-module (written `moduleSpecΓFunctor.obj N`, matching the syntax of Mathlib's
tilde adjunction). -/
abbrev ΓN : ModuleCat.{u} A := moduleSpecΓFunctor.obj N

/-- T := B ⊗_A Γ(N, ⊤) -/
abbrev T : ModuleCat.{u} B := (ModuleCat.extendScalars φ.hom).obj (ΓN N)

/-- P := g^* N -/
abbrev P : (Spec B).Modules := (pullback (Spec.map φ)).obj N

/-- The unit `η : N → g_* g^* N`. -/
abbrev η : N ⟶ (pushforward (Spec.map φ)).obj (P φ N) :=
  (pullbackPushforwardAdjunction (Spec.map φ)).unit.app N

/-- The unit on global sections: `Γ(N, ⊤) → Γ(g_* g^* N, ⊤)` (`A`-linear). -/
def unitΓ : ΓN N ⟶ ModuleCat.of A Γ((pushforward (Spec.map φ)).obj (P φ N), ⊤) :=
  moduleSpecΓFunctor.map (η φ N)

/-- `α : Γ(N, ⊤) → Γ(g^*N, ⊤)`, `A`-linear (target with scalars restricted along `φ`). -/
def α : ΓN N ⟶ (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj (P φ N)) :=
  unitΓ φ N ≫ resDown φ (P φ N)

theorem α_apply (m : Γ(N, ⊤)) :
    α φ N m = (P φ N).presheaf.map (homOfLE le_top).op ((η φ N).app ⊤ m) := rfl

/-- `τ : B ⊗_A Γ(N, ⊤) → Γ(g^*N, ⊤)`, the transpose of `α`. -/
def τ : T φ N ⟶ moduleSpecΓFunctor.obj (P φ N) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm (α φ N)

theorem homEquiv_τ : ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _) (τ φ N) = α φ N :=
  Equiv.apply_symm_apply _ _

theorem τ_unit (m : Γ(N, ⊤)) :
    τ φ N ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) m) = α φ N m := by
  have h := homEquiv_τ φ N
  rw [Adjunction.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom h m

/-- χ : T~ → g^*N -/
def χ : (tilde.functor B).obj (T φ N) ⟶ P φ N :=
  ((tilde.adjunction (R := B)).homEquiv _ _).symm (τ φ N)

theorem unit_Γmap_χ :
    (tilde.adjunction (R := B)).unit.app (T φ N) ≫ moduleSpecΓFunctor.map (χ φ N) = τ φ N := by
  have h : (tilde.adjunction (R := B)).homEquiv _ _ (χ φ N) = τ φ N := Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact h

theorem χ_app_top_toOpen (t : T φ N) :
    (χ φ N).app ⊤ (tilde.toOpen (T φ N) ⊤ t) = τ φ N t := by
  have h := ConcreteCategory.congr_hom (unit_Γmap_χ φ N) t
  rw [ConcreteCategory.comp_apply] at h
  exact h

/-- `ι' : Γ(N, ⊤) → Γ(g_* T~, ⊤)`, `s ↦ toOpen(1 ⊗ s)` (`A`-linear). -/
def ι' : ΓN N ⟶ ModuleCat.of A Γ((pushforward (Spec.map φ)).obj ((tilde.functor B).obj (T φ N)), ⊤) :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) ≫
    (ModuleCat.restrictScalars φ.hom).map ((tilde.adjunction (R := B)).unit.app (T φ N)) ≫
    resUp φ _

theorem ι'_apply (m : Γ(N, ⊤)) :
    ι' φ N m = ((tilde.functor B).obj (T φ N)).presheaf.map (homOfLE le_top).op
      (tilde.toOpen (T φ N) ⊤ ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) m)) := rfl

/-- θ : Γ(N)~ → g_* T~ -/
def θ : (tilde.functor A).obj (ΓN N) ⟶
    (pushforward (Spec.map φ)).obj ((tilde.functor B).obj (T φ N)) :=
  ((tilde.adjunction (R := A)).homEquiv _ _).symm (ι' φ N)

theorem homEquiv_θ : (tilde.adjunction (R := A)).homEquiv _ _ (θ φ N) = ι' φ N :=
  Equiv.apply_symm_apply _ _

theorem θ_app_top_toOpen (m : Γ(N, ⊤)) :
    (θ φ N).app ⊤ (tilde.toOpen (ΓN N) ⊤ m) = ι' φ N m := by
  have h := homEquiv_θ φ N
  rw [Adjunction.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom h m

/-- The counit `Γ(N)~ → N`, with source written `(tilde.functor A).obj (ΓN N)` (syntactically the
source of `θ`). -/
def counit' : (tilde.functor A).obj (ΓN N) ⟶ N := (tilde.adjunction (R := A)).counit.app N

/-- The counit on `⊤`: `counit(toOpen m) = m`. -/
theorem counit'_app_top_toOpen (m : Γ(N, ⊤)) :
    (counit' N).app ⊤ (tilde.toOpen (ΓN N) ⊤ m) = m := by
  have h := (tilde.adjunction (R := A)).right_triangle_components N
  exact ConcreteCategory.congr_hom h m

/-- homEquiv(counit') = 𝟙 -/
theorem homEquiv_counit' : (tilde.adjunction (R := A)).homEquiv (ΓN N) N (counit' N) = 𝟙 (ΓN N) :=
  ((tilde.adjunction (R := A)).homEquiv_unit _ _ (counit' N)).trans
    ((tilde.adjunction (R := A)).right_triangle_components N)

variable [N.IsQuasicoherent]

theorem isIso_counit' : IsIso (counit' N) := N.isIso_fromTildeΓ_of_isQuasicoherent

/-- ψ' : N → g_* T~ -/
def ψ' : N ⟶ (pushforward (Spec.map φ)).obj ((tilde.functor B).obj (T φ N)) :=
  haveI := isIso_counit' N
  inv (counit' N) ≫ θ φ N

theorem ψ'_app_top (m : Γ(N, ⊤)) :
    (ψ' φ N).app ⊤ m = ((tilde.functor B).obj (T φ N)).presheaf.map (homOfLE le_top).op
      (tilde.toOpen (T φ N) ⊤ ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) m)) := by
  haveI := isIso_counit' N
  have h1 : (inv (counit' N)).app ⊤ m = tilde.toOpen (ΓN N) ⊤ m := by
    have h2 := counit'_app_top_toOpen N m
    have h3 : (inv (counit' N)).app ⊤ ((counit' N).app ⊤ (tilde.toOpen (ΓN N) ⊤ m)) =
        tilde.toOpen (ΓN N) ⊤ m := by
      rw [inv_app]
      exact IsIso.hom_inv_id_apply _ _
    rw [h2] at h3
    exact h3
  change (θ φ N).app ⊤ ((inv (counit' N)).app ⊤ m) = _
  rw [h1, θ_app_top_toOpen, ι'_apply]

/-- ψ : g^*N → T~ -/
def ψ : P φ N ⟶ (tilde.functor B).obj (T φ N) :=
  ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _).symm (ψ' φ N)

theorem unit_pushforward_ψ :
    η φ N ≫ (pushforward (Spec.map φ)).map (ψ φ N) = ψ' φ N := by
  have h : (pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ (ψ φ N) = ψ' φ N :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact h

theorem ψ_app_unit (m : Γ(N, ⊤)) :
    (ψ φ N).app (Spec.map φ ⁻¹ᵁ ⊤) ((η φ N).app ⊤ m) = (ψ' φ N).app ⊤ m := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => Hom.app f ⊤) (unit_pushforward_ψ φ N)) m
  exact h

theorem ψ_χ : ψ φ N ≫ χ φ N = 𝟙 _ := by
  haveI := isIso_counit' N
  have key : θ φ N ≫ (pushforward (Spec.map φ)).map (χ φ N) = counit' N ≫ η φ N := by
    apply ((tilde.adjunction (R := A)).homEquiv (ΓN N) _).injective
    refine ((tilde.adjunction (R := A)).homEquiv_naturality_right (θ φ N) _).trans ?_
    refine Eq.trans ?_ ((tilde.adjunction (R := A)).homEquiv_naturality_right (counit' N) _).symm
    rw [homEquiv_θ, homEquiv_counit', Category.id_comp]
    ext m
    have e1 : (ι' φ N ≫ moduleSpecΓFunctor.map ((pushforward (Spec.map φ)).map (χ φ N))) m =
        (χ φ N).app (Spec.map φ ⁻¹ᵁ ⊤)
          (((tilde.functor B).obj (T φ N)).presheaf.map (homOfLE le_top).op
            (tilde.toOpen (T φ N) ⊤ ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) m))) :=
      rfl
    have e2 := app_map (χ φ N) (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)
      (tilde.toOpen (T φ N) ⊤ ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) m))
    have e3 := congrArg (fun y => (P φ N).presheaf.map (homOfLE (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)).op y)
      (χ_app_top_toOpen φ N ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) m))
    have e4 := congrArg (fun y => (P φ N).presheaf.map (homOfLE (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)).op y)
      (τ_unit φ N m)
    have e5 : (P φ N).presheaf.map (homOfLE (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (α φ N m) =
        (P φ N).presheaf.map (homOfLE (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)).op
          ((P φ N).presheaf.map (homOfLE (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤)).op ((η φ N).app ⊤ m)) := rfl
    have e6 := map_homOfLE_map_homOfLE_self (P φ N) (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤) (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)
      ((η φ N).app ⊤ m)
    have e7 : (η φ N).app ⊤ m = (moduleSpecΓFunctor.map (η φ N)) m := rfl
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))
  apply ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    ← Category.assoc]
  change (η φ N ≫ (pushforward (Spec.map φ)).map (ψ φ N)) ≫ _ = _
  rw [unit_pushforward_ψ]
  calc ψ' φ N ≫ (pushforward (Spec.map φ)).map (χ φ N)
      = (inv (counit' N) ≫ θ φ N) ≫ (pushforward (Spec.map φ)).map (χ φ N) := rfl
    _ = inv (counit' N) ≫ (θ φ N ≫ (pushforward (Spec.map φ)).map (χ φ N)) := Category.assoc _ _ _
    _ = inv (counit' N) ≫ (counit' N ≫ η φ N) := by rw [key]
    _ = η φ N := IsIso.inv_hom_id_assoc _ _

theorem χ_ψ : χ φ N ≫ ψ φ N = 𝟙 _ := by
  apply ((tilde.adjunction (R := B)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    ← Category.assoc, unit_Γmap_χ]
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_τ]
  ext m
  have e1 : (α φ N ≫ (ModuleCat.restrictScalars φ.hom).map (moduleSpecΓFunctor.map (ψ φ N))) m =
      (ψ φ N).app ⊤ ((P φ N).presheaf.map (homOfLE (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤)).op
        ((η φ N).app ⊤ m)) := rfl
  have e2 := app_map (ψ φ N) (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤) ((η φ N).app ⊤ m)
  have e3 := congrArg
    (fun y => ((tilde.functor B).obj (T φ N)).presheaf.map (homOfLE (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤)).op y)
    (ψ_app_unit φ N m)
  have e4 := congrArg
    (fun y => ((tilde.functor B).obj (T φ N)).presheaf.map (homOfLE (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤)).op y)
    (ψ'_app_top φ N m)
  have e5 := map_homOfLE_map_homOfLE_self ((tilde.functor B).obj (T φ N)) (le_top : Spec.map φ ⁻¹ᵁ ⊤ ≤ ⊤)
    (le_top : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤)
    (tilde.toOpen (T φ N) ⊤ ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) m))
  have e6 : tilde.toOpen (T φ N) ⊤ ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ΓN N) m) =
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
        ((tilde.adjunction (R := B)).unit.app (T φ N))) m := rfl
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))

theorem isIso_χ : IsIso (χ φ N) := ⟨ψ φ N, χ_ψ φ N, ψ_χ φ N⟩

theorem isIso_τ : IsIso (τ φ N) := by
  rw [← unit_Γmap_χ]
  haveI h1 : IsIso ((tilde.adjunction (R := B)).unit.app (T φ N)) := tilde.isIso_toOpen_top
  haveI h2 : IsIso (χ φ N) := isIso_χ φ N
  haveI h3 : IsIso (moduleSpecΓFunctor.map (χ φ N)) := Functor.map_isIso moduleSpecΓFunctor (χ φ N)
  exact IsIso.comp_isIso

/-- **Stacks 01I9 (Spec version)**: `B ⊗_A Γ(N, ⊤) → Γ(g^*N, ⊤)`, `b ⊗ s ↦ b · η(s)`, is bijective. -/
theorem bijective_τ : Function.Bijective (τ φ N) :=
  have := isIso_τ φ N
  ConcreteCategory.bijective_of_isIso _

omit [N.IsQuasicoherent] in
/-- The `ModuleCat.of` form of `α` (the same term as `α`, with target written
`ModuleCat.of B Γ(g^*N, ⊤)`). -/
def α' : ΓN N ⟶ (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B Γ(P φ N, ⊤)) :=
  unitΓ φ N ≫ resDown φ (P φ N)

omit [N.IsQuasicoherent] in
theorem α'_apply (m : Γ(N, ⊤)) :
    α' φ N m = (P φ N).presheaf.map (homOfLE le_top).op ((η φ N).app ⊤ m) := rfl

/-- **Stacks 01I9 (Spec version, `ModuleCat.of` form)**: the transpose `B ⊗_A Γ(N, ⊤) → Γ(g^*N, ⊤)` of
`α'` is bijective. -/
theorem bijective_transpose :
    Function.Bijective (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv (ΓN N)
      (ModuleCat.of B Γ(P φ N, ⊤))).symm (α' φ N)) :=
  bijective_τ φ N

end SpecBaseChange

end AlgebraicGeometry.Scheme.Modules

end
