import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap

/-! # The pullback unit and open immersions

Auxiliary lemmas for the compatibility of the adjunction unit with open immersions (used in the
proof of the base-change formula for sections, Stacks 01I9):
1. `isIso_transpose_of_iso`: invertibility of the base-change transpose is invariant under module
   isomorphisms of source and target (pure algebra, variable level).
2. `restrictFunctorIsoPullback_hom_app_apply`: the isomorphism "restriction ≅ pullback" of an open
   immersion `j` acts on sections as "unit, then restrict" (from Mathlib
   `Adjunction.unit_leftAdjointUniq_hom_app`).
3. `pullbackComp_inv_app_unit`: the inverse of `pullbackComp` sends the unit of a composite to
   the two units (from Mathlib `unit_conjugateEquiv` and `conjugateEquiv_pullbackComp_inv`), for
   sections over an arbitrary open (`pullback_comp_inv` in `ModuleSectionPullback.lean` covers only
   global sections).
4. `pullbackCongr_hom_app_pullbackSectionsOn`: transport along an equality of morphisms preserves
   the pullback of sections.
5. Scalar compatibility for `fromSpec`: the action of `Γ(X, U)` on `Γ(M.restrict hU.fromSpec, W)`
   (the instance from Mathlib's `Tilde`) equals the action after restricting to `j(W)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry

/-- Restricting along two mutually inverse inclusions is the identity (the restriction map between
equal opens is the identity). -/
theorem map_homOfLE_map_homOfLE_self {Z : AlgebraicGeometry.Scheme.{u}} (Q : Z.Modules) {U V : Z.Opens} (h : V ≤ U)
    (h' : U ≤ V) (x : Γ(Q, U)) :
    Q.presheaf.map (homOfLE h').op (Q.presheaf.map (homOfLE h).op x) = x := by
  rw [famRes_comp']
  have : (homOfLE (h'.trans h) : U ⟶ U) = 𝟙 U := rfl
  rw [this, op_id, Q.presheaf.map_id]
  rfl

section Transport

/-- Invertibility of the base-change transpose is invariant under isomorphisms of source and target
modules: if `eM.hom ≫ α₁ = α₀ ≫ res(eN.hom)` and the transpose of `α₀` is bijective, then the
transpose of `α₁` is an isomorphism. -/
theorem isIso_transpose_of_iso {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {M₀ M₁ : ModuleCat.{u} R} {N₀ N₁ : ModuleCat.{u} S}
    (α₀ : M₀ ⟶ (ModuleCat.restrictScalars f).obj N₀) (α₁ : M₁ ⟶ (ModuleCat.restrictScalars f).obj N₁)
    (eM : M₀ ≅ M₁) (eN : N₀ ≅ N₁)
    (hcomm : eM.hom ≫ α₁ = α₀ ≫ (ModuleCat.restrictScalars f).map eN.hom)
    (h₀ : Function.Bijective (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm α₀)) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm α₁) := by
  have key : (ModuleCat.extendScalars f).map eM.hom ≫
      ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm α₁ =
      ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm α₀ ≫ eN.hom := by
    apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, hcomm]
  haveI : IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm α₀) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h₀
  have e : ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm α₁ =
      inv ((ModuleCat.extendScalars f).map eM.hom) ≫
        (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm α₀ ≫ eN.hom) := by
    rw [← key, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

end Transport

section UnitCompat

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- The two components of an isomorphism of sheaves of modules are inverse to each other on sections. -/
theorem modIso_hom_app_inv_app {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(N, U)) :
    e.hom.app U (e.inv.app U x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ U) e.inv_hom_id) x

theorem modIso_inv_app_hom_app {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    e.inv.app U (e.hom.app U x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ U) e.hom_inv_id) x

/-- **The unit is compatible with open immersions**: the isomorphism "restriction ≅ pullback" of an
open immersion `j` (Mathlib `restrictFunctorIsoPullback`, from the uniqueness of left adjoints)
acts on sections over `W` as "take the unit, then restrict to `W`". -/
theorem restrictFunctorIsoPullback_hom_app_apply (j : Z ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (W : Z.Opens) (x : Γ(M, j ''ᵁ W)) :
    ((restrictFunctorIsoPullback j).app M).hom.app W x =
      pullbackSectionsOn j M (j ''ᵁ W) W (le_of_eq (j.preimage_image_eq W).symm) x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j)
    (pullbackPushforwardAdjunction j) M
  have h1 := ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ (j ''ᵁ W)) h) x
  have h2 : ((restrictFunctorIsoPullback j).app M).hom.app (j ⁻¹ᵁ (j ''ᵁ W))
      (M.presheaf.map (homOfLE (j.image_preimage_le (j ''ᵁ W))).op x) =
      pullbackUnitHom j M (j ''ᵁ W) x := h1
  have h3 := app_map ((restrictFunctorIsoPullback j).app M).hom
    (le_of_eq (j.preimage_image_eq W).symm)
    (M.presheaf.map (homOfLE (j.image_preimage_le (j ''ᵁ W))).op x)
  have h4 : (M.restrict j).presheaf.map (homOfLE (le_of_eq (j.preimage_image_eq W).symm)).op
      (M.presheaf.map (homOfLE (j.image_preimage_le (j ''ᵁ W))).op x) = x :=
    map_homOfLE_map_homOfLE_self M (j.image_preimage_le (j ''ᵁ W))
      (j.image_mono (le_of_eq (j.preimage_image_eq W).symm)) x
  have h5 : ((restrictFunctorIsoPullback j).app M).hom.app W x =
      ((restrictFunctorIsoPullback j).app M).hom.app W
        ((M.restrict j).presheaf.map (homOfLE (le_of_eq (j.preimage_image_eq W).symm)).op
          (M.presheaf.map (homOfLE (j.image_preimage_le (j ''ᵁ W))).op x)) :=
    congrArg (fun y => ((restrictFunctorIsoPullback j).app M).hom.app W y) h4.symm
  have h6 := congrArg (fun y => ((pullback j).obj M).presheaf.map
    (homOfLE (le_of_eq (j.preimage_image_eq W).symm)).op y) h2
  exact h5.trans (h3.trans h6)

/-- The inverse of `pullbackComp` sends the unit of `f ≫ g` to the two units (sections over an
arbitrary open `U`). -/
theorem pullbackComp_inv_app_unit (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens)
    (s : Γ(M, U)) :
    ((pullbackComp f g).app M).inv.app ((f ≫ g) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s) =
      ((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U s) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h1 := ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ U) h) s
  exact h1.symm

/-- Transport along an equality of morphisms preserves the pullback of sections. -/
theorem pullbackCongr_hom_app_pullbackSectionsOn {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules)
    (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) (h' : W ≤ f' ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((pullbackCongr e).app M).hom.app W (pullbackSectionsOn f M U W h s) =
      pullbackSectionsOn f' M U W h' s := by
  subst e
  rfl

/-- The unit commutes with restriction (`pullbackUnitHom_restrict` in `Hom.app` form). -/
theorem unit_app_map (f : X ⟶ Y) (M : Y.Modules) {V W : Y.Opens} (hW : W ≤ V) (s : Γ(M, V)) :
    ((pullbackPushforwardAdjunction f).unit.app M).app W (M.presheaf.map (homOfLE hW).op s) =
      ((pullback f).obj M).presheaf.map
        (homOfLE (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V from fun _ hx => hW hx)).op
        (((pullbackPushforwardAdjunction f).unit.app M).app V s) :=
  pullbackUnitHom_restrict f M hW s

/-- Naturality of the unit on sections: `((f^*ψ).app U)(η_M s) = η_N (ψ.app U s)`. -/
theorem unit_naturality_app (f : X ⟶ Y) {M N : Y.Modules} (ψ : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
    ((pullback f).map ψ).app (f ⁻¹ᵁ U) (((pullbackPushforwardAdjunction f).unit.app M).app U s) =
      ((pullbackPushforwardAdjunction f).unit.app N).app U (ψ.app U s) := by
  have h := (pullbackPushforwardAdjunction f).unit.naturality ψ
  have h1 := ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ U) h) s
  exact h1.symm

end UnitCompat

section FromSpec

variable {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem fromSpec_image_le (W : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ W ≤ U := by
  have := Scheme.Hom.image_le_opensRange hU.fromSpec W
  rwa [hU.opensRange_fromSpec] at this

theorem fromSpec_image_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

theorem fromSpec_ring_key (W : (Spec Γ(X, U)).Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map W.leTop.op ≫
      (hU.fromSpec.appIso W).inv = X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op := by
  have h1 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map W.leTop.op =
      hU.fromSpec.appLE U W (by rw [hU.fromSpec_preimage_self]; exact le_top) := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rfl
  rw [← Category.assoc, h1, Scheme.Hom.appLE_appIso_inv]

/-- The action of `Γ(X, U)` on `Γ(M.restrict hU.fromSpec, W) = Γ(M, j(W))` (the `Module R Γ(N, W)`
instance of Mathlib's `Tilde`) equals the action of `r` restricted to `j(W)`. -/
theorem fromSpec_smul_key (M : X.Modules) (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U))
    (x : Γ(M.restrict hU.fromSpec, W)) :
    r • x = (M.restrictAppIso hU.fromSpec W).inv
      ((X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r) •
        (M.restrictAppIso hU.fromSpec W).hom x) := by
  rw [Scheme.Modules.smul_Spec_def, ← fromSpec_ring_key hU W]
  rfl

end FromSpec

end AlgebraicGeometry.Scheme.Modules

end
