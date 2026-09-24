import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsSpecBaseChange

/-! # Base change of sections over affine opens (Stacks 01I9)

Let `g : Y → X`, `V ⊆ X` and `V' ⊆ g⁻¹V` affine opens, and `M` quasi-coherent. Then
`Γ(Y, V') ⊗_{Γ(X,V)} Γ(M, V) → Γ(g^*M, V')`, `t ⊗ s ↦ t·(g^*s)|_{V'}`, is an isomorphism (the
open-set version of Stacks 01I9; `pullbackSectionsNative` is the `Γ(X, V)`-linear pullback of
sections, defined in this file).

Proof.
(b) Spec case: `SpecBaseChange.bijective_transpose` — for `φ : A → B` and `N` quasi-coherent on
    `Spec A`, the map `B ⊗_A Γ(N, ⊤) → Γ((Spec φ)^*N, ⊤)` is bijective (two adjunctions and
    Mathlib's tilde equivalence).
(a) Transport to affine opens: let `j = hV.fromSpec : Spec Γ(X, V) → X`,
    `j' = hV'.fromSpec : Spec Γ(Y, V') → Y` (open immersions with images `V`, `V'`) and
    `φ = g^♯ : Γ(X, V) → Γ(Y, V')`, so that `Spec φ ≫ j = j' ≫ g` (Mathlib
    `IsAffineOpen.SpecMap_appLE_fromSpec`). `N := M|_{Spec Γ(X,V)}` is quasi-coherent,
    `(Spec φ)^*N ≅ (g^*M)|_{Spec Γ(Y,V')}` (`Φ`: restriction ≅ pullback, `pullbackComp`,
    `pullbackCongr`), and this isomorphism sends "unit, then restrict" to "unit, then restrict"
    (`Φ_hom_app_top`, verified elementwise with the compatibility lemmas of
    `PullbackUnitOpenImmersion.lean`). `Γ(N, ⊤) ≅ Γ(M, V)` and `Γ((Spec φ)^*N, ⊤) ≅ Γ(g^*M, V')`
    are linear isomorphisms (`restrictTopIso`; scalar compatibility by `fromSpec_smul_key`)
    commuting with the two base-change maps (`hcomm`), so `isIso_transpose_of_iso` concludes.

References: Stacks 01I9; Hartshorne II.5.2(e).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)

/-- The pullback of sections is semilinear over `Γ(X, V)`: `(x • s) ↦ g^♯(x)|_{V'} • (g^*s)|_{V'}`. -/
theorem pullbackSectionsOn_smul_native (M : X.Modules) (V : X.Opens) (V' : Y.Opens)
    (h : V' ≤ g ⁻¹ᵁ V) (x : Γ(X, V)) (s : Γ(M, V)) :
    pullbackSectionsOn g M V V' h (x • s) = (g.appLE V V' h).hom x • pullbackSectionsOn g M V V' h s := by
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply, pullbackUnitHom_smul,
    AlgebraicGeometry.Scheme.Modules.map_smul]
  rfl

/-- The pullback of sections as a `Γ(X, V)`-linear map `Γ(M, V) → Γ(g^*M, V')` (the target with
scalars restricted along `g^♯ : Γ(X, V) → Γ(Y, V')`). -/
def pullbackSectionsNative (M : X.Modules) (V : X.Opens) (V' : Y.Opens) (h : V' ≤ g ⁻¹ᵁ V) :
    (ModuleCat.of Γ(X, V) Γ(M, V)) ⟶
      (ModuleCat.restrictScalars (g.appLE V V' h).hom).obj
        (ModuleCat.of Γ(Y, V') Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V')) :=
  ModuleCat.ofHom
    (Y := ((ModuleCat.restrictScalars (g.appLE V V' h).hom).obj
        (ModuleCat.of Γ(Y, V') Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V')) :
      ModuleCat Γ(X, V)))
    { toFun := pullbackSectionsOn g M V V' h
      map_add' := _root_.map_add _
      map_smul' := fun x s => pullbackSectionsOn_smul_native g M V V' h x s }

namespace NativeBaseChangeAux

open AlgebraicGeometry

/-- Restriction of the structure sheaf: restricting and restricting back is the identity (for equal
opens). -/
theorem ring_res_res (Z : Scheme.{u}) {U V : Z.Opens} (h : V ≤ U) (h' : U ≤ V) (r : Γ(Z, U)) :
    Z.presheaf.map (homOfLE h').op (Z.presheaf.map (homOfLE h).op r) = r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have : ((homOfLE h).op ≫ (homOfLE h').op : op U ⟶ op U) = 𝟙 (op U) := rfl
  rw [this, Z.presheaf.map_id]
  rfl

section RestrictTop

variable {Z : Scheme.{u}} {U : Z.Opens} (hU : IsAffineOpen U) (M : Z.Modules)

theorem le_image_top : U ≤ hU.fromSpec ''ᵁ ⊤ := le_of_eq (fromSpec_image_top hU).symm
theorem image_top_le : hU.fromSpec ''ᵁ ⊤ ≤ U := le_of_eq (fromSpec_image_top hU)

/-- `Γ(M|_{Spec Γ(Z,U)}, ⊤) → Γ(M, U)` (restriction along `j(⊤) = U`), `Γ(Z, U)`-linear. -/
def restrictTopHom : moduleSpecΓFunctor.obj (M.restrict hU.fromSpec) ⟶ ModuleCat.of Γ(Z, U) Γ(M, U) :=
  ModuleCat.ofHom (X := moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) (Y := ModuleCat.of Γ(Z, U) Γ(M, U))
    ({ toFun := fun x => M.presheaf.map (homOfLE (le_image_top hU)).op x
       map_add' := fun x y => map_add _ x y
       map_smul' := fun r x => by
         have e1 : M.presheaf.map (homOfLE (le_image_top hU)).op (r • x) =
             M.presheaf.map (homOfLE (le_image_top hU)).op
               ((Z.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op r) •
                 (M.restrictAppIso hU.fromSpec ⊤).hom x) :=
           congrArg (fun y => M.presheaf.map (homOfLE (le_image_top hU)).op y) (fromSpec_smul_key hU M ⊤ r x)
         have e2 := AlgebraicGeometry.Scheme.Modules.map_smul (M := M) (homOfLE (le_image_top hU))
           (Z.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op r) ((M.restrictAppIso hU.fromSpec ⊤).hom x)
         have e3 := congrArg (fun t => t • M.presheaf.map (homOfLE (le_image_top hU)).op x)
           (ring_res_res Z (fromSpec_image_le hU ⊤) (le_image_top hU) r)
         exact e1.trans (e2.trans e3) } :
      Γ(M.restrict hU.fromSpec, ⊤) →ₗ[Γ(Z, U)] Γ(M, U))

/-- `Γ(M, U) → Γ(M|_{Spec Γ(Z,U)}, ⊤)`, the inverse of `restrictTopHom`. -/
def restrictTopInv : ModuleCat.of Γ(Z, U) Γ(M, U) ⟶ moduleSpecΓFunctor.obj (M.restrict hU.fromSpec) :=
  ModuleCat.ofHom (X := ModuleCat.of Γ(Z, U) Γ(M, U)) (Y := moduleSpecΓFunctor.obj (M.restrict hU.fromSpec))
    ({ toFun := fun x => M.presheaf.map (homOfLE (image_top_le hU)).op x
       map_add' := fun x y => map_add _ x y
       map_smul' := fun r x => by
         have e1 := AlgebraicGeometry.Scheme.Modules.map_smul (M := M) (homOfLE (image_top_le hU)) r x
         have e2 := (fromSpec_smul_key hU M ⊤ r (M.presheaf.map (homOfLE (image_top_le hU)).op x)).symm
         exact e1.trans e2 } :
      Γ(M, U) →ₗ[Γ(Z, U)] Γ(M.restrict hU.fromSpec, ⊤))

/-- `Γ(M|_{Spec Γ(Z,U)}, ⊤) ≅ Γ(M, U)` as `Γ(Z, U)`-modules. -/
def restrictTopIso : moduleSpecΓFunctor.obj (M.restrict hU.fromSpec) ≅ ModuleCat.of Γ(Z, U) Γ(M, U) where
  hom := restrictTopHom hU M
  inv := restrictTopInv hU M
  hom_inv_id := by
    ext x
    exact map_homOfLE_map_homOfLE_self M (le_image_top hU) (image_top_le hU) x
  inv_hom_id := by
    ext x
    exact map_homOfLE_map_homOfLE_self M (image_top_le hU) (le_image_top hU) x

theorem restrictTopIso_hom_apply (x : Γ(M.restrict hU.fromSpec, ⊤)) :
    (restrictTopIso hU M).hom x = M.presheaf.map (homOfLE (le_image_top hU)).op x := rfl

end RestrictTop

section Main

variable (M : X.Modules) {V : X.Opens} (hV : IsAffineOpen V) {V' : Y.Opens} (hV' : IsAffineOpen V')
  (h : V' ≤ g ⁻¹ᵁ V)

theorem square : Spec.map (g.appLE V V' h) ≫ hV.fromSpec = hV'.fromSpec ≫ g :=
  IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' h

include h in
theorem image_top_le_preimage : hV'.fromSpec ''ᵁ ⊤ ≤ g ⁻¹ᵁ (hV.fromSpec ''ᵁ ⊤) := by
  rw [fromSpec_image_top, fromSpec_image_top]
  exact h

/-- Φ : (Spec φ)^*(M|_{Spec Γ(X,V)}) ≅ (g^*M)|_{Spec Γ(Y,V')} -/
def Φ : (pullback (Spec.map (g.appLE V V' h))).obj (M.restrict hV.fromSpec) ≅
    ((pullback g).obj M).restrict hV'.fromSpec :=
  (pullback (Spec.map (g.appLE V V' h))).mapIso ((restrictFunctorIsoPullback hV.fromSpec).app M) ≪≫
  (pullbackComp (Spec.map (g.appLE V V' h)) hV.fromSpec).app M ≪≫
  (pullbackCongr (square g hV hV' h)).app M ≪≫
  ((pullbackComp hV'.fromSpec g).app M).symm ≪≫
  ((restrictFunctorIsoPullback hV'.fromSpec).app ((pullback g).obj M)).symm

/-! Notation (reducible abbreviations, transparent to `rw`) -/

/-- f := Spec φ -/
abbrev fφ : Spec Γ(Y, V') ⟶ Spec Γ(X, V) := Spec.map (g.appLE V V' h)
/-- U := j(⊤) -/
abbrev Uj : X.Opens := hV.fromSpec ''ᵁ ⊤
/-- U' := j'(⊤) -/
abbrev Uj' : Y.Opens := hV'.fromSpec ''ᵁ ⊤
/-- ρ : M|_j ≅ j^*M -/
abbrev ρ : M.restrict hV.fromSpec ≅ (pullback hV.fromSpec).obj M := (restrictFunctorIsoPullback hV.fromSpec).app M
/-- ρ' : (g^*M)|_{j'} ≅ j'^*(g^*M) -/
abbrev ρ' : ((pullback g).obj M).restrict hV'.fromSpec ≅ (pullback hV'.fromSpec).obj ((pullback g).obj M) :=
  (restrictFunctorIsoPullback hV'.fromSpec).app ((pullback g).obj M)
/-- `η^f` on `M|_j`. -/
abbrev ηf : M.restrict hV.fromSpec ⟶ (pushforward (fφ g h)).obj ((pullback (fφ g h)).obj (M.restrict hV.fromSpec)) :=
  (pullbackPushforwardAdjunction (fφ g h)).unit.app (M.restrict hV.fromSpec)
/-- `η^f` on `j^*M`. -/
abbrev ηfj : (pullback hV.fromSpec).obj M ⟶
    (pushforward (fφ g h)).obj ((pullback (fφ g h)).obj ((pullback hV.fromSpec).obj M)) :=
  (pullbackPushforwardAdjunction (fφ g h)).unit.app ((pullback hV.fromSpec).obj M)
/-- `η^j` on `M`. -/
abbrev ηj : M ⟶ (pushforward hV.fromSpec).obj ((pullback hV.fromSpec).obj M) :=
  (pullbackPushforwardAdjunction hV.fromSpec).unit.app M
/-- `η^{f ≫ j}` on `M`. -/
abbrev ηfjc : M ⟶ (pushforward (fφ g h ≫ hV.fromSpec)).obj ((pullback (fφ g h ≫ hV.fromSpec)).obj M) :=
  (pullbackPushforwardAdjunction (fφ g h ≫ hV.fromSpec)).unit.app M
/-- `η^{j' ≫ g}` on `M`. -/
abbrev ηjgc : M ⟶ (pushforward (hV'.fromSpec ≫ g)).obj ((pullback (hV'.fromSpec ≫ g)).obj M) :=
  (pullbackPushforwardAdjunction (hV'.fromSpec ≫ g)).unit.app M
/-- `η^{j'}` on `g^*M`. -/
abbrev ηj' : (pullback g).obj M ⟶ (pushforward hV'.fromSpec).obj ((pullback hV'.fromSpec).obj ((pullback g).obj M)) :=
  (pullbackPushforwardAdjunction hV'.fromSpec).unit.app ((pullback g).obj M)
/-- `η^g` on `M`. -/
abbrev ηg : M ⟶ (pushforward g).obj ((pullback g).obj M) := (pullbackPushforwardAdjunction g).unit.app M

theorem preimage_Uj : hV.fromSpec ⁻¹ᵁ Uj hV = ⊤ := hV.fromSpec.preimage_image_eq ⊤

include h in
theorem top_le_fφ_preimage : ⊤ ≤ fφ g h ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ Uj hV) := by
  rw [preimage_Uj]
  exact le_of_eq rfl

include h in
theorem top_le_comp_preimage : ⊤ ≤ (fφ g h ≫ hV.fromSpec) ⁻¹ᵁ Uj hV := top_le_fφ_preimage g hV h

include h in
theorem top_le_comp_preimage' : ⊤ ≤ (hV'.fromSpec ≫ g) ⁻¹ᵁ Uj hV := fun x _ =>
  image_top_le_preimage g hV hV' h ⟨x, trivial, rfl⟩

theorem top_le_preimage_Uj' : ⊤ ≤ hV'.fromSpec ⁻¹ᵁ Uj' hV' := le_of_eq (hV'.fromSpec.preimage_image_eq ⊤).symm

include h in
theorem preimage_Uj'_le : hV'.fromSpec ⁻¹ᵁ Uj' hV' ≤ hV'.fromSpec ⁻¹ᵁ (g ⁻¹ᵁ Uj hV) :=
  fun _ hx => image_top_le_preimage g hV hV' h hx

/-- **The unit is compatible with open immersions (core computation)**: `Φ` sends the unit of
`(Spec φ)^*` to the unit of `g^*` followed by restriction. -/
theorem Φ_hom_app_top (m : Γ(M.restrict hV.fromSpec, ⊤)) :
    (Φ g M hV hV' h).hom.app ⊤
        (pullbackSectionsOn (fφ g h) (M.restrict hV.fromSpec) ⊤ ⊤ le_top m) =
      pullbackSectionsOn g M (Uj hV) (Uj' hV') (image_top_le_preimage g hV hV' h) m := by
  -- s0: unfold Φ
  have s0 : (Φ g M hV hV' h).hom.app ⊤ (pullbackSectionsOn (fφ g h) (M.restrict hV.fromSpec) ⊤ ⊤ le_top m) =
      (ρ' g M hV').inv.app ⊤ (((pullbackComp hV'.fromSpec g).app M).inv.app ⊤
        (((pullbackCongr (square g hV hV' h)).app M).hom.app ⊤
          (((pullbackComp (fφ g h) hV.fromSpec).app M).hom.app ⊤
            (((pullback (fφ g h)).map (ρ M hV).hom).app ⊤
              (((pullback (fφ g h)).obj (M.restrict hV.fromSpec)).presheaf.map (homOfLE le_top).op
                ((ηf g M hV h).app ⊤ m)))))) := rfl
  -- Step A: commute the restriction, naturality of the unit through ρ.hom
  have sA1 : ((pullback (fφ g h)).map (ρ M hV).hom).app ⊤
      (((pullback (fφ g h)).obj (M.restrict hV.fromSpec)).presheaf.map (homOfLE le_top).op
        ((ηf g M hV h).app ⊤ m)) =
      ((pullback (fφ g h)).obj ((pullback hV.fromSpec).obj M)).presheaf.map (homOfLE le_top).op
        (((pullback (fφ g h)).map (ρ M hV).hom).app (fφ g h ⁻¹ᵁ ⊤) ((ηf g M hV h).app ⊤ m)) :=
    app_map ((pullback (fφ g h)).map (ρ M hV).hom) (le_top : ⊤ ≤ fφ g h ⁻¹ᵁ ⊤) ((ηf g M hV h).app ⊤ m)
  have sA2 : ((pullback (fφ g h)).map (ρ M hV).hom).app (fφ g h ⁻¹ᵁ ⊤) ((ηf g M hV h).app ⊤ m) =
      (ηfj g M hV h).app ⊤ ((ρ M hV).hom.app ⊤ m) :=
    unit_naturality_app (fφ g h) (ρ M hV).hom ⊤ m
  -- Step B: ρ.hom on sections is unit-then-restrict
  have sB : (ρ M hV).hom.app ⊤ m =
      ((pullback hV.fromSpec).obj M).presheaf.map (homOfLE (le_of_eq (preimage_Uj hV).symm)).op
        ((ηj M hV).app (Uj hV) m) :=
    restrictFunctorIsoPullback_hom_app_apply hV.fromSpec M ⊤ m
  -- Step C: unit of f commutes with restriction
  have sC : (ηfj g M hV h).app ⊤
      (((pullback hV.fromSpec).obj M).presheaf.map (homOfLE (le_of_eq (preimage_Uj hV).symm)).op
        ((ηj M hV).app (Uj hV) m)) =
      ((pullback (fφ g h)).obj ((pullback hV.fromSpec).obj M)).presheaf.map
        (homOfLE (show fφ g h ⁻¹ᵁ ⊤ ≤ fφ g h ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ Uj hV) from
          fun _ hx => (le_of_eq (preimage_Uj hV).symm) hx)).op
        ((ηfj g M hV h).app (hV.fromSpec ⁻¹ᵁ Uj hV) ((ηj M hV).app (Uj hV) m)) :=
    unit_app_map (fφ g h) ((pullback hV.fromSpec).obj M) (le_of_eq (preimage_Uj hV).symm)
      ((ηj M hV).app (Uj hV) m)
  -- Step D: C.hom sends η^f(η^j m) to η^{f ≫ j} m
  have sD1 : ((pullbackComp (fφ g h) hV.fromSpec).app M).inv.app ((fφ g h ≫ hV.fromSpec) ⁻¹ᵁ Uj hV)
      ((ηfjc g M hV h).app (Uj hV) m) =
      (ηfj g M hV h).app (hV.fromSpec ⁻¹ᵁ Uj hV) ((ηj M hV).app (Uj hV) m) :=
    pullbackComp_inv_app_unit (fφ g h) hV.fromSpec M (Uj hV) m
  have sD2 : ((pullbackComp (fφ g h) hV.fromSpec).app M).hom.app (fφ g h ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ Uj hV))
      ((ηfj g M hV h).app (hV.fromSpec ⁻¹ᵁ Uj hV) ((ηj M hV).app (Uj hV) m)) =
      (ηfjc g M hV h).app (Uj hV) m := by
    rw [← sD1]
    exact modIso_hom_app_inv_app ((pullbackComp (fφ g h) hV.fromSpec).app M) _ _
  have sD3 : ((pullbackComp (fφ g h) hV.fromSpec).app M).hom.app ⊤
      (((pullback (fφ g h)).obj ((pullback hV.fromSpec).obj M)).presheaf.map
        (homOfLE (top_le_fφ_preimage g hV h)).op
        ((ηfj g M hV h).app (hV.fromSpec ⁻¹ᵁ Uj hV) ((ηj M hV).app (Uj hV) m))) =
      ((pullback (fφ g h ≫ hV.fromSpec)).obj M).presheaf.map (homOfLE (top_le_fφ_preimage g hV h)).op
        (((pullbackComp (fφ g h) hV.fromSpec).app M).hom.app (fφ g h ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ Uj hV))
          ((ηfj g M hV h).app (hV.fromSpec ⁻¹ᵁ Uj hV) ((ηj M hV).app (Uj hV) m))) :=
    app_map ((pullbackComp (fφ g h) hV.fromSpec).app M).hom (top_le_fφ_preimage g hV h) _
  -- Step E: transport along the square
  have sE : ((pullbackCongr (square g hV hV' h)).app M).hom.app ⊤
      (pullbackSectionsOn (fφ g h ≫ hV.fromSpec) M (Uj hV) ⊤ (top_le_comp_preimage g hV h) m) =
      pullbackSectionsOn (hV'.fromSpec ≫ g) M (Uj hV) ⊤ (top_le_comp_preimage' g hV hV' h) m :=
    pullbackCongr_hom_app_pullbackSectionsOn (square g hV hV' h) M (Uj hV) ⊤
      (top_le_comp_preimage g hV h) (top_le_comp_preimage' g hV hV' h) m
  -- Step F: C'.inv sends η^{j' ≫ g} m to η^{j'}(η^g m)
  have sF1 : ((pullbackComp hV'.fromSpec g).app M).inv.app ⊤
      (((pullback (hV'.fromSpec ≫ g)).obj M).presheaf.map (homOfLE (top_le_comp_preimage' g hV hV' h)).op
        ((ηjgc g M hV').app (Uj hV) m)) =
      ((pullback hV'.fromSpec).obj ((pullback g).obj M)).presheaf.map
        (homOfLE (top_le_comp_preimage' g hV hV' h)).op
        (((pullbackComp hV'.fromSpec g).app M).inv.app ((hV'.fromSpec ≫ g) ⁻¹ᵁ Uj hV)
          ((ηjgc g M hV').app (Uj hV) m)) :=
    app_map ((pullbackComp hV'.fromSpec g).app M).inv (top_le_comp_preimage' g hV hV' h) _
  have sF2 : ((pullbackComp hV'.fromSpec g).app M).inv.app ((hV'.fromSpec ≫ g) ⁻¹ᵁ Uj hV)
      ((ηjgc g M hV').app (Uj hV) m) =
      (ηj' g M hV').app (g ⁻¹ᵁ Uj hV) ((ηg g M).app (Uj hV) m) :=
    pullbackComp_inv_app_unit hV'.fromSpec g M (Uj hV) m
  -- Step G: unit of j' on U' then restrict
  have sG1 : (ηj' g M hV').app (Uj' hV')
      (((pullback g).obj M).presheaf.map (homOfLE (image_top_le_preimage g hV hV' h)).op
        ((ηg g M).app (Uj hV) m)) =
      ((pullback hV'.fromSpec).obj ((pullback g).obj M)).presheaf.map
        (homOfLE (preimage_Uj'_le g hV hV' h)).op
        ((ηj' g M hV').app (g ⁻¹ᵁ Uj hV) ((ηg g M).app (Uj hV) m)) :=
    unit_app_map hV'.fromSpec ((pullback g).obj M) (image_top_le_preimage g hV hV' h) _
  have sG2 : (ρ' g M hV').hom.app ⊤
      (((pullback g).obj M).presheaf.map (homOfLE (image_top_le_preimage g hV hV' h)).op
        ((ηg g M).app (Uj hV) m)) =
      ((pullback hV'.fromSpec).obj ((pullback g).obj M)).presheaf.map
        (homOfLE (top_le_preimage_Uj' hV')).op
        ((ηj' g M hV').app (Uj' hV')
          (((pullback g).obj M).presheaf.map (homOfLE (image_top_le_preimage g hV hV' h)).op
            ((ηg g M).app (Uj hV) m))) :=
    restrictFunctorIsoPullback_hom_app_apply hV'.fromSpec ((pullback g).obj M) ⊤ _
  -- Step H: ρ'.inv ∘ ρ'.hom = id
  have sH : (ρ' g M hV').inv.app ⊤ ((ρ' g M hV').hom.app ⊤
      (((pullback g).obj M).presheaf.map (homOfLE (image_top_le_preimage g hV hV' h)).op
        ((ηg g M).app (Uj hV) m))) =
      ((pullback g).obj M).presheaf.map (homOfLE (image_top_le_preimage g hV hV' h)).op
        ((ηg g M).app (Uj hV) m) :=
    modIso_inv_app_hom_app (ρ' g M hV') ⊤ _
  -- assemble
  rw [s0]
  have t1 : ((pullback (fφ g h)).map (ρ M hV).hom).app ⊤
      (((pullback (fφ g h)).obj (M.restrict hV.fromSpec)).presheaf.map (homOfLE le_top).op
        ((ηf g M hV h).app ⊤ m)) =
      ((pullback (fφ g h)).obj ((pullback hV.fromSpec).obj M)).presheaf.map
        (homOfLE (top_le_fφ_preimage g hV h)).op
        ((ηfj g M hV h).app (hV.fromSpec ⁻¹ᵁ Uj hV) ((ηj M hV).app (Uj hV) m)) := by
    rw [sA1, sA2, sB, sC]
    exact famRes_comp' _ _ _ _
  rw [t1]
  have t2 : ((pullbackComp (fφ g h) hV.fromSpec).app M).hom.app ⊤
      (((pullback (fφ g h)).obj ((pullback hV.fromSpec).obj M)).presheaf.map
        (homOfLE (top_le_fφ_preimage g hV h)).op
        ((ηfj g M hV h).app (hV.fromSpec ⁻¹ᵁ Uj hV) ((ηj M hV).app (Uj hV) m))) =
      pullbackSectionsOn (fφ g h ≫ hV.fromSpec) M (Uj hV) ⊤ (top_le_comp_preimage g hV h) m := by
    rw [sD3, sD2]
    rfl
  rw [t2, sE]
  have t3 : ((pullbackComp hV'.fromSpec g).app M).inv.app ⊤
      (pullbackSectionsOn (hV'.fromSpec ≫ g) M (Uj hV) ⊤ (top_le_comp_preimage' g hV hV' h) m) =
      (ρ' g M hV').hom.app ⊤
        (((pullback g).obj M).presheaf.map (homOfLE (image_top_le_preimage g hV hV' h)).op
          ((ηg g M).app (Uj hV) m)) := by
    have u0 : pullbackSectionsOn (hV'.fromSpec ≫ g) M (Uj hV) ⊤ (top_le_comp_preimage' g hV hV' h) m =
        ((pullback (hV'.fromSpec ≫ g)).obj M).presheaf.map
          (homOfLE (top_le_comp_preimage' g hV hV' h)).op ((ηjgc g M hV').app (Uj hV) m) := rfl
    rw [u0, sF1, sF2, sG2]
    have u2 := congrArg (fun y => ((pullback hV'.fromSpec).obj ((pullback g).obj M)).presheaf.map
      (homOfLE (top_le_preimage_Uj' hV')).op y) sG1
    have u3 := famRes_comp' ((pullback hV'.fromSpec).obj ((pullback g).obj M))
      (preimage_Uj'_le g hV hV' h) (top_le_preimage_Uj' hV')
      ((ηj' g M hV').app (g ⁻¹ᵁ Uj hV) ((ηg g M).app (Uj hV) m))
    exact (u2.trans u3).symm
  rw [t3, sH]
  rfl

/-- The module isomorphism on the target side, `Γ((Spec φ)^*N, ⊤) ≅ Γ(g^*M, V')`. -/
def eN : ModuleCat.of Γ(Y, V') Γ((pullback (Spec.map (g.appLE V V' h))).obj (M.restrict hV.fromSpec), ⊤) ≅
    ModuleCat.of Γ(Y, V') Γ((pullback g).obj M, V') :=
  moduleSpecΓFunctor.mapIso (Φ g M hV hV' h) ≪≫ restrictTopIso hV' ((pullback g).obj M)

theorem hcomm :
    (restrictTopIso hV M).hom ≫ pullbackSectionsNative g M V V' h =
      SpecBaseChange.α' (g.appLE V V' h) (M.restrict hV.fromSpec) ≫
        (ModuleCat.restrictScalars (g.appLE V V' h).hom).map (eN g M hV hV' h).hom := by
  ext m
  have e1 : ((restrictTopIso hV M).hom ≫ pullbackSectionsNative g M V V' h) m =
      pullbackSectionsOn g M V V' h (M.presheaf.map (homOfLE (le_image_top hV)).op m) := rfl
  have e2 : (SpecBaseChange.α' (g.appLE V V' h) (M.restrict hV.fromSpec) ≫
      (ModuleCat.restrictScalars (g.appLE V V' h).hom).map (eN g M hV hV' h).hom) m =
      ((pullback g).obj M).presheaf.map (homOfLE (le_image_top hV')).op
        ((Φ g M hV hV' h).hom.app ⊤
          (pullbackSectionsOn (Spec.map (g.appLE V V' h)) (M.restrict hV.fromSpec) ⊤ ⊤ le_top m)) := rfl
  have e3 := congrArg (fun y => ((pullback g).obj M).presheaf.map (homOfLE (le_image_top hV')).op y)
    (Φ_hom_app_top g M hV hV' h m)
  have e4 := pullbackSectionsOn_restrict g M (image_top_le_preimage g hV hV' h) h (le_image_top hV)
    (le_image_top hV') m
  exact e1.trans (e4.symm.trans (e3.symm.trans e2.symm))

end Main

end NativeBaseChangeAux

open NativeBaseChangeAux in
/-- **Stacks 01I9, open-set version.** For any morphism `g : Y → X`, affine opens `V ⊆ X`,
`V' ⊆ g⁻¹V`, and `M` quasi-coherent, the pullback of sections `Γ(M, V) → Γ(g^*M, V')` is the base
change along `Γ(X, V) → Γ(Y, V')`: the transpose `Γ(Y, V') ⊗_{Γ(X,V)} Γ(M, V) → Γ(g^*M, V')`,
`t ⊗ s ↦ t · (g^*s)|_{V'}`, is an isomorphism.

Proof: see the module docstring. The Spec case is `SpecBaseChange.bijective_transpose`, transported
along `hV.fromSpec`, `hV'.fromSpec` (`Φ`, `Φ_hom_app_top`, `restrictTopIso`, `hcomm`), and
`isIso_transpose_of_iso` concludes.
References: Stacks 01I9 (schemes-lemma-widetilde-pullback); Hartshorne II.5.2(e).

Edge cases: for `V' = ∅` both sides are zero; likewise for `M = 0`. -/
theorem isIso_transpose_pullbackSectionsNative (M : X.Modules) [M.IsQuasicoherent] (V : X.Opens)
    (hV : AlgebraicGeometry.IsAffineOpen V) (V' : Y.Opens)
    (hV' : AlgebraicGeometry.IsAffineOpen V') (h : V' ≤ g ⁻¹ᵁ V) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj (g.appLE V V' h).hom).homEquiv _ _).symm
      (pullbackSectionsNative g M V V' h)) :=
  isIso_transpose_of_iso (g.appLE V V' h).hom
    (SpecBaseChange.α' (g.appLE V V' h) (M.restrict hV.fromSpec)) (pullbackSectionsNative g M V V' h)
    (restrictTopIso hV M) (eN g M hV hV' h) (hcomm g M hV hV' h)
    (SpecBaseChange.bijective_transpose (g.appLE V V' h) (M.restrict hV.fromSpec))

/-- The open-set version of Stacks 01I9 as a bare existence statement (`Nonempty (≃ₗ)`), a weaker
form of `isIso_transpose_pullbackSectionsNative` from which it is deduced. -/
theorem pullback_app_affine {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] (U : Y.affineOpens) (W : X.affineOpens)
    (e : W.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(Y, U.1) Γ(X, W.1) := (f.appLE U.1 W.1 e).hom.toAlgebra
    Nonempty (Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, W.1)
      ≃ₗ[Γ(X, W.1)] TensorProduct Γ(Y, U.1) Γ(X, W.1) Γ(M, U.1)) := by
  haveI := isIso_transpose_pullbackSectionsNative f M U.1 U.2 W.1 W.2 e
  exact ⟨(CategoryTheory.asIso
    (((ModuleCat.extendRestrictScalarsAdj (f.appLE U.1 W.1 e).hom).homEquiv _ _).symm
      (pullbackSectionsNative f M U.1 W.1 e))).toLinearEquiv.symm⟩

end AlgebraicGeometry.Scheme.Modules

end
