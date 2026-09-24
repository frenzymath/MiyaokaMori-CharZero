import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrames
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SchemeModulesPullbackFreeIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnit

/-! # The pullback of a frame is a frame

For `f : X ⟶ Y`, `F : Y.Modules` and a finite frame `e : I → Γ(F, V)` of `F` on `V ⊆ Y`
(`IsFrameOn`, helper 1), the sections `unit(eᵢ) ∈ Γ(f^*F, f⁻¹V)` (image of `eᵢ` under the
adjunction unit `F ⟶ f_*f^*F`) form a frame of `f^*F` on `f⁻¹V` (`isFrameOn_pullback`).

Proof. Write `j : V → Y`, `j' : f⁻¹V → X` for the open immersions and `g := f ∣_ V`. The frame `e`
gives an isomorphism `frameHom e : O_V^{(I)} ≅ F|_V`; pulling back along `g` and composing with
`pullbackObjFreeIso g I : g^*O_V^{(I)} ≅ O^{(I)}` and the base change isomorphism
`pullbackRestrictIso f F V : (f^*F)|_{f⁻¹V} ≅ g^*(F|_V)` (`PullbackUnit.lean`) gives an isomorphism
`O_{f⁻¹V}^{(I)} ≅ (f^*F)|_{f⁻¹V}`. It remains to identify the images of the standard sections
with `unit(eᵢ)`; this is the compatibility of the five isomorphisms making up `pullbackRestrictIso`
with the adjunction units (`restrictFunctorIsoPullback` via `unit_leftAdjointUniq_hom_app`,
`pullbackComp` via `conjugateEquiv_pullbackComp_inv` and `unit_conjugateEquiv_symm`,
`pullbackCongr` by `subst`), together with `pullback_map_ιFree_comp_pullbackObjFreeIso_hom`.

Source: Stacks 01C6/01CR (pullback of a locally free module; base change along an open).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.DualPullback

open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

section PbSec

variable {X' Y' : Scheme.{u}} (p : X' ⟶ Y') (N : Y'.Modules)

/-- The section `unit(m) ∈ Γ(p^*N, p⁻¹Z)` of the adjunction unit, for `m ∈ Γ(N, Z)`. -/
def unitSec {Z : Y'.Opens} (m : Γ(N, Z)) : Γ((Scheme.Modules.pullback p).obj N, p ⁻¹ᵁ Z) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N).app Z m

/-- The section `unit(m)|_{W₁}` of `p^*N`, for `m ∈ Γ(N, Z)` and `W₁ ≤ p⁻¹Z`. -/
def pbSec {Z : Y'.Opens} (m : Γ(N, Z)) {W₁ : X'.Opens} (h : W₁ ≤ p ⁻¹ᵁ Z) :
    Γ((Scheme.Modules.pullback p).obj N, W₁) :=
  res ((Scheme.Modules.pullback p).obj N) h (unitSec p N m)

lemma pbSec_res {Z : Y'.Opens} (m : Γ(N, Z)) {W₁ W₂ : X'.Opens} (h : W₁ ≤ p ⁻¹ᵁ Z) (h₂ : W₂ ≤ W₁) :
    res ((Scheme.Modules.pullback p).obj N) h₂ (pbSec p N m h) = pbSec p N m (h₂.trans h) := by
  unfold pbSec
  rw [res_res]

lemma pbSec_self {Z : Y'.Opens} (m : Γ(N, Z)) (h : p ⁻¹ᵁ Z ≤ p ⁻¹ᵁ Z) :
    pbSec p N m h = unitSec p N m := by
  unfold pbSec
  rw [res_self]

/-- The adjunction unit commutes with restriction. -/
lemma unitSec_res {Z' Z : Y'.Opens} (hZ : Z' ≤ Z) (m : Γ(N, Z)) :
    unitSec p N (res N hZ m) =
      res ((Scheme.Modules.pullback p).obj N) ((Opens.map p.base).map (homOfLE hZ)).le
        (unitSec p N m) :=
  PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N).val (homOfLE hZ).op m

lemma pbSec_res_left {Z' Z : Y'.Opens} (hZ : Z' ≤ Z) (m : Γ(N, Z)) {W₁ : X'.Opens}
    (h' : W₁ ≤ p ⁻¹ᵁ Z') :
    pbSec p N (res N hZ m) h' = pbSec p N m (h'.trans ((Opens.map p.base).map (homOfLE hZ)).le) := by
  unfold pbSec
  rw [unitSec_res, res_res]

/-- Naturality of the unit sections in the module. -/
lemma unitSec_map {N' : Y'.Modules} (φ : N ⟶ N') {Z : Y'.Opens} (m : Γ(N, Z)) :
    ((Scheme.Modules.pullback p).map φ).app (p ⁻¹ᵁ Z) (unitSec p N m) = unitSec p N' (φ.app Z m) := by
  have h2 := congrArg (fun k => k.app Z m)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality φ)
  exact h2.symm

/-- Naturality of `pbSec` in the module. -/
lemma pbSec_map {N' : Y'.Modules} (φ : N ⟶ N') {Z : Y'.Opens} (m : Γ(N, Z)) {W₁ : X'.Opens}
    (h : W₁ ≤ p ⁻¹ᵁ Z) :
    ((Scheme.Modules.pullback p).map φ).app W₁ (pbSec p N m h) = pbSec p N' (φ.app Z m) h := by
  unfold pbSec
  have h1 := PresheafOfModules.naturality_apply ((Scheme.Modules.pullback p).map φ).val
    (homOfLE h).op (unitSec p N m)
  change ((Scheme.Modules.pullback p).map φ).app W₁ (res ((Scheme.Modules.pullback p).obj N) h _) =
    res ((Scheme.Modules.pullback p).obj N') h
      (((Scheme.Modules.pullback p).map φ).app (p ⁻¹ᵁ Z) (unitSec p N m)) at h1
  rw [h1, unitSec_map]

end PbSec

section Restrict

variable {X' X : Scheme.{u}} (p : X' ⟶ X) [IsOpenImmersion p] (M : X.Modules)

lemma le_preimage_of_image_le {W₁ : X'.Opens} {Z : X.Opens} (hW : p ''ᵁ W₁ ≤ Z) : W₁ ≤ p ⁻¹ᵁ Z :=
  fun x hx => hW ⟨x, hx, rfl⟩

/-- `restrictFunctorIsoPullback` is compatible with the adjunction unit: on `p⁻¹Z`. -/
lemma restrictFunctorIsoPullback_hom_app_unit {Z : X.Opens} (m : Γ(M, Z)) :
    ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M).app (p ⁻¹ᵁ Z)
        (res M (p.image_preimage_le Z) m : Γ(M.restrict p, p ⁻¹ᵁ Z)) =
      unitSec p M m := by
  have h1 := congrArg (fun k => k.app Z m)
    (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction p)
      (Scheme.Modules.pullbackPushforwardAdjunction p) M)
  exact h1

/-- `restrictFunctorIsoPullback` is compatible with the adjunction unit: on `W₁` with
`p ''ᵁ W₁ ≤ Z`. -/
lemma restrictFunctorIsoPullback_hom_app_res {W₁ : X'.Opens} {Z : X.Opens} (hW : p ''ᵁ W₁ ≤ Z)
    (m : Γ(M, Z)) :
    ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M).app W₁
        (res M hW m : Γ(M.restrict p, W₁)) =
      pbSec p M m (le_preimage_of_image_le p hW) := by
  have h2 := PresheafOfModules.naturality_apply
    ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M).val
    (homOfLE (le_preimage_of_image_le p hW)).op
    (res M (p.image_preimage_le Z) m : Γ(M.restrict p, p ⁻¹ᵁ Z))
  change ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M).app W₁
      (res M (p.image_mono (le_preimage_of_image_le p hW)) (res M (p.image_preimage_le Z) m) :
        Γ(M.restrict p, W₁)) =
    res ((Scheme.Modules.pullback p).obj M) (le_preimage_of_image_le p hW)
      (((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M).app (p ⁻¹ᵁ Z)
        (res M (p.image_preimage_le Z) m : Γ(M.restrict p, p ⁻¹ᵁ Z))) at h2
  rw [res_res, restrictFunctorIsoPullback_hom_app_unit] at h2
  exact h2

lemma restrictFunctorIsoPullback_inv_app_unit {Z : X.Opens} (m : Γ(M, Z)) :
    ((Scheme.Modules.restrictFunctorIsoPullback p).inv.app M).app (p ⁻¹ᵁ Z) (unitSec p M m) =
      (res M (p.image_preimage_le Z) m : Γ(M.restrict p, p ⁻¹ᵁ Z)) := by
  rw [← restrictFunctorIsoPullback_hom_app_unit p M m]
  change ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M ≫
    (Scheme.Modules.restrictFunctorIsoPullback p).inv.app M).app (p ⁻¹ᵁ Z) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

end Restrict

section Comp

variable {X' X Y : Scheme.{u}} (p : X' ⟶ X) (q : X ⟶ Y) (N : Y.Modules)

/-- `pullbackComp` is compatible with the adjunction units. -/
lemma pullbackComp_hom_app_unit {Z : Y.Opens} (m : Γ(N, Z)) :
    ((Scheme.Modules.pullbackComp p q).hom.app N).app (p ⁻¹ᵁ (q ⁻¹ᵁ Z))
        (unitSec p ((Scheme.Modules.pullback q).obj N) (unitSec q N m)) =
      unitSec (p ≫ q) N m := by
  have hconj : (Scheme.Modules.pullbackComp p q).inv =
      (conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction q).comp
        (Scheme.Modules.pullbackPushforwardAdjunction p))
        (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q))).symm
        (Scheme.Modules.pushforwardComp p q).hom := by
    rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv p q, Equiv.symm_apply_apply]
  have h1 := unit_conjugateEquiv_symm
    ((Scheme.Modules.pullbackPushforwardAdjunction q).comp
      (Scheme.Modules.pullbackPushforwardAdjunction p))
    (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q))
    (Scheme.Modules.pushforwardComp p q).hom N
  rw [← hconj] at h1
  have h2 := congrArg (fun k => k.app Z m) h1
  simp only [Scheme.Modules.Hom.comp_app] at h2
  change ((Scheme.Modules.pushforwardComp p q).hom.app
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N))).app Z
      ((((Scheme.Modules.pullbackPushforwardAdjunction q).comp
        (Scheme.Modules.pullbackPushforwardAdjunction p)).unit.app N).app Z m) =
    ((Scheme.Modules.pullbackComp p q).inv.app N).app (p ⁻¹ᵁ (q ⁻¹ᵁ Z)) (unitSec (p ≫ q) N m) at h2
  rw [Scheme.Modules.pushforwardComp_hom_app_app, Adjunction.comp_unit_app] at h2
  change unitSec p ((Scheme.Modules.pullback q).obj N) (unitSec q N m) =
    ((Scheme.Modules.pullbackComp p q).inv.app N).app (p ⁻¹ᵁ (q ⁻¹ᵁ Z)) (unitSec (p ≫ q) N m) at h2
  rw [h2]
  change ((Scheme.Modules.pullbackComp p q).inv.app N ≫
    (Scheme.Modules.pullbackComp p q).hom.app N).app (p ⁻¹ᵁ (q ⁻¹ᵁ Z)) _ = _
  rw [Iso.inv_hom_id_app]
  rfl

lemma pullbackComp_inv_app_unit {Z : Y.Opens} (m : Γ(N, Z)) :
    ((Scheme.Modules.pullbackComp p q).inv.app N).app (p ⁻¹ᵁ (q ⁻¹ᵁ Z)) (unitSec (p ≫ q) N m) =
      unitSec p ((Scheme.Modules.pullback q).obj N) (unitSec q N m) := by
  rw [← pullbackComp_hom_app_unit p q N m]
  change ((Scheme.Modules.pullbackComp p q).hom.app N ≫
    (Scheme.Modules.pullbackComp p q).inv.app N).app (p ⁻¹ᵁ (q ⁻¹ᵁ Z)) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

/-- `pullbackComp_inv_app_unit`, stated with the open `(p ≫ q) ⁻¹ᵁ Z`. -/
lemma pullbackComp_inv_app_unit' {Z : Y.Opens} (m : Γ(N, Z)) :
    ((Scheme.Modules.pullbackComp p q).inv.app N).app ((p ≫ q) ⁻¹ᵁ Z) (unitSec (p ≫ q) N m) =
      unitSec p ((Scheme.Modules.pullback q).obj N) (unitSec q N m) :=
  pullbackComp_inv_app_unit p q N m

end Comp

section Congr

variable {X' Y : Scheme.{u}}

/-- `pullbackCongr` is compatible with `pbSec`. -/
lemma pullbackCongr_hom_app_pbSec {p p' : X' ⟶ Y} (hp : p = p') (N : Y.Modules) {Z : Y.Opens}
    (m : Γ(N, Z)) {W₁ : X'.Opens} (h : W₁ ≤ p ⁻¹ᵁ Z) (h' : W₁ ≤ p' ⁻¹ᵁ Z) :
    ((Scheme.Modules.pullbackCongr hp).hom.app N).app W₁ (pbSec p N m h) = pbSec p' N m h' := by
  subst hp
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Scheme.Modules.Hom.id_app]
  rfl

end Congr

section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) (V : Y.Opens)

lemma le_restrict_preimage {W₁ : (f ⁻¹ᵁ V).toScheme.Opens} {Z : Y.Opens}
    (h1 : (f ⁻¹ᵁ V).ι ''ᵁ W₁ ≤ f ⁻¹ᵁ Z) : W₁ ≤ (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ Z) := by
  have h2 : W₁ ≤ ((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ Z := le_preimage_of_image_le (f ⁻¹ᵁ V).ι h1
  rw [← morphismRestrict_ι] at h2
  exact h2

/-- Restriction of `pbSec` for a composite pullback, through naturality of a morphism of the
pulled-back sheaves. -/
lemma app_pbSec_of_app_unitSec {X' Y' : Scheme.{u}} (p : X' ⟶ Y') {N : Y'.Modules}
    {P : X'.Modules} (α : (Scheme.Modules.pullback p).obj N ⟶ P) {Z : Y'.Opens} (m : Γ(N, Z))
    {W₁ : X'.Opens} (h : W₁ ≤ p ⁻¹ᵁ Z) :
    α.app W₁ (pbSec p N m h) = res P h (α.app (p ⁻¹ᵁ Z) (unitSec p N m)) := by
  unfold pbSec
  exact PresheafOfModules.naturality_apply α.val (homOfLE h).op (unitSec p N m)

/-- The base change isomorphism `pullbackRestrictIso` is compatible with the adjunction units. -/
lemma pullbackRestrictIso_hom_app_pbSec {W₁ : (f ⁻¹ᵁ V).toScheme.Opens} {Z : Y.Opens}
    (m : Γ(F, Z)) (h1 : (f ⁻¹ᵁ V).ι ''ᵁ W₁ ≤ f ⁻¹ᵁ Z) :
    (Scheme.Modules.pullbackRestrictIso f F V).hom.app W₁
        (pbSec f F m h1 : Γ(((Scheme.Modules.pullback f).obj F).restrict (f ⁻¹ᵁ V).ι, W₁)) =
      pbSec (f ∣_ V) (F.restrict V.ι)
        (res F (V.ι.image_preimage_le Z) m : Γ(F.restrict V.ι, V.ι ⁻¹ᵁ Z))
        (le_restrict_preimage f V h1) := by
  simp only [Scheme.Modules.pullbackRestrictIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Scheme.Modules.Hom.comp_app]
  change ((Scheme.Modules.pullback (f ∣_ V)).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app F)).app W₁
    (((Scheme.Modules.pullbackComp (f ∣_ V) V.ι).inv.app F).app W₁
      (((Scheme.Modules.pullbackCongr (morphismRestrict_ι f V).symm).hom.app F).app W₁
        (((Scheme.Modules.pullbackComp (f ⁻¹ᵁ V).ι f).hom.app F).app W₁
          (((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).hom.app
            ((Scheme.Modules.pullback f).obj F)).app W₁
              (pbSec f F m h1 : Γ(((Scheme.Modules.pullback f).obj F).restrict (f ⁻¹ᵁ V).ι, W₁)))))) = _
  -- step 1: restrictFunctorIsoPullback
  have s1 : ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).hom.app
      ((Scheme.Modules.pullback f).obj F)).app W₁
        (pbSec f F m h1 : Γ(((Scheme.Modules.pullback f).obj F).restrict (f ⁻¹ᵁ V).ι, W₁)) =
      pbSec (f ⁻¹ᵁ V).ι ((Scheme.Modules.pullback f).obj F) (unitSec f F m)
        (le_preimage_of_image_le (f ⁻¹ᵁ V).ι h1) :=
    restrictFunctorIsoPullback_hom_app_res (f ⁻¹ᵁ V).ι ((Scheme.Modules.pullback f).obj F) h1 _
  rw [s1]
  -- step 2: pullbackComp
  have h1' : W₁ ≤ ((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ Z := le_preimage_of_image_le (f ⁻¹ᵁ V).ι h1
  have h2' : W₁ ≤ (f ∣_ V ≫ V.ι) ⁻¹ᵁ Z := le_restrict_preimage f V h1
  rw [app_pbSec_of_app_unitSec (f ⁻¹ᵁ V).ι ((Scheme.Modules.pullbackComp (f ⁻¹ᵁ V).ι f).hom.app F),
    pullbackComp_hom_app_unit]
  change ((Scheme.Modules.pullback (f ∣_ V)).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app F)).app W₁
    (((Scheme.Modules.pullbackComp (f ∣_ V) V.ι).inv.app F).app W₁
      (((Scheme.Modules.pullbackCongr (morphismRestrict_ι f V).symm).hom.app F).app W₁
        (pbSec ((f ⁻¹ᵁ V).ι ≫ f) F m h1'))) = _
  -- step 3: pullbackCongr
  rw [pullbackCongr_hom_app_pbSec (morphismRestrict_ι f V).symm F m h1' h2']
  -- step 4: pullbackComp inverse
  rw [app_pbSec_of_app_unitSec (f ∣_ V ≫ V.ι) ((Scheme.Modules.pullbackComp (f ∣_ V) V.ι).inv.app F),
    pullbackComp_inv_app_unit']
  -- step 5: pullback of restrictFunctorIsoPullback inverse
  change ((Scheme.Modules.pullback (f ∣_ V)).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app F)).app W₁
    (pbSec (f ∣_ V) ((Scheme.Modules.pullback V.ι).obj F) (unitSec V.ι F m)
      (le_restrict_preimage f V h1)) = _
  rw [pbSec_map, restrictFunctorIsoPullback_inv_app_unit]
  rfl

end BaseChange

section Frame

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) (V : Y.Opens)

/-- The pulled-back frame vectors `unit(eᵢ) ∈ Γ(f^*F, f⁻¹V)`. -/
def unitFrame' {I : Type u} (e : I → Γ(F, V)) (i : I) : Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V (e i)

lemma le_preimage_top {X' Y' : Scheme.{u}} (p : X' ⟶ Y') (W₁ : X'.Opens) : W₁ ≤ p ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

open MiyaokaMori.FreeStalk

/-- `pullbackUnitIso`, with the canonical types of the unit modules. -/
def unitIso {X' Y' : Scheme.{u}} (p : X' ⟶ Y') :
    (Scheme.Modules.pullback p).obj (Scheme.Modules.unitModule Y') ≅ Scheme.Modules.unitModule X' :=
  Scheme.Modules.pullbackUnitIso p

/-- `pullbackObjFreeIso`, with the canonical types of the free modules. -/
def freeIso {X' Y' : Scheme.{u}} (p : X' ⟶ Y') (I : Type u) :
    (Scheme.Modules.pullback p).obj (freeM Y' I) ≅ freeM X' I :=
  Scheme.Modules.pullbackObjFreeIso p I

/-- The section `1` of `p^*O_{Y'}` corresponds, under `unitIso`, to the section `1`. -/
lemma unitIso_inv_app_one {X' Y' : Scheme.{u}} (p : X' ⟶ Y') (W₁ : X'.Opens) :
    (unitIso p).inv.app W₁ (uSec W₁ 1) = pbSec p (Scheme.Modules.unitModule Y') (uSec ⊤ 1) (le_preimage_top p W₁) := by
  haveI : (SheafOfModules.pushforward.{u} p.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).isRightAdjoint
  have hiso : IsIso ((unitIso p).hom.app W₁) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp (Iso.isIso_hom _) W₁
  have hu : Function.Injective ((unitIso p).hom.app W₁) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp hiso).1
  apply hu
  have h1 : (unitIso p).hom.app W₁ ((unitIso p).inv.app W₁ (uSec W₁ 1)) = uSec W₁ 1 := by
    have := congrArg (fun k => k.app W₁ (uSec W₁ 1)) (Iso.inv_hom_id (unitIso p))
    exact this
  rw [h1, app_pbSec_of_app_unitSec p (unitIso p).hom]
  have h3 : (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (Scheme.Modules.unitModule Y') ≫
        (Scheme.Modules.pushforward p).map (unitIso p).hom =
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom := by
    have := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      p.toRingCatSheafHom
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have h4 : (unitIso p).hom.app (p ⁻¹ᵁ ⊤) (unitSec p (Scheme.Modules.unitModule Y') (uSec ⊤ 1)) =
      uSec (p ⁻¹ᵁ ⊤) (p.app ⊤ 1) := by
    have := congrArg (fun k => k.app ⊤ (uSec ⊤ 1)) h3
    exact this
  rw [h4]
  change (1 : Γ(X', W₁)) = X'.presheaf.map (homOfLE (le_preimage_top p W₁)).op (p.app ⊤ (1 : Γ(Y', ⊤)))
  rw [map_one, map_one]

/-- `unitIso` and `freeIso` are compatible with the standard inclusions. -/
lemma unitIso_inv_comp_map_inc {X' Y' : Scheme.{u}} (p : X' ⟶ Y') (I : Type u) (i : I) :
    (unitIso p).inv ≫ (Scheme.Modules.pullback p).map (inc Y' I i) =
      inc X' I i ≫ (freeIso p I).inv := by
  haveI : (SheafOfModules.pushforward.{u} p.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).isRightAdjoint
  have h : (Scheme.Modules.pullback p).map (inc Y' I i) ≫ (freeIso p I).hom =
      (unitIso p).hom ≫ inc X' I i :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom p.toRingCatSheafHom (I := I) i
  have h' : (Scheme.Modules.pullback p).map (inc Y' I i) =
      ((unitIso p).hom ≫ inc X' I i) ≫ (freeIso p I).inv := (Iso.eq_comp_inv _).mpr h
  exact (Iso.inv_comp_eq _).mpr (h'.trans (Category.assoc _ _ _))

variable {I : Type u} [Fintype I] {e : I → Γ(F, V)}

/-- The pullback of a frame is a frame. -/
theorem isFrameOn_pullback (he : IsFrameOn F e) :
    IsFrameOn ((Scheme.Modules.pullback f).obj F) (unitFrame' f F V e) := by
  have hb : IsIso (frameHom F V e) := isIso_frameHom_of_isFrameOn F V e he
  let b' : freeM (f ⁻¹ᵁ V).toScheme I ⟶ ((Scheme.Modules.pullback f).obj F).restrict (f ⁻¹ᵁ V).ι :=
    (freeIso (f ∣_ V) I).inv ≫ (Scheme.Modules.pullback (f ∣_ V)).map (frameHom F V e) ≫
      (Scheme.Modules.pullbackRestrictIso f F V).inv
  have hb' : IsIso b' := by
    haveI : IsIso ((Scheme.Modules.pullback (f ∣_ V)).map (frameHom F V e)) := Functor.map_isIso _ _
    exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' inferInstance (Iso.isIso_inv _))
  have key : frameHom ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) (unitFrame' f F V e) = b' := by
    apply (((Scheme.Modules.pullback f).obj F).restrict (f ⁻¹ᵁ V).ι).freeHomEquiv.injective
    rw [freeHomEquiv_frameHom]
    funext i
    apply PresheafOfModules.sections_ext
    rintro ⟨W₁⟩
    rw [frameSection_val]
    change pbSec f F (e i) ((f ⁻¹ᵁ V).ι_image_le W₁) = b'.app W₁ (MiyaokaMori.FreeStalk.e I i W₁)
    have hcomp : inc (f ⁻¹ᵁ V).toScheme I i ≫ b' =
        (unitIso (f ∣_ V)).inv ≫ (Scheme.Modules.pullback (f ∣_ V)).map (inc V.toScheme I i) ≫
          (Scheme.Modules.pullback (f ∣_ V)).map (frameHom F V e) ≫
            (Scheme.Modules.pullbackRestrictIso f F V).inv := by
      calc inc (f ⁻¹ᵁ V).toScheme I i ≫ b'
          = (inc (f ⁻¹ᵁ V).toScheme I i ≫ (freeIso (f ∣_ V) I).inv) ≫
              ((Scheme.Modules.pullback (f ∣_ V)).map (frameHom F V e) ≫
                (Scheme.Modules.pullbackRestrictIso f F V).inv) := by
            simp only [b', Category.assoc]
        _ = ((unitIso (f ∣_ V)).inv ≫ (Scheme.Modules.pullback (f ∣_ V)).map (inc V.toScheme I i)) ≫
              ((Scheme.Modules.pullback (f ∣_ V)).map (frameHom F V e) ≫
                (Scheme.Modules.pullbackRestrictIso f F V).inv) :=
            congrArg (fun k => k ≫ _) (unitIso_inv_comp_map_inc (f ∣_ V) I i).symm
        _ = _ := by simp only [Category.assoc]
    have hb'e : b'.app W₁ (MiyaokaMori.FreeStalk.e I i W₁) =
        (Scheme.Modules.pullbackRestrictIso f F V).inv.app W₁
          (((Scheme.Modules.pullback (f ∣_ V)).map (frameHom F V e)).app W₁
            (((Scheme.Modules.pullback (f ∣_ V)).map (inc V.toScheme I i)).app W₁
              ((unitIso (f ∣_ V)).inv.app W₁ (uSec W₁ 1)))) := by
      rw [e_eq]
      exact congrArg (fun k => k.app W₁ (uSec W₁ 1)) hcomp
    rw [hb'e, unitIso_inv_app_one (f ∣_ V) W₁, pbSec_map, pbSec_map]
    -- identify the section of `F.restrict V.ι`
    have hs : (frameHom F V e).app ⊤ ((inc V.toScheme I i).app ⊤ (uSec ⊤ 1)) =
        (res F (V.ι_image_le ⊤) (e i) : Γ(F.restrict V.ι, ⊤)) := by
      rw [← e_eq]
      exact frameHom_app_e F V e ⊤ i
    rw [hs]
    -- compare with `pullbackRestrictIso_hom_app_pbSec`
    have hc := pullbackRestrictIso_hom_app_pbSec f F V (e i) ((f ⁻¹ᵁ V).ι_image_le W₁)
    have hres : (res F (V.ι.image_preimage_le V) (e i) : Γ(F.restrict V.ι, V.ι ⁻¹ᵁ V)) =
        res (F.restrict V.ι) (le_top : V.ι ⁻¹ᵁ V ≤ ⊤)
          (res F (V.ι_image_le ⊤) (e i) : Γ(F.restrict V.ι, ⊤)) := by
      change res F _ (e i) = res F (V.ι.image_mono le_top) (res F (V.ι_image_le ⊤) (e i))
      rw [res_res]
    have hres' : pbSec (f ∣_ V) (F.restrict V.ι)
        (res F (V.ι.image_preimage_le V) (e i) : Γ(F.restrict V.ι, V.ι ⁻¹ᵁ V))
        (le_restrict_preimage f V ((f ⁻¹ᵁ V).ι_image_le W₁)) =
        pbSec (f ∣_ V) (F.restrict V.ι) (res F (V.ι_image_le ⊤) (e i) : Γ(F.restrict V.ι, ⊤))
          (le_preimage_top (f ∣_ V) W₁) :=
      (congrArg (fun y => pbSec (f ∣_ V) (F.restrict V.ι) y
        (le_restrict_preimage f V ((f ⁻¹ᵁ V).ι_image_le W₁))) hres).trans
        (pbSec_res_left (f ∣_ V) (F.restrict V.ι) le_top _ _)
    have hc2 := hc.trans hres'
    rw [← hc2]
    change _ = ((Scheme.Modules.pullbackRestrictIso f F V).hom.app W₁ ≫
      (Scheme.Modules.pullbackRestrictIso f F V).inv.app W₁) (pbSec f F (e i) _)
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
    rfl
  have : IsIso (frameHom ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) (unitFrame' f F V e)) := by
    rw [key]; exact hb'
  exact isFrameOn_of_isIso_frameHom _ _ _

end Frame

end MiyaokaMori.DualPullback

end
