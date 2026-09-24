import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.FreeTransitionCompatible
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrames
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion

/-! # Frames of a trivialization cocycle give compatible block isomorphisms

The frames of a trivialization cocycle give block isomorphisms compatible with the transition
matrices: if `IsTrivializationCocycle V U g` (`V` has a frame `e_α` on `U_α`, and
`e_{α'} = e_α · g_{αα'}` on overlaps), then there are coordinate isomorphisms
`ψ_α : V|_{U_α} ≅ O^r` such that on `U_α ⊓ U_α'`
`freeTransition (U α) (U α') (g α' α) ∘ ψ_α = ψ_α'` (`IsTransitionCompatible`), i.e. the
coordinates satisfy `a_{α'} = g_{α'α} a_α`.

Reference: Hartshorne II Ex. 5.18(a) (locally free sheaves and transition matrices).

## Route

Write `F_α := frameHom V (U α) e'_α : O^r ⟶ V|_{U_α}` (`DualPullbackCommute_Frame`), an isomorphism because
`Scheme.Modules.IsFrameOn` implies `DualPullback.IsFrameOn` (`dualPullback_isFrameOn_of_isFrameOn`).
Put `ψ_α := (asIso F_α).symm`. For the compatibility on `W := U α ⊓ U α'` the whole proof is reduced, by a
variable-level categorical lemma (`cat_transition_of_frame`), to the identity of morphisms `O^r_W ⟶ V|_W`
  `matrixHom W (swapMatrix (g α' α)) ≫ frameHom V W (e'_{α'}|_W) = frameHom V W (e'_α|_W)`,
given the two "restriction" identities (`restrictFreeIso_inv_comp_map_frameHom`)
  `(restrictFreeIso h).inv ≫ R_h(F_α) ≫ (restrictιIso h V).hom = frameHom V W (e'_α|_W)`.
The latter is checked on the standard sections `ιFree i` via `freeHomEquiv`: the key computation is
`restrictFreeIso_inv_app_e` (`restrictFreeIso.inv` sends `e_i` on `A` to `e_i` on `j ''ᵁ A`), which comes from
the naturality of `restrictFunctorIsoPullback`, Mathlib's `pullback_map_ιFree_comp_pullbackObjFreeIso_hom`, and
the fact that the unit comparison `restrictFunctorIsoPullback ≫ pullbackObjUnitToUnit` sends `1 ↦ 1`
(`unitIso_hom_app_one`, from `restrictFunctorIsoPullback_hom_app_apply` and the adjunction description of
`pullbackObjUnitToUnit`). `matrixHom_comp_frameHom` computes `matrixHom ≫ frameHom` on `ιFree i` as
`∑ j, g j i • e_j`; the remaining identity is the transition relation of `IsTrivializationCocycle` at `(α', α)`,
restricted along `U α ⊓ U α' ≤ U α' ⊓ U α`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.TrivFrameIso

open MiyaokaMori.FreeStalk MiyaokaMori.DualPullback
open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

/-! ### Step 0: the unit part of `restrictFreeIso` sends `1` to `1` -/

/-- `pullbackObjUnitToUnit` on `η(x)` is `j.app x` (Mathlib
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`, section form). -/
theorem pullbackObjUnitToUnit_app_unitHom {Y Z : Scheme.{u}} (j : Y ⟶ Z) (T : Z.Opens)
    (x : Γ(Z, T)) :
    haveI : (SheafOfModules.pushforward.{u} j.toRingCatSheafHom).IsRightAdjoint :=
      (Scheme.Modules.pullbackPushforwardAdjunction j).isRightAdjoint
    Scheme.Modules.Hom.app (SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom) (j ⁻¹ᵁ T)
      (Scheme.Modules.pullbackUnitHom j (SheafOfModules.unit Z.ringCatSheaf) T x) =
      (j.app T).hom x := by
  have : (SheafOfModules.pushforward.{u} j.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction j).isRightAdjoint
  have h := congrArg (fun φ : SheafOfModules.unit Z.ringCatSheaf ⟶
      (Scheme.Modules.pushforward j).obj (SheafOfModules.unit Y.ringCatSheaf) =>
        Scheme.Modules.Hom.app φ T x)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      j.toRingCatSheafHom)
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- The composite `restrictFunctorIsoPullback ≫ pullbackObjUnitToUnit` on the unit sends `1` to `1`. -/
theorem unitIso_hom_app_one {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (A : Y.Opens) :
    haveI : (SheafOfModules.pushforward.{u} j.toRingCatSheafHom).IsRightAdjoint :=
      (Scheme.Modules.pullbackPushforwardAdjunction j).isRightAdjoint
    Scheme.Modules.Hom.app (SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom) A
      (((Scheme.Modules.restrictFunctorIsoPullback j).app
        (SheafOfModules.unit Z.ringCatSheaf)).hom.app A (uSec (j ''ᵁ A) 1)) = uSec A 1 := by
  have : (SheafOfModules.pushforward.{u} j.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction j).isRightAdjoint
  rw [Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply j
    (SheafOfModules.unit Z.ringCatSheaf) A (uSec (j ''ᵁ A) 1)]
  erw [Scheme.Modules.pullbackSectionsOn_apply]
  erw [Scheme.Modules.app_map (SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom)
      (le_of_eq (j.preimage_image_eq A).symm)]
  erw [pullbackObjUnitToUnit_app_unitHom]
  unfold uSec
  rw [map_one]
  exact PresheafOfModules.unit_map_one (R := Y.ringCatSheaf.obj)
    (homOfLE (le_of_eq (j.preimage_image_eq A).symm)).op

/-! ### Step 1: `restrictFreeIso` on the standard sections -/

variable {X : Scheme.{u}}

/-- `R(ιFree i) ≫ restrictFreeIso.hom` factors through the unit comparison. -/
theorem restrictFunctor_map_ιFree_comp_restrictFreeIso_hom {r : ℕ} {V W : X.Opens} (h : W ≤ V)
    (i : ULift.{u} (Fin r)) :
    haveI : (SheafOfModules.pushforward.{u} (X.homOfLE h).toRingCatSheafHom).IsRightAdjoint :=
      (Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE h)).isRightAdjoint
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) i) ≫
      (bundleFamilyOfCocycle.restrictFreeIso (r := r) h).hom =
    ((Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE h)).app
        (SheafOfModules.unit V.toScheme.ringCatSheaf)).hom ≫
      SheafOfModules.pullbackObjUnitToUnit (X.homOfLE h).toRingCatSheafHom ≫
      SheafOfModules.ιFree i := by
  have : (SheafOfModules.pushforward.{u} (X.homOfLE h).toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE h)).isRightAdjoint
  have : (TopologicalSpace.Opens.map (X.homOfLE h).base).Final :=
    bundleFamilyOfCocycle_opensMap_final h
  unfold bundleFamilyOfCocycle.restrictFreeIso
  rw [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, NatTrans.naturality, Category.assoc]
  congr 1
  exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i

/-- `restrictFreeIso.inv` sends the standard section `e_i` on `A` to `e_i` on `j ''ᵁ A`. -/
theorem restrictFreeIso_inv_app_e {r : ℕ} {V W : X.Opens} (h : W ≤ V) (i : ULift.{u} (Fin r))
    (A : W.toScheme.Opens) :
    (bundleFamilyOfCocycle.restrictFreeIso (r := r) h).inv.app A (e (ULift.{u} (Fin r)) i A) =
      e (ULift.{u} (Fin r)) i (X.homOfLE h ''ᵁ A) := by
  have : (SheafOfModules.pushforward.{u} (X.homOfLE h).toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE h)).isRightAdjoint
  have h0 := congrArg (fun φ => Scheme.Modules.Hom.app φ A (uSec (X.homOfLE h ''ᵁ A) 1))
    (restrictFunctor_map_ιFree_comp_restrictFreeIso_hom h i)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h0
  have h2 := unitIso_hom_app_one (X.homOfLE h) A
  have h3 := congrArg (fun z => Scheme.Modules.Hom.app (SheafOfModules.ιFree i) A z) h2
  have h1 : (bundleFamilyOfCocycle.restrictFreeIso (r := r) h).hom.app A
      (e (ULift.{u} (Fin r)) i (X.homOfLE h ''ᵁ A)) = e (ULift.{u} (Fin r)) i A := by
    rw [e_eq, e_eq]
    exact h0.trans h3
  rw [← h1]
  exact Scheme.Modules.modIso_inv_app_hom_app _ A _

/-! ### Step 2: `restrictιIso.hom` on sections -/

theorem restrictιIso_hom_app {V' W : X.Opens} (h : V' ≤ W) (M : X.Modules)
    (A : V'.toScheme.Opens) :
    (Scheme.Modules.restrictιIso h M).hom.app A =
      M.presheaf.map (eqToHom (Scheme.Modules.image_homOfLE_image h A).symm).op := by
  simp only [Scheme.Modules.restrictιIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app]
  exact Scheme.Modules.glueAux_map2 M.presheaf _ _ _

/-! ### Step 3: `frameHom` is compatible with restriction to a smaller open -/

/-- Restricting the frame isomorphism of `e` to `W ≤ V` gives the frame isomorphism of `e|_W`
(after aligning both sides by `restrictFreeIso` and `restrictιIso`). -/
theorem restrictFreeIso_inv_comp_map_frameHom {r : ℕ} {V W : X.Opens} (h : W ≤ V) (M : X.Modules)
    (s : ULift.{u} (Fin r) → Γ(M, V)) :
    (bundleFamilyOfCocycle.restrictFreeIso (r := r) h).inv ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (frameHom M V s) ≫
      (Scheme.Modules.restrictιIso h M).hom =
    frameHom M W (fun i => res M h (s i)) := by
  apply (M.restrict W.ι).freeHomEquiv.injective
  rw [freeHomEquiv_frameHom]
  funext i
  apply PresheafOfModules.sections_ext
  rintro ⟨A⟩
  rw [frameSection_val, SheafOfModules.freeHomEquiv_apply]
  change Scheme.Modules.Hom.app ((bundleFamilyOfCocycle.restrictFreeIso (r := r) h).inv ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (frameHom M V s) ≫
      (Scheme.Modules.restrictιIso h M).hom) A (e (ULift.{u} (Fin r)) i A) = _
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [restrictFreeIso_inv_app_e]
  change (Scheme.Modules.restrictιIso h M).hom.app A
    ((frameHom M V s).app (X.homOfLE h ''ᵁ A) (e (ULift.{u} (Fin r)) i (X.homOfLE h ''ᵁ A))) = _
  rw [frameHom_app_e, restrictιIso_hom_app, res_res]
  have key := ConcreteCategory.congr_hom (Scheme.Modules.glueAux_map2 M.presheaf
    (homOfLE (V.ι_image_le (X.homOfLE h ''ᵁ A))).op
    (eqToHom (Scheme.Modules.image_homOfLE_image h A).symm).op
    (homOfLE ((W.ι_image_le A).trans h)).op) (s i)
  rw [ConcreteCategory.comp_apply] at key
  exact key

/-- Two successive restriction maps of a presheaf on a preorder compose to the (unique) one. -/
theorem presheaf_map_map_eq {T : Type*} [Preorder T] (F : Tᵒᵖ ⥤ CommRingCat.{u}) {a b c : Tᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (k : a ⟶ c) (x : F.obj a) : (F.map g) ((F.map f) x) = (F.map k) x :=
  ConcreteCategory.congr_hom (Scheme.Modules.glueAux_map2 F f g k) x

/-! ### Step 4: `matrixHom ≫ frameHom` is the `frameHom` of the transformed frame -/

/-- `matrixHom W g` sends `ιFree i` to `∑ j, g j i • ιFree j`, so composing with the frame
isomorphism of `s` gives the frame isomorphism of `i ↦ ∑ j, g j i • s j`. -/
theorem matrixHom_comp_frameHom {r : ℕ} (W : X.Opens) (M : X.Modules)
    (g : Matrix (Fin r) (Fin r) Γ(X, W)) (s : ULift.{u} (Fin r) → Γ(M, W)) :
    bundleFamilyOfCocycle.matrixHom W g ≫ frameHom M W s =
      frameHom M W (fun i => ∑ j : ULift.{u} (Fin r), g j.down i.down • s j) := by
  apply (M.restrict W.ι).freeHomEquiv.injective
  rw [freeHomEquiv_frameHom]
  funext i
  rw [SheafOfModules.freeHomEquiv_comp_apply]
  unfold bundleFamilyOfCocycle.matrixHom Scheme.Modules.freeHomOfCoeffs
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  rintro ⟨A⟩
  rw [frameSection_val]
  change (frameHom M W s).app A (Scheme.Modules.freeHomOfCoeffs.sectionFamily _ (op A)) = _
  unfold Scheme.Modules.freeHomOfCoeffs.sectionFamily
  rw [Finsupp.sum_fintype _ _ (fun j => by rw [map_zero, zero_smul])]
  rw [map_sum, res_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [res_smul]
  change (frameHom M W s).app A ((W.toScheme.presheaf.map (homOfLE le_top).op
      (W.topIso.inv.hom (g j.down i.down))) • e (ULift.{u} (Fin r)) j A) = _
  rw [Scheme.Modules.Hom.app_smul, frameHom_app_e,
    MiyaokaMori.DualRestrictScratch.openRestrict_smul X W M A, Scheme.Opens.topIso_inv]
  congr 1
  exact presheaf_map_map_eq X.presheaf _ _ _ _

/-! ### Step 5: `Scheme.Modules.IsFrameOn` gives `DualPullback.IsFrameOn` -/

/-- A frame in the sense of `Scheme.Modules.IsFrameOn` (linearly independent and spanning on every
open subset) is a frame in the sense of `DualPullback.IsFrameOn` (the coordinate map is bijective),
after reindexing by `ULift`. -/
theorem dualPullback_isFrameOn_of_isFrameOn {r : ℕ} {M : X.Modules} {U : X.Opens}
    {e : Fin r → Γ(M, U)} (he : M.IsFrameOn U e) :
    IsFrameOn M (fun i : ULift.{u} (Fin r) => e i.down) := by
  intro W hW
  obtain ⟨hli, hsp⟩ := he W hW
  have hsum : ∀ c : ULift.{u} (Fin r) → Γ(X, W),
      frameMap M (fun i : ULift.{u} (Fin r) => e i.down) hW c =
        ∑ i : Fin r, c (ULift.up i) • res M hW (e i) := by
    intro c
    rw [frameMap_apply]
    exact (Equiv.ulift.symm.sum_comp
      (fun i : ULift.{u} (Fin r) => c i • res M hW (e i.down))).symm
  constructor
  · intro c c' hcc'
    have h0 : frameMap M (fun i : ULift.{u} (Fin r) => e i.down) hW (c - c') = 0 := by
      rw [map_sub, hcc', sub_self]
    rw [hsum] at h0
    have h1 := (Fintype.linearIndependent_iff.mp hli) (fun i => (c - c') (ULift.up i)) h0
    funext i
    have hi := h1 i.down
    simp only [Pi.sub_apply] at hi
    exact sub_eq_zero.mp hi
  · intro t
    have ht : t ∈ Submodule.span Γ(X, W)
        (Set.range fun i => M.presheaf.map (homOfLE hW).op (e i)) := by
      rw [hsp]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, W)).mp ht
    exact ⟨fun i => c i.down, by rw [hsum]; exact hc⟩

/-! ### Step 6: the categorical bookkeeping, at the variable level -/

/-- Abstract form of the compatibility: if `m ≫ G' = G` for the two "restricted frame"
morphisms `G = c⁻¹ ≫ φ ≫ a`, `G' = d⁻¹ ≫ φ' ≫ a'`, then the transition `c ≫ m ≫ d⁻¹`
intertwines `φ⁻¹` and `φ'⁻¹` (up to the alignments `a`, `a'`). -/
theorem cat_transition_of_frame {C : Type*} [Category C] {P Q A F P' Q' : C}
    (a : P ≅ A) (c : Q ≅ F) (a' : P' ≅ A) (d : Q' ≅ F) (φ : Q ≅ P) (φ' : Q' ≅ P') (m : F ⟶ F)
    (hyp : m ≫ d.inv ≫ φ'.hom ≫ a'.hom = c.inv ≫ φ.hom ≫ a.hom) :
    a.inv ≫ φ.inv ≫ (c.hom ≫ m ≫ d.inv) = a'.inv ≫ φ'.inv := by
  rw [← cancel_mono (φ'.hom ≫ a'.hom)]
  simp only [Category.assoc]
  rw [hyp]
  simp

end MiyaokaMori.TrivFrameIso

open MiyaokaMori.TrivFrameIso MiyaokaMori.DualPullback in
open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul) in
/-- The frames `e_α` of a trivialization cocycle `IsTrivializationCocycle V U g` give coordinate
isomorphisms `ψ_α : V|_{U_α} ≅ O_{U_α}^r` which on overlaps are compatible with
`freeTransition (U α) (U α') (g α' α)` (left multiplication of coordinates by `g_{α'α}`).

Reference: Hartshorne II Ex. 5.18(a) (locally free sheaves ↔ transition matrices).

Proof: `ψ_α := (asIso (frameHom V (U α) e'_α)).symm` (`isIso_frameHom_of_isFrameOn` +
`dualPullback_isFrameOn_of_isFrameOn`). By `cat_transition_of_frame` the compatibility reduces to
`matrixHom (swap g_{α'α}) ≫ frameHom V W (e'_{α'}|_W) = frameHom V W (e'_α|_W)`
(two instances of `restrictFreeIso_inv_comp_map_frameHom` give "the restricted frame isomorphism
is the isomorphism of the restricted frame"), which follows from `matrixHom_comp_frameHom` and
the transition relation of the cocycle (taken at `(α', α)`, restricted along `inf_comm`).
See the module docstring for details. -/
theorem IsTrivializationCocycle.exists_frame_iso {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} {r : ℕ}
    {V : X.Modules} {U : ι → X.Opens} {g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α')}
    (h : IsTrivializationCocycle V U g) :
    ∃ ψ : ∀ α, V.restrict (U α).ι ≅
        SheafOfModules.free (R := (U α).toScheme.ringCatSheaf) (ULift.{u} (Fin r)),
      ∀ α α', AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible U
        (fun α => SheafOfModules.free (R := (U α).toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
        (fun α α' => AlgebraicGeometry.Scheme.Modules.freeTransition (U α) (U α') (g α' α)) V ψ α α' := by
  obtain ⟨e, he, h2⟩ := h
  let e' : ∀ α, ULift.{u} (Fin r) → Γ(V, U α) := fun α i => e α i.down
  have hfr : ∀ α, IsIso (frameHom V (U α) (e' α)) := fun α =>
    isIso_frameHom_of_isFrameOn V (U α) (e' α) (dualPullback_isFrameOn_of_isFrameOn (he α))
  refine ⟨fun α => (@asIso _ _ _ _ (frameHom V (U α) (e' α)) (hfr α)).symm, fun α α' => ?_⟩
  -- the transition relation of the frames, restricted to `U α ⊓ U α'`
  have key : ∀ i : ULift.{u} (Fin r),
      res V (inf_le_left : U α ⊓ U α' ≤ U α) (e' α i) =
        ∑ j : ULift.{u} (Fin r),
          bundleFamilyOfCocycle.swapMatrix (U α) (U α') (g α' α) j.down i.down •
            res V (inf_le_right : U α ⊓ U α' ≤ U α') (e' α' j) := by
    intro i
    have h3 := congrArg (res V (le_of_eq (inf_comm (U α) (U α')) : U α ⊓ U α' ≤ U α' ⊓ U α))
      (h2 α' α i.down)
    rw [res_res, res_sum] at h3
    refine h3.trans ?_
    rw [← Equiv.ulift.symm.sum_comp (fun j : ULift.{u} (Fin r) =>
      bundleFamilyOfCocycle.swapMatrix (U α) (U α') (g α' α) j.down i.down •
        res V (inf_le_right : U α ⊓ U α' ≤ U α') (e' α' j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [res_smul, res_res]
    rfl
  have hL := restrictFreeIso_inv_comp_map_frameHom (inf_le_left : U α ⊓ U α' ≤ U α) V (e' α)
  have hL' := restrictFreeIso_inv_comp_map_frameHom (inf_le_right : U α ⊓ U α' ≤ U α') V (e' α')
  have hE : bundleFamilyOfCocycle.matrixHom (U α ⊓ U α')
        (bundleFamilyOfCocycle.swapMatrix (U α) (U α') (g α' α)) ≫
      frameHom V (U α ⊓ U α') (fun i => res V inf_le_right (e' α' i)) =
      frameHom V (U α ⊓ U α') (fun i => res V inf_le_left (e' α i)) := by
    rw [matrixHom_comp_frameHom]
    congr 1
    funext i
    exact (key i).symm
  unfold AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible
    AlgebraicGeometry.Scheme.Modules.freeTransition
  exact cat_transition_of_frame
    (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_left : U α ⊓ U α' ≤ U α) V)
    (bundleFamilyOfCocycle.restrictFreeIso inf_le_left)
    (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_right : U α ⊓ U α' ≤ U α') V)
    (bundleFamilyOfCocycle.restrictFreeIso inf_le_right)
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE inf_le_left)).mapIso
      (@asIso _ _ _ _ (frameHom V (U α) (e' α)) (hfr α)))
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE inf_le_right)).mapIso
      (@asIso _ _ _ _ (frameHom V (U α') (e' α')) (hfr α')))
    (bundleFamilyOfCocycle.matrixHom _ _)
    (by
      show _ ≫ (bundleFamilyOfCocycle.restrictFreeIso inf_le_right).inv ≫
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE inf_le_right)).map
            (frameHom V (U α') (e' α')) ≫
          (AlgebraicGeometry.Scheme.Modules.restrictιIso inf_le_right V).hom =
        (bundleFamilyOfCocycle.restrictFreeIso inf_le_left).inv ≫
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE inf_le_left)).map
            (frameHom V (U α) (e' α)) ≫
          (AlgebraicGeometry.Scheme.Modules.restrictιIso inf_le_left V).hom
      rw [hL', hL]
      exact hE)

end
