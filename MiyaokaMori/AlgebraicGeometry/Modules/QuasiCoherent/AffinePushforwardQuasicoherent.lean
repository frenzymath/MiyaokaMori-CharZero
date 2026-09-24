import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.AffineTildeAdjunction

/-! # Pushforward along an affine morphism preserves quasi-coherence

An affine morphism (in particular a finite morphism) pushes the structure sheaf forward to a
quasi-coherent sheaf: `f` affine ⇒ `f_*O_X` quasi-coherent, and on an affine open `V`,
`(f_*O_X)|_V ≅ Γ(X, f⁻¹V)~`.

Source: Stacks 01SB (Morphisms, "affine morphisms and quasi-coherent modules", part of
lemma-affine-equivalence-modules) / Stacks 01I9(2); Hartshorne II.5.8(c).

## Proof

Everything is proved for an arbitrary quasi-coherent `M` (`isQuasicoherent_pushforward_of_isAffineHom`);
the target `isQuasicoherent_pushforward_one_of_isAffineHom` is the case `M = O_X`.

1. *Quasi-coherence is affine-local on the target* (`isQuasicoherent_of_affineOpens_restrict`):
   if `N|_U` is quasi-coherent for every affine open `U ⊆ Y`, then `N` is quasi-coherent. Proof: on the
   affine scheme `U`, a quasi-coherent module has a global presentation (`presentationOfAffine`: the counit
   `T(Γ N) ⟶ N` of the transported tilde adjunction is an isomorphism, and `tilde` of a module has the
   presentation `presentationTilde`); the presentation of `N|_U` is moved to the slice `N.over U` by
   `presentationOver` (already in the library); finally Mathlib's `IsQuasicoherent.of_coversTop` glues over
   the affine opens (`iSup_affineOpens_eq_top`).
2. *Base change of `f_*` to an open `V ⊆ S`* (`pushforwardRestrictIso`):
   `(f_*M)|_V ≅ (f|_{f⁻¹V})_* (M|_{f⁻¹V})`, where `f|_{f⁻¹V} = f.resLE V (f⁻¹V)`. Proof: the unit
   `M ⟶ j_* j^* M` of `restrictAdjunction` (`j = (f⁻¹V).ι`) becomes an isomorphism after `f_*` and `|_V`
   (`isIso_restrict_pushforward_unit`), because on `W ⊆ V` its component is the restriction map of `M` along
   the *equality* `j '' j⁻¹ (f⁻¹(V.ι '' W)) = f⁻¹(V.ι '' W)` (`image_preimage_preimage_eq`); then
   `f_* j_* ≅ (j ≫ f)_* = (f| ≫ V.ι)_* ≅ V.ι_* (f|)_*` (`pushforwardComp`, `pushforwardCongr`) and
   `(V.ι_* N)|_V ≅ N` (`restrictFunctorAdjCounitIso`).
3. *Pushforward between affine schemes* (`isQuasicoherent_pushforward_of_isAffine`): for `g : U ⟶ V`
   with `U, V` affine, write `g = U.isoSpec.hom ≫ Spec.map g.appTop ≫ V.isoSpec.inv`
   (`isoSpec_hom_naturality`). Pushforward along an isomorphism preserves quasi-coherence
   (`AffineTilde.isQuasicoherent_pushforward_hom`), and pushforward along `Spec.map φ` preserves it by
   Mathlib's `isIso_fromTildeΓ_pushforward` together with `isQuasicoherent_iff_isIso_fromTildeΓ`.
4. Assemble: for `V` affine open in `S`, `f⁻¹V` is affine (`IsAffineOpen.preimage`, definition of
   `IsAffineHom`), `M|_{f⁻¹V}` is quasi-coherent (Mathlib `isQuasicoherent_restrictFunctor`), so by 3 and 2
   `(f_*M)|_V` is quasi-coherent, and by 1 `f_*M` is.
5. `O_X` is quasi-coherent (`isQuasicoherent_unit`): on `Spec R` Mathlib knows
   `IsIso (fromTildeΓ (unit))`; on an affine scheme transport along `isoSpec` using `unitPullbackIso` and
   `isQuasicoherent_pullback`; in general use 1 with `restrictUnitIso`.

Step 2 also gives the second half of the informal statement, `(f_*O_X)|_V ≅ Γ(X, f⁻¹V)~` (combine
`pushforwardRestrictIso` with the counit isomorphism of `AffineTilde.adj` on `V`); it is not stated
separately because no user needs it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.AffinePushforwardAux

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module on an affine scheme has a global presentation: the counit
`T (Γ N) ⟶ N` of the transported tilde adjunction is an isomorphism (`AffineTilde.isIso_counit_app`),
and `tilde P` has the presentation `presentationTilde` (pulled back along `isoSpec.hom`). -/
def presentationOfAffine {Y : Scheme.{u}} [IsAffine Y] (N : Y.Modules) [N.IsQuasicoherent] :
    N.Presentation := by
  haveI : @IsIso (SheafOfModules.{u} Y.ringCatSheaf) _ _ _ (AffineTilde.adj.counit.app N) :=
    AffineTilde.isIso_counit_app N
  have P : (AffineTilde.T (AffineTilde.ΓS N)).Presentation :=
    PullbackQcAux.presentationPullback Y.isoSpec.hom
      (presentationTilde (AffineTilde.ΓS N) Set.univ (by simp) _ (Submodule.span_eq _))
  exact SheafOfModules.Presentation.ofIsIso (AffineTilde.adj.counit.app N) P

/-- Quasi-coherence is affine-local on the target: if `N|_U` is quasi-coherent for every affine open
`U`, then `N` is quasi-coherent (Stacks 01BE / Hartshorne II.5.4; via `IsQuasicoherent.of_coversTop`). -/
theorem isQuasicoherent_of_affineOpens_restrict {Y : Scheme.{u}} (N : Y.Modules)
    (h : ∀ U : Y.affineOpens, (N.restrict U.1.ι).IsQuasicoherent) : N.IsQuasicoherent := by
  have : ∀ U : Y.affineOpens, (N.over U.1).IsQuasicoherent := fun U => by
    have : IsAffine U.1 := U.2
    have := h U
    exact (PullbackQcAux.presentationOver U.1 (presentationOfAffine (N.restrict U.1.ι))).isQuasicoherent
  refine SheafOfModules.IsQuasicoherent.of_coversTop N (fun U : Y.affineOpens => U.1) ?_
  rw [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
  exact AlgebraicGeometry.iSup_affineOpens_eq_top Y

/-- The structure sheaf of an affine scheme is quasi-coherent (Mathlib knows `IsIso (fromTildeΓ O)` on
`Spec R`; transport along `isoSpec` using `f^*O ≅ O`). -/
theorem isQuasicoherent_unit_of_isAffine (Y : Scheme.{u}) [IsAffine Y] :
    (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
  haveI : (SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (PullbackQcAux.unitPullbackIso Y.isoSpec.hom).symm (isQuasicoherent_pullback _ _)

/-- The structure sheaf of any scheme is quasi-coherent. -/
theorem isQuasicoherent_unit (X : Scheme.{u}) : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  refine isQuasicoherent_of_affineOpens_restrict _ fun U => ?_
  have : IsAffine U.1 := U.2
  have := isQuasicoherent_unit_of_isAffine U.1
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (restrictUnitIso U.1.ι).symm inferInstance

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (V : S.Opens)

/-- `f⁻¹(V.ι '' W) ⊆ f⁻¹V`, hence `j '' j⁻¹ (f⁻¹(V.ι '' W)) = f⁻¹(V.ι '' W)` for `j = (f⁻¹V).ι`. -/
theorem image_preimage_preimage_eq (W : (V : Scheme.{u}).Opens) :
    (f ⁻¹ᵁ V).ι ''ᵁ ((f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ (V.ι ''ᵁ W))) = f ⁻¹ᵁ (V.ι ''ᵁ W) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
  exact f.preimage_mono (V.ι_image_le W)

/-- The unit `M ⟶ j_* j^* M` (`j = (f⁻¹V).ι`) becomes an isomorphism after `f_*` and restriction to
`V`: its component over `W ⊆ V` is the restriction map of `M` along an equality of opens. -/
theorem isIso_restrict_pushforward_unit :
    IsIso ((restrictFunctor V.ι).map ((pushforward f).map
      ((restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M))) := by
  rw [Hom.isIso_iff_isIso_app]
  intro W
  change IsIso (((restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M).app (f ⁻¹ᵁ (V.ι ''ᵁ W)))
  rw [restrictAdjunction_unit_app_app]
  have : homOfLE ((f ⁻¹ᵁ V).ι.image_preimage_le (f ⁻¹ᵁ (V.ι ''ᵁ W))) =
      eqToHom (image_preimage_preimage_eq f V W) := Subsingleton.elim _ _
  rw [this]
  have : IsIso (eqToHom (image_preimage_preimage_eq f V W)).op := isIso_op _
  exact Functor.map_isIso M.presheaf _

/-- Base change of the pushforward to the open `V ⊆ S`:
`(f_*M)|_V ≅ (f|_{f⁻¹V})_* (M|_{f⁻¹V})` with `f|_{f⁻¹V} = f.resLE V (f⁻¹V)`. -/
def pushforwardRestrictIso :
    ((pushforward f).obj M).restrict V.ι ≅
      (pushforward (f.resLE V (f ⁻¹ᵁ V) le_rfl)).obj (M.restrict (f ⁻¹ᵁ V).ι) :=
  haveI := isIso_restrict_pushforward_unit f M V
  asIso ((restrictFunctor V.ι).map ((pushforward f).map
      ((restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M))) ≪≫
  (restrictFunctor V.ι).mapIso ((pushforwardComp (f ⁻¹ᵁ V).ι f).app (M.restrict (f ⁻¹ᵁ V).ι)) ≪≫
  (restrictFunctor V.ι).mapIso
    ((pushforwardCongr (Scheme.Hom.resLE_comp_ι f le_rfl).symm).app (M.restrict (f ⁻¹ᵁ V).ι)) ≪≫
  (restrictFunctor V.ι).mapIso
    (((pushforwardComp (f.resLE V (f ⁻¹ᵁ V) le_rfl) V.ι).app (M.restrict (f ⁻¹ᵁ V).ι)).symm) ≪≫
  (restrictFunctorAdjCounitIso V.ι).app
    ((pushforward (f.resLE V (f ⁻¹ᵁ V) le_rfl)).obj (M.restrict (f ⁻¹ᵁ V).ι))

/-- Pushforward along a morphism of affine schemes preserves quasi-coherence (Stacks 01SB, affine case):
`g = U.isoSpec.hom ≫ Spec.map g.appTop ≫ V.isoSpec.inv`; isomorphisms preserve quasi-coherence, and
`Spec.map φ` does by Mathlib's `isIso_fromTildeΓ_pushforward`. -/
theorem isQuasicoherent_pushforward_of_isAffine {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (g : Y ⟶ Z) (N : Y.Modules) [N.IsQuasicoherent] :
    ((pushforward g).obj N).IsQuasicoherent := by
  have hg : (Y.isoSpec.hom ≫ Spec.map g.appTop) ≫ Z.isoSpec.inv = g := by
    rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1 : ((pushforward Y.isoSpec.hom).obj N).IsQuasicoherent :=
    AffineTilde.isQuasicoherent_pushforward_hom Y.isoSpec N
  have h2 : ((pushforward (Spec.map g.appTop)).obj
      ((pushforward Y.isoSpec.hom).obj N)).IsQuasicoherent := by
    rw [isQuasicoherent_iff_isIso_fromTildeΓ]
    exact isIso_fromTildeΓ_pushforward g.appTop _
  have h3 : ((pushforward Z.isoSpec.inv).obj ((pushforward (Spec.map g.appTop)).obj
      ((pushforward Y.isoSpec.hom).obj N))).IsQuasicoherent :=
    AffineTilde.isQuasicoherent_pushforward_hom Z.isoSpec.symm _
  refine (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso ?_ h3
  exact (pushforward Z.isoSpec.inv).mapIso
      ((pushforwardComp Y.isoSpec.hom (Spec.map g.appTop)).app N) ≪≫
    (pushforwardComp (Y.isoSpec.hom ≫ Spec.map g.appTop) Z.isoSpec.inv).app N ≪≫
    (pushforwardCongr hg).app N

/-- Pushforward along an affine morphism preserves quasi-coherence (Stacks 01SB / 01I9(2)). -/
theorem isQuasicoherent_pushforward_of_isAffineHom [IsAffineHom f] [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  refine isQuasicoherent_of_affineOpens_restrict _ fun V => ?_
  have : IsAffine V.1 := V.2
  have : IsAffine (f ⁻¹ᵁ V.1) := V.2.preimage f
  have : ((pushforward (f.resLE V.1 (f ⁻¹ᵁ V.1) le_rfl)).obj
      (M.restrict (f ⁻¹ᵁ V.1).ι)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffine _ _
  exact (SheafOfModules.isQuasicoherent V.1.toScheme.ringCatSheaf).prop_of_iso
    (pushforwardRestrictIso f M V.1).symm inferInstance

end AlgebraicGeometry.Scheme.Modules.AffinePushforwardAux

theorem AlgebraicGeometry.isQuasicoherent_pushforward_one_of_isAffineHom {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) [AlgebraicGeometry.IsAffineHom f] :
    ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
  haveI := AlgebraicGeometry.Scheme.Modules.AffinePushforwardAux.isQuasicoherent_unit X
  AlgebraicGeometry.Scheme.Modules.AffinePushforwardAux.isQuasicoherent_pushforward_of_isAffineHom f _

end
