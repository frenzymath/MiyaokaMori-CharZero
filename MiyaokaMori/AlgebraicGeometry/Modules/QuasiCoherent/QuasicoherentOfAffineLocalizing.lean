import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization

/-! # An affine-local criterion for quasi-coherence

The converse of `QcSectionsBasicOpenLocalization`: let `X` be a scheme and `M` an `O_X`-module. If for
every affine open `U ⊆ X` and every `h ∈ Γ(U, O_X)` the restriction map `Γ(U, M) → Γ(D(h), M)` has the
two properties of "localization at `h`",
(a) (existence) `∀ s ∈ Γ(D(h), M), ∃ n, t ∈ Γ(U, M), t|_{D(h)} = (h|_{D(h)})^n • s`;
(b) (uniqueness) `∀ t ∈ Γ(U, M), t|_{D(h)} = 0 ⟹ ∃ n, h^n • t = 0`,
then `M` is quasi-coherent.

Proof (Stacks 01IB / EGA I 1.4.1; Mathlib's `isQuasicoherent_iff_isIso_fromTildeΓ` and
`isIso_fromTildeΓ_iff_isLocalizing` reduce the case of `Spec R` to `IsLocalizing`):
1. Take an affine open `U`, `A = Γ(U, O_X)`, `j = hU.fromSpec : Spec A → X` (an open immersion with image
   `U`), `N = M.restrict j`. `Γ(V, N) = Γ(j(V), M)` by definition (`restrictAppIso = Iso.refl`); `j(⊤) = U`
   and `j(D(f)) = X.basicOpen f`. The action of `A` on `Γ(V, N)` is `f ↦ (f|_{j(V)}) • −`
   (`QcBasicOpenLocAux.smul_key`). So (a), (b) for `U, f` are exactly the two conditions of
   `IsLocalizedModule.Away.mk_of_addCommGroup` (the invertibility condition
   `isUnit_algebraMap_end_of_le_basicOpen` holds automatically for any sheaf of modules on `Spec A`), hence
   `N` is `IsLocalizing`, so `N` is quasi-coherent and `N ≅ Γ(N)^~`; `Γ(N)^~` has the global presentation
   `presentationTilde`, hence so does `N`.
2. Restrict along the isomorphism `hU.isoSpec.hom : U → Spec A` (`presentationRestrict`) and use
   `isoSpec.hom ≫ fromSpec = U.ι` (`restrictFunctorComp`, `restrictFunctorCongr`) to get a global
   presentation of `M.restrict U.ι`; `PullbackQcAux.presentationOver` transports it to a presentation of
   `M.over U` on the slice site, so `M.over U` is quasi-coherent.
3. Affine opens cover `X` (`iSup_affineOpens_eq_top`); `IsQuasicoherent.of_coversTop` glues.

Source: Stacks 01IB (quasi-coherent ⟺ `M~` on affine opens), EGA I (1.4.1); Mathlib
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

namespace QcOfAffineLocalizingAux

open QcBasicOpenLocAux

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)

include hU in
/-- Step 1: the two localization properties ⟹ `M.restrict hU.fromSpec` is `IsLocalizing` on
`Spec Γ(U, O_X)`. -/
theorem isLocalizing_restrict
    (hex : ∀ (h : Γ(X, U)) (s : Γ(M, X.basicOpen h)),
      ∃ (n : ℕ) (t : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le h)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) ^ n • s)
    (huniq : ∀ (h : Γ(X, U)) (t : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le h)).op t = 0 → ∃ n : ℕ, h ^ n • t = 0) :
    IsLocalizing (modulesSpecToSheaf.obj (M.restrict hU.fromSpec)) := by
  intro f
  have e1 : hU.fromSpec ''ᵁ D f = X.basicOpen f := hU.fromSpec_image_basicOpen f
  have e0 : hU.fromSpec ''ᵁ ⊤ = U := image_top hU
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    change Γ(M.restrict hU.fromSpec, D f) at x
    obtain ⟨n, t, ht⟩ := hex f
      (M.presheaf.map (eqToHom e1.symm).op ((M.restrictAppIso hU.fromSpec (D f)).hom x))
    refine ⟨n, (M.restrictAppIso hU.fromSpec ⊤).inv (M.presheaf.map (eqToHom e0).op t), ?_⟩
    show f ^ n • x = (M.restrict hU.fromSpec).presheaf.map (D f).leTop.op
      ((M.restrictAppIso hU.fromSpec ⊤).inv (M.presheaf.map (eqToHom e0).op t))
    apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec (D f)).hom).injective
    rw [smul_key, Iso.inv_hom_id_apply, Scheme.Modules.map_restrictAppIso_hom_apply,
      Iso.inv_hom_id_apply]
    have h1 : M.presheaf.map (homOfLE (Scheme.Hom.image_mono _ (le_top : D f ≤ ⊤))).op
        (M.presheaf.map (eqToHom e0).op t) =
        M.presheaf.map (eqToHom e1).op (M.presheaf.map (homOfLE (X.basicOpen_le f)).op t) := by
      rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
      rfl
    have hcancel : M.presheaf.map (eqToHom e1).op (M.presheaf.map (eqToHom e1.symm).op
        ((M.restrictAppIso hU.fromSpec (D f)).hom x)) = (M.restrictAppIso hU.fromSpec (D f)).hom x := by
      rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
        M.presheaf.map_id, ConcreteCategory.id_apply]
    rw [h1, ht, Scheme.Modules.map_smul, hcancel, map_pow, map_pow, ← X.presheaf.map_comp_apply]
    rfl
  · intro x hx
    change Γ(M.restrict hU.fromSpec, ⊤) at x
    change (M.restrict hU.fromSpec).presheaf.map (D f).leTop.op x = 0 at hx
    have hx' : M.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (M.presheaf.map (eqToHom e0.symm).op ((M.restrictAppIso hU.fromSpec ⊤).hom x)) = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (M.presheaf.map (eqToHom e1).op)).injective
      rw [map_zero, ← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
      have := congr((M.restrictAppIso hU.fromSpec (D f)).hom $hx)
      rw [map_zero, Scheme.Modules.map_restrictAppIso_hom_apply] at this
      exact this
    obtain ⟨n, hn⟩ := huniq f _ hx'
    refine ⟨n, ?_⟩
    show f ^ n • x = 0
    apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec ⊤).hom).injective
    rw [smul_key, Iso.inv_hom_id_apply, map_zero]
    have hcancel : M.presheaf.map (eqToHom e0).op (M.presheaf.map (eqToHom e0.symm).op
        ((M.restrictAppIso hU.fromSpec ⊤).hom x)) = (M.restrictAppIso hU.fromSpec ⊤).hom x := by
      rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
        M.presheaf.map_id, ConcreteCategory.id_apply]
    replace hn := congr(M.presheaf.map (eqToHom e0).op $hn)
    rw [map_zero, Scheme.Modules.map_smul, hcancel] at hn
    exact hn

include hU in
set_option backward.isDefEq.respectTransparency false in
/-- Step 2: `M.restrict hU.fromSpec` is `IsLocalizing` ⟹ `M.over U` on the slice site is quasi-coherent. -/
theorem isQuasicoherent_over_of_isLocalizing
    (hloc : IsLocalizing (modulesSpecToSheaf.obj (M.restrict hU.fromSpec))) :
    (M.over U).IsQuasicoherent := by
  have hiso : IsIso (M.restrict hU.fromSpec).fromTildeΓ :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mpr hloc
  let P₀ : (M.restrict hU.fromSpec).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u} (M.restrict hU.fromSpec).fromTildeΓ
      (presentationTilde.{u} _ Set.univ (by simp) _ (Submodule.span_eq _))
  let P₁ : ((M.restrict hU.fromSpec).restrict hU.isoSpec.hom).Presentation :=
    Scheme.Modules.presentationRestrict hU.isoSpec.hom P₀
  let e : (M.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ M.restrict U.ι :=
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M
  let P₂ : (M.restrict U.ι).Presentation := SheafOfModules.Presentation.ofIsIso.{u, u, u} e.hom P₁
  exact (Scheme.Modules.PullbackQcAux.presentationOver U P₂).isQuasicoherent

end QcOfAffineLocalizingAux

/-- Affine-local criterion for quasi-coherence: if for every affine open `U` and every `h ∈ Γ(U, O_X)` the
restriction `Γ(U, M) → Γ(D(h), M)` has the existence and uniqueness properties of a localization, then
`M` is quasi-coherent (the "⟸" direction of Stacks 01IB, for general schemes). -/
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_affine_localizing
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    (hex : ∀ (U : X.Opens), AlgebraicGeometry.IsAffineOpen U →
      ∀ (h : Γ(X, U)) (s : Γ(M, X.basicOpen h)),
      ∃ (n : ℕ) (t : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le h)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) ^ n • s)
    (huniq : ∀ (U : X.Opens), AlgebraicGeometry.IsAffineOpen U → ∀ (h : Γ(X, U)) (t : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le h)).op t = 0 → ∃ n : ℕ, h ^ n • t = 0) :
    M.IsQuasicoherent := by
  have : ∀ U : X.affineOpens, (M.over (U : X.Opens)).IsQuasicoherent := fun U =>
    QcOfAffineLocalizingAux.isQuasicoherent_over_of_isLocalizing M U.2
      (QcOfAffineLocalizingAux.isLocalizing_restrict M U.2 (hex U U.2) (huniq U U.2))
  refine SheafOfModules.IsQuasicoherent.of_coversTop M (fun U : X.affineOpens => (U : X.Opens)) ?_
  rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
  exact iSup_affineOpens_eq_top X

end
