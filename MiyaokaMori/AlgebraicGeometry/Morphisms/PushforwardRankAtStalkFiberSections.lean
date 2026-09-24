import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentStalkIsLocalizedModule
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforwardQuasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Localization.BaseChange

/-! # Rank of the pushforward of the structure sheaf at a point

For an affine morphism `f : X → Y`, the rank of the pushforward `f_*O_X` at `y` equals the
dimension over `κ(y)` of the ring of global sections of the fibre `F = f.fiber y`:
`rank_y(f_*O_X) = dim_{κ(y)} (κ(y) ⊗_{O_{Y,y}} (f_*O_X)_y) = dim_{κ(y)} Γ(F, O_F)`.

Reference: [Stacks, 02RH], step 3 of the proof (reduce to the affine case, where
`(f_*O_X)_y = A_p` and `Γ(F) = κ(p) ⊗_R A`).

## Outline of the proof

Fix an affine open `U ∋ y`, `R := Γ(Y, U)`, `A := Γ(X, f⁻¹U) = Γ(f_*O_X, U)`, `O := O_{Y,y}`, `k := κ(y)`,
`p ⊂ R` the prime of `y`.
* (A1) `f_*O_X` is quasi-coherent (`AffinePushforwardQuasicoherent`), so its stalk at `y` is the localization
  `A_p` of `A` (`isLocalizedModule_germₗ_of_isQuasicoherent`), i.e. `O ⊗[R] A ≃ₗ[O] (f_*O_X)_y`
  (`IsLocalizedModule.isBaseChange`), hence `k ⊗[O] (f_*O_X)_y ≃ₗ[k] k ⊗[O] (O ⊗[R] A) ≃ₗ[k] k ⊗[R] A`
  (`AlgebraTensorModule.congr`, `cancelBaseChange`).
* (A2) The fiber square `F = X ×_Y Spec k` restricted to the affine opens `U`, `f⁻¹U`, `⊤` is a pushout of rings
  (Mathlib `isIso_pushoutSection_of_isAffineOpen`, `isIso_pushoutSection_iff`); after identifying
  `Γ(Spec k, ⊤) ≅ k` (`ΓSpecIso`, `IsPushout.of_iso`) and `R → k` with the evaluation `germ ≫ residue`
  (`fromSpecResidueField_appLE_ΓSpecIso_hom`), `CommRingCat.isPushout_iff_isPushout` gives
  `Algebra.IsPushout R k A Γ(F)`, so `k ⊗[R] A ≃ₐ[k] Γ(F, O_F)` (`Algebra.IsPushout.equiv`).
* (A3) `Module.finrank` is invariant under the `k`-linear equivalences (`LinearEquiv.finrank_eq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry

/-- Sections over `U ∋ y` pulled back along `Spec κ(y) → Y` and identified with `κ(y)` via `ΓSpecIso` give the
evaluation map `Γ(Y, U) → O_{Y,y} → κ(y)` (`Y.evaluation U y hy = germ ≫ residue`).
Proof: `fromSpecResidueField = Spec.map (residue) ≫ fromSpecStalk`; `comp_appLE`, `fromSpecStalk_app`
(`fromSpecStalk.app U = germ ≫ (ΓSpecIso O).inv ≫ restriction`), `map_appLE`, `appLE_eq_app` and
`ΓSpecIso_naturality` for `Spec.map (residue)`. -/
theorem Scheme.fromSpecResidueField_appLE_ΓSpecIso_hom {Y : Scheme.{u}} (y : Y) {U : Y.Opens}
    (hy : y ∈ U) (h : (⊤ : (Spec (Y.residueField y)).Opens) ≤ (Y.fromSpecResidueField y) ⁻¹ᵁ U) :
    (Y.fromSpecResidueField y).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (Y.residueField y)).hom =
      Y.presheaf.germ U y hy ≫ Y.residue y := by
  have h' : (⊤ : (Spec (Y.residueField y)).Opens) ≤
      (Spec.map (Y.residue y)) ⁻¹ᵁ ((Y.fromSpecStalk y) ⁻¹ᵁ U) := h
  have e1 : (Y.fromSpecResidueField y).appLE U ⊤ h =
      (Y.fromSpecStalk y).app U ≫
        (Spec.map (Y.residue y)).appLE ((Y.fromSpecStalk y) ⁻¹ᵁ U) ⊤ h' :=
    Scheme.Hom.comp_appLE (Spec.map (Y.residue y)) (Y.fromSpecStalk y) U ⊤ h
  rw [e1, Scheme.fromSpecStalk_app hy, Category.assoc, Category.assoc, Category.assoc,
    Scheme.Hom.map_appLE_assoc]
  have e2 : (Spec.map (Y.residue y)).appLE ⊤ ⊤ (le_top.trans (le_of_eq rfl)) =
      (Spec.map (Y.residue y)).appTop := by
    show (Spec.map (Y.residue y)).appLE ⊤ ((Spec.map (Y.residue y)) ⁻¹ᵁ ⊤) le_rfl = _
    exact Scheme.Hom.appLE_eq_app _
  rw [e2, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- **Rank of the pushforward of the structure sheaf along an affine morphism** ([Stacks, 02RH], step 3 of
the proof). Let `f : X ⟶ Y` be an affine morphism, `y ∈ Y`, `k := κ(y)`, `F := f.fiber y = X ×_Y Spec k`,
`q := f.fiberToSpecResidueField y : F ⟶ Spec k`. Then
`rank_y (f_* O_X) = dim_k Γ(F, O_F)`, where `rank_y M := dim_k (k ⊗_{O_{Y,y}} M_y)` (`Scheme.Modules.rankAtStalk`)
and `Γ(F, O_F)` is a `k`-module through `k ≅ Γ(Spec k, O) → Γ(F, O_F)`, i.e. `(ΓSpecIso k).inv ≫ q.appTop`.
No finiteness is needed: both sides are `dim_k` of isomorphic `k`-vector spaces (possibly infinite-dimensional,
in which case both `finrank`s are `0`).

Proof: see the module docstring — (A1) stalk of the quasi-coherent sheaf `f_*O_X` = localization of
`A = Γ(X, f⁻¹U)` at `p`, so `k ⊗_{O_{Y,y}} (f_*O_X)_y ≃ k ⊗_R A`; (A2) `Γ(F) ≃ k ⊗_R A` from the pushout of rings
attached to the fiber square over the affine opens `U`, `f⁻¹U`, `⊤`; (A3) compare `finrank`s.
Edge cases: `y ∉ f(X)` — then `A_p = 0`, `F = ∅`, `Γ(F) = 0`, both sides `0`; `X = ∅` is the same.
`Y` need not be Noetherian and `f` need not be flat or finite. -/
theorem Scheme.Hom.rankAtStalk_pushforward_unit_eq_finrank_fiber_sections {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] (y : Y) :
    Scheme.Modules.rankAtStalk
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) y
      = (letI := ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
            (f.fiberToSpecResidueField y).appTop).hom.toAlgebra
         Module.finrank (Y.residueField y) Γ(f.fiber y, ⊤)) := by
  -- notation
  set M : Y.Modules := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) with hM
  set k := Y.residueField y with hk
  set O := Y.presheaf.stalk y with hO
  set s := Y.fromSpecResidueField y with hs
  set q := f.fiberToSpecResidueField y with hq
  set ι := f.fiberι y with hι
  -- an affine open neighbourhood of y
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  -- (A1) the stalk of f_* O_X is the localization of A := Γ(X, f⁻¹U) at p
  have hqc : M.IsQuasicoherent :=
    haveI := Scheme.Modules.AffinePushforwardAux.isQuasicoherent_unit X
    Scheme.Modules.AffinePushforwardAux.isQuasicoherent_pushforward_of_isAffineHom f
      (SheafOfModules.unit X.ringCatSheaf)
  let _ : Module Γ(Y, U) (M.presheaf.stalk y) := M.stalkModuleSections U y hy
  have hloc := M.isLocalizedModule_germₗ_of_isQuasicoherent U y hy hU
  set p := hU.primeIdealOf ⟨y, hy⟩ with hp
  let _ : Algebra Γ(Y, U) O := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  have : IsLocalization p.asIdeal.primeCompl O := hU.isLocalization_stalk ⟨y, hy⟩
  have : IsScalarTower Γ(Y, U) O (M.presheaf.stalk y) :=
    ⟨fun r o m => by
      change (algebraMap Γ(Y, U) O r * o) • m = algebraMap Γ(Y, U) O r • (o • m)
      rw [mul_smul]⟩
  have hbc : IsBaseChange O (M.germₗ U y hy) :=
    IsLocalizedModule.isBaseChange p.asIdeal.primeCompl O (M.germₗ U y hy)
  let e₁ : O ⊗[Γ(Y, U)] Γ(M, U) ≃ₗ[O] M.presheaf.stalk y := hbc.equiv
  let _ : Algebra O k := (Y.residue y).hom.toAlgebra
  let _ : Algebra Γ(Y, U) k := (Y.presheaf.germ U y hy ≫ Y.residue y).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) O k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₂ : k ⊗[O] (O ⊗[Γ(Y, U)] Γ(M, U)) ≃ₗ[k] k ⊗[Γ(Y, U)] Γ(M, U) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(Y, U) O k k Γ(M, U)
  let e₃ : k ⊗[O] (O ⊗[Γ(Y, U)] Γ(M, U)) ≃ₗ[k] k ⊗[O] (M.presheaf.stalk y) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl k k) e₁
  -- (A2) Γ(F) is the pushout k ⊗[R] A of the fiber square over the affine opens U, f⁻¹U, ⊤
  have H : IsPullback ι q f s := IsPullback.of_hasPullback f s
  have hUST : (⊤ : (Spec k).Opens) ≤ s ⁻¹ᵁ U := by
    intro z _
    change s.base z ∈ U
    have hz : s.base z = y := Scheme.fromSpecResidueField_apply y z
    rw [hz]; exact hy
  have hUY : (⊤ : (f.fiber y).Opens) = ι ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ q ⁻¹ᵁ ⊤ := by
    refine le_antisymm (fun ξ _ => ⟨?_, trivial⟩) le_top
    change f.base (ι.base ξ) ∈ U
    have h1 : f.base (ι.base ξ) = s.base (q.base ξ) := by
      change (ι ≫ f).base ξ = (q ≫ s).base ξ
      rw [H.w]
    have h2 : s.base (q.base ξ) = y := Scheme.fromSpecResidueField_apply y (q.base ξ)
    rw [h1, h2]; exact hy
  have hι' : (⊤ : (f.fiber y).Opens) ≤ ι ⁻¹ᵁ (f ⁻¹ᵁ U) := hUY.le.trans inf_le_left
  have hP := (isIso_pushoutSection_iff H hUST le_rfl hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST le_rfl hUY hU (isAffineOpen_top _) (hU.preimage f))
  have hP' : IsPushout (Y.presheaf.germ U y hy ≫ Y.residue y) (f.app U)
      ((Scheme.ΓSpecIso k).inv ≫ q.appTop) (ι.appLE (f ⁻¹ᵁ U) ⊤ hι') := by
    refine hP.flip.of_iso (Iso.refl _) (Scheme.ΓSpecIso k) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp]
      exact Scheme.fromSpecResidueField_appLE_ΓSpecIso_hom y hy hUST
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact Scheme.Hom.appLE_eq_app f
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
      show q.appLE ⊤ (q ⁻¹ᵁ ⊤) le_rfl = _
      exact Scheme.Hom.appLE_eq_app q
    · simp
  let _ : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let _ : Algebra k Γ(f.fiber y, ⊤) := ((Scheme.ΓSpecIso k).inv ≫ q.appTop).hom.toAlgebra
  let _ : Algebra Γ(X, f ⁻¹ᵁ U) Γ(f.fiber y, ⊤) := (ι.appLE (f ⁻¹ᵁ U) ⊤ hι').hom.toAlgebra
  let _ : Algebra Γ(Y, U) Γ(f.fiber y, ⊤) := ((f.app U) ≫ ι.appLE (f ⁻¹ᵁ U) ⊤ hι').hom.toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(f.fiber y, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower Γ(Y, U) k Γ(f.fiber y, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hP'.w.symm)
  have hpo : Algebra.IsPushout Γ(Y, U) k Γ(X, f ⁻¹ᵁ U) Γ(f.fiber y, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hP'
  let e₄ : k ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[k] Γ(f.fiber y, ⊤) :=
    Algebra.IsPushout.equiv Γ(Y, U) k Γ(X, f ⁻¹ᵁ U) Γ(f.fiber y, ⊤)
  -- (A3) compare finranks
  show Module.finrank k (k ⊗[O] (M.stalk y)) = Module.finrank k Γ(f.fiber y, ⊤)
  have h1 : Module.finrank k (k ⊗[O] (M.stalk y))
      = Module.finrank k (k ⊗[O] (O ⊗[Γ(Y, U)] Γ(M, U))) := e₃.symm.finrank_eq
  have h2 : Module.finrank k (k ⊗[O] (O ⊗[Γ(Y, U)] Γ(M, U)))
      = Module.finrank k (k ⊗[Γ(Y, U)] Γ(M, U)) := e₂.finrank_eq
  have h3 : Module.finrank k (k ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U)) = Module.finrank k Γ(f.fiber y, ⊤) :=
    e₄.toLinearEquiv.finrank_eq
  rw [h1, h2, ← h3]
  rfl

end AlgebraicGeometry

end
