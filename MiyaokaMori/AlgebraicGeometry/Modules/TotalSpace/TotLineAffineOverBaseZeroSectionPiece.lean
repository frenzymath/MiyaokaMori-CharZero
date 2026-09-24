import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecOfAlgebraMapSections
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalProjection

/-! # The zero section on functions of `Tot(V)|_W`

Used for the zero section of `Tot(L)` in `P(O ⊕ L)` (`zeroSection_toProjBundle_pieces`, `TotLineAffineOverBase`; in
the paper, "the section defined by the other summand `O` is the zero section of `Tot(L)`"; the zero section is the
augmentation; Stacks 01LQ).

Notation: `p : Tot(V) = Spec_X Sym(V^∨) → X`, `z = zeroSection V : X → Tot(V)` (`z ≫ p = 𝟙`, `z` is
`relativeSpec.ofAlgebraMap` of the augmentation `symAugmentation : Sym(V^∨) → O_X`), `W ⊆ X` open,
`z|_W : W → p⁻¹W` (`Scheme.Hom.resLE`), and `z^♯ : Γ(p⁻¹W, O_Tot) → Γ(W, O_X)` its ring map on global sections
(through `Opens.topIso`).

* `zeroSection_preimage_preimage`: `z⁻¹(p⁻¹W) = W`.
* `zeroSection_resLE_appTop_topIso_inv_app` (**degree zero**): `z^♯(p^♯ r) = r` (`z ≫ p = 𝟙`).
* `zeroSection_resLE_appTop_topIso_inv_structureHom_totalIncl_one` (**degree one**): `z^♯` kills the fibre coordinates
  `structureHom (totalIncl 1 (symGen n))`, `n ∈ Γ(W, V^∨)`: by `relativeSpec.ofAlgebraMap_appLE_structureHom`
  (Stacks 01LQ, the defining property of `ofAlgebraMap`) `z^♯ ∘ structureHom` is the augmentation, which vanishes in
  degree one (`symAugmentation_app_ι_app`).

-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.totalSpace

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (W : X.Opens)

/-- `z⁻¹(p⁻¹W) = W`. -/
theorem zeroSection_preimage_preimage :
    zeroSection V ⁻¹ᵁ ((totalSpace V).hom ⁻¹ᵁ W) = W := by
  rw [← Scheme.Hom.comp_preimage, zeroSection_comp]
  rfl

theorem le_zeroSection_preimage : W ≤ zeroSection V ⁻¹ᵁ ((totalSpace V).hom ⁻¹ᵁ W) :=
  (zeroSection_preimage_preimage V W).ge

/-- `topIso.hom ∘ topIso.inv = id` on `Γ(U, O)`. -/
theorem topIso_hom_topIso_inv_apply {Y : AlgebraicGeometry.Scheme.{u}} (U : Y.Opens) (y : Γ(Y, U)) :
    U.topIso.hom.hom (U.topIso.inv.hom y) = y := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

/-- Two restriction maps of `O_X` between the same open (up to defeq) compose to the identity. -/
theorem presheaf_map_map_of_eq (U U' : X.Opens) (h : U' = U) (i : op U ⟶ op U') (j : op U' ⟶ op U)
    (x : Γ(X, U)) : (X.presheaf.map j).hom ((X.presheaf.map i).hom x) = x := by
  subst h
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _),
    CategoryTheory.Functor.map_id]
  rfl

/-- **Degree zero**: `z^♯(p^♯ r) = r`. -/
theorem zeroSection_resLE_appTop_topIso_inv_app (r : Γ(X, W)) :
    ((zeroSection V).resLE ((totalSpace V).hom ⁻¹ᵁ W) W (le_zeroSection_preimage V W)).appTop.hom
        (((totalSpace V).hom ⁻¹ᵁ W).topIso.inv.hom ((totalSpace V).hom.app W r)) =
      W.topIso.inv.hom r := by
  show ((((zeroSection V).resLE ((totalSpace V).hom ⁻¹ᵁ W) W (le_zeroSection_preimage V W)).app ⊤).hom
    (((totalSpace V).hom ⁻¹ᵁ W).topIso.inv.hom ((totalSpace V).hom.app W r))) = _
  rw [Scheme.Hom.resLE_app_top]
  change W.topIso.inv.hom (((zeroSection V).appLE ((totalSpace V).hom ⁻¹ᵁ W) W (le_zeroSection_preimage V W)).hom
    (((totalSpace V).hom ⁻¹ᵁ W).topIso.hom.hom (((totalSpace V).hom ⁻¹ᵁ W).topIso.inv.hom
      ((totalSpace V).hom.app W r)))) = _
  rw [topIso_hom_topIso_inv_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  unfold Scheme.Hom.appLE
  rw [Scheme.Hom.congr_app (zeroSection_comp V)]
  change (X.presheaf.map (homOfLE _).op).hom ((X.presheaf.map (CategoryTheory.eqToHom _).op).hom r) = r
  exact presheaf_map_map_of_eq W ((zeroSection V ≫ (totalSpace V).hom) ⁻¹ᵁ W) (by rw [zeroSection_comp]; rfl) _ _ r

/-- **Degree one**: `z^♯` kills `structureHom (totalIncl 1 (symGen n))`. -/
theorem zeroSection_resLE_appTop_topIso_inv_structureHom_totalIncl_one (n : Γ(dual V, W)) :
    ((zeroSection V).resLE ((totalSpace V).hom ⁻¹ᵁ W) W (le_zeroSection_preimage V W)).appTop.hom
        (((totalSpace V).hom ⁻¹ᵁ W).topIso.inv.hom
          ((relativeSpec.structureHom (symGradedAlgebra (dual V)).total).app W
            ((symGen (dual V) ≫ (symGradedAlgebra (dual V)).totalIncl 1).app W n))) = 0 := by
  show ((((zeroSection V).resLE ((totalSpace V).hom ⁻¹ᵁ W) W (le_zeroSection_preimage V W)).app ⊤).hom
    (((totalSpace V).hom ⁻¹ᵁ W).topIso.inv.hom _)) = 0
  rw [Scheme.Hom.resLE_app_top]
  change W.topIso.inv.hom (((zeroSection V).appLE ((totalSpace V).hom ⁻¹ᵁ W) W (le_zeroSection_preimage V W)).hom
    (((totalSpace V).hom ⁻¹ᵁ W).topIso.hom.hom (((totalSpace V).hom ⁻¹ᵁ W).topIso.inv.hom
      ((relativeSpec.structureHom (symGradedAlgebra (dual V)).total).app W
        ((symGen (dual V) ≫ (symGradedAlgebra (dual V)).totalIncl 1).app W n))))) = 0
  rw [topIso_hom_topIso_inv_apply]
  refine Eq.trans (congrArg W.topIso.inv.hom ?_) (map_zero _)
  -- `z = ofAlgebraMap (symAugmentation ≫ pushforwardId⁻¹)`; Stacks 01LQ evaluates `z^♯ ∘ structureHom`
  have h := relativeSpec.ofAlgebraMap_appLE_structureHom (symGradedAlgebra (dual V)).total
    (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X))
    (symAugmentation (dual V) ≫ (pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf))
    (symAugmentation_isAlgebraMap (dual V)) W
    ((symGen (dual V) ≫ (symGradedAlgebra (dual V)).totalIncl 1).app W n) (le_zeroSection_preimage V W)
  refine h.trans ?_
  show ((pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)).app W
    ((symAugmentation (dual V)).app W
      ((Sigma.ι (symGradedAlgebra (dual V)).part 1).app W ((symGen (dual V)).app W n))) = 0
  rw [symAugmentation_app_ι_app, map_zero]

end AlgebraicGeometry.Scheme.totalSpace

end
