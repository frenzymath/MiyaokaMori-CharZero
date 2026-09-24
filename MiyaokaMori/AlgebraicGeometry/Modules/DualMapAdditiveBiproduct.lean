import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualMapFunctorial
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualCurryMap
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive

/-! # `dualMap` is additive; the dual of a finite biproduct

`dualMap g = dualCurry ((W^∨ ◁ g) ≫ ev_W)` (`dualMap_eq`) and `dualCurry` is a
bijection whose inverse is `ψ ↦ (ψ ▷ V) ≫ ev_V` (`dualCurry_symm_apply`). Since whiskering is additive in `X.Modules`
(`whiskerLeft_add'` / `add_whiskerRight'`) and composition is additive (`Preadditive`),
uncurrying both sides of `dualMap (f + g) = dualMap f + dualMap g` gives the same morphism, so `dualMap` is additive
(`dualMap_add`, `dualMap_zero`, `dualMap_sum`).

Consequence (`sum_dualMap_ι_comp_dualMap_π`): for a finite biproduct `⨁ f` in `X.Modules`,
`∑ j, (ι_j)^∨ ≫ (π_j)^∨ = (∑ j, π_j ≫ ι_j)^∨ = (𝟙)^∨ = 𝟙 (⨁ f)^∨` (`biproduct.total`, `dualMap_comp`, `dualMap_id`).
On sections (`eq_sum_dualMap_π_app`): every `w ∈ Γ(U, (⨁ f)^∨)` is `∑ j, (π_j)^∨ ((ι_j)^∨ w)` — "a functional on a
finite direct sum is the sum of its components" (Stacks 01CG-adjacent bookkeeping; the paper uses it as
`(⊕_j Q_j)^∨ = ⊕_j Q_j^∨`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `(f + g)^∨ = f^∨ + g^∨`. -/
theorem dualMap_add {V W : X.Modules} (f g : V ⟶ W) : dualMap (f + g) = dualMap f + dualMap g := by
  have hf : (dualMap f ▷ V) ≫ dualEv V = (dual W ◁ f) ≫ dualEv W := dualCurryMap_whiskerRight_ev f
  have hg : (dualMap g ▷ V) ≫ dualEv V = (dual W ◁ g) ≫ dualEv W := dualCurryMap_whiskerRight_ev g
  have e : (dual W ◁ (f + g)) ≫ dualEv W = ((dualMap f + dualMap g) ▷ V) ≫ dualEv V := by
    rw [whiskerLeft_add']
    erw [Preadditive.add_comp]
    rw [add_whiskerRight']
    erw [Preadditive.add_comp]
    rw [hf, hg]
  rw [dualMap_eq]
  exact (congrArg (dualCurry (dual W) V) e).trans (dualCurry_whiskerRight_ev (dual W) V _)

/-- `0^∨ = 0`. -/
theorem dualMap_zero (V W : X.Modules) : dualMap (0 : V ⟶ W) = 0 :=
  dualCurryMap_zero V W

/-- `dualMap` as an additive map `(V ⟶ W) →+ (W^∨ ⟶ V^∨)`. -/
def dualMapAddHom (V W : X.Modules) : (V ⟶ W) →+ (dual W ⟶ dual V) :=
  AddMonoidHom.mk' dualMap dualMap_add

theorem dualMapAddHom_apply {V W : X.Modules} (g : V ⟶ W) : dualMapAddHom V W g = dualMap g := rfl

/-- `(∑ j ∈ s, f j)^∨ = ∑ j ∈ s, (f j)^∨`. -/
theorem dualMap_sum {V W : X.Modules} {J : Type*} (s : Finset J) (f : J → (V ⟶ W)) :
    dualMap (∑ j ∈ s, f j) = ∑ j ∈ s, dualMap (f j) :=
  map_sum (dualMapAddHom V W) f s

/-- **Dual of a finite biproduct**: `∑ j, (ι_j)^∨ ≫ (π_j)^∨ = 𝟙 (⨁ f)^∨`. -/
theorem sum_dualMap_ι_comp_dualMap_π {J : Type} [Fintype J] (f : J → X.Modules) [HasBiproduct f] :
    ∑ j, dualMap (biproduct.ι f j) ≫ dualMap (biproduct.π f j) = 𝟙 (dual (⨁ f)) := by
  have h : ∀ j, dualMap (biproduct.ι f j) ≫ dualMap (biproduct.π f j) =
      dualMap (biproduct.π f j ≫ biproduct.ι f j) := fun j => (dualMap_comp _ _).symm
  rw [Finset.sum_congr rfl (fun j _ => h j), ← dualMap_sum, biproduct.total, dualMap_id]

/-- Application of a finite sum of morphisms of `𝒪_X`-modules to a section. (Private: the same fact is
`Hom.sum_app_apply` in `JetNeighborhoodZeroSectionSurjectiveNilpotent`, whose import closure is
far too large for this foundational helper.) -/
private theorem Hom.app_finset_sum_apply {M N : X.Modules} {J : Type*} (s : Finset J) (φ : J → (M ⟶ N)) (U : X.Opens)
    (x : Γ(M, U)) :
    (∑ j ∈ s, φ j).app U x = ∑ j ∈ s, (φ j).app U x := by
  let e : (M ⟶ N) →+ Γ(N, U) := AddMonoidHom.mk' (fun ψ => ψ.app U x) (fun ψ ψ' => rfl)
  exact map_sum e φ s

/-- **A section of `(⨁ f)^∨` is the sum of its components**: `w = ∑ j, (π_j)^∨ ((ι_j)^∨ w)`. -/
theorem eq_sum_dualMap_π_app {J : Type} [Fintype J] (f : J → X.Modules) [HasBiproduct f] (U : X.Opens)
    (w : Γ(dual (⨁ f), U)) :
    w = ∑ j, (dualMap (biproduct.π f j)).app U ((dualMap (biproduct.ι f j)).app U w) := by
  have h := congrArg (fun ψ : dual (⨁ f) ⟶ dual (⨁ f) => ψ.app U w) (sum_dualMap_ι_comp_dualMap_π f)
  simp only at h
  rw [Hom.app_finset_sum_apply] at h
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  rfl

end AlgebraicGeometry.Scheme.Modules

end
