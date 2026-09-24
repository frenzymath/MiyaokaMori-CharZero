import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualCurry
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalZero

/-! # The dual of a morphism in the `dual` world

**The dual of a morphism, spelled entirely in the `dual` world, and its functoriality.**

`dualCurryMap g : W^∨ ⟶ V^∨` (for `g : V ⟶ W`) is `dualCurry (W^∨) V ((W^∨ ◁ g) ≫ dualEv W)`: the
currying of "evaluate after `g`" (`φ ↦ φ ∘ g`), using the `dual`-spelled evaluation `dualEv` and currying
`dualCurry` of `ModulesDualCurry`. It is the same morphism as `Modules.dualMap g` (`ModulesDualMap`):
`dualMap g` is literally the same term with `dualEv W` replaced by `internalHomEval W O_X`, and
`dualEv W` is `internalHomEval W O_X` transported along the definitional equality
`dual W = internalHom W O_X` (`dual_eq_internalHom`). That identification is *not* proved here:
checking `dual W ≡ internalHom W O_X` costs several seconds per occurrence (see the header of
`ModulesDualCurry`); the bridging lemma is `dualMap_eq` in `ModulesDualMapFunctorial`, so
`dualCurryMap` can be eliminated by `rw [← dualMap_eq]`.

Everything below is formal (Stacks 01CM, tensor–Hom adjunction), and every rewrite is syntactic:

* `dualCurryMap_whiskerRight_ev`: uncurrying, `(dualCurryMap g ▷ V) ≫ dualEv V = (W^∨ ◁ g) ≫ dualEv W`
  (`dualCurry_symm_apply` + `Equiv.symm_apply_apply`).
* `dualCurryMap_id`: `W^∨ ◁ 𝟙 ≫ ev = ev = (𝟙 ▷ W) ≫ ev`, then `dualCurry_whiskerRight_ev`.
* `dualCurryMap_comp`: `dualCurryMap h ≫ dualCurry (…) = dualCurry ((dualCurryMap h ▷ V) ≫ (W^∨ ◁ g) ≫ ev_W)`
  (`dualCurry_naturality_left`); exchange the whiskerings (`whisker_exchange`) and uncurry
  `dualCurryMap h` to get `dualCurry ((Z^∨ ◁ g) ≫ (Z^∨ ◁ h) ≫ ev_Z) = dualCurryMap (g ≫ h)`.
* `dualCurryMap_zero`: `W^∨ ◁ 0 = 0` (`Modules.whiskerLeft_zeroMorphism`) and
  `0 ▷ V = 0` (`Modules.zeroMorphism_whiskerRight`), so both sides uncurry to `0`.
* Binary biproducts `A ⊞ B`: `dualCurryMap fst ≫ dualCurryMap inl = dualCurryMap (inl ≫ fst) = 𝟙`,
  `dualCurryMap fst ≫ dualCurryMap inr = dualCurryMap (inr ≫ fst) = dualCurryMap 0 = 0`, etc.; hence
  `dualCurryMap inl`, `dualCurryMap inr` are split epimorphisms.

Needed for `totalSpace.toProjBundleQuotient` and its epimorphism property
`toProjBundleQuotient_epi`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The dual `W^∨ ⟶ V^∨` of `g : V ⟶ W`, `φ ↦ φ ∘ g`, spelled in the `dual` world
(same morphism as `dualMap g`, see the module docstring). -/
def dualCurryMap {V W : X.Modules} (g : V ⟶ W) : dual W ⟶ dual V :=
  dualCurry (dual W) V ((dual W ◁ g) ≫ dualEv W)

/-- Uncurried form: `(dualCurryMap g ▷ V) ≫ ev_V = (W^∨ ◁ g) ≫ ev_W`. -/
theorem dualCurryMap_whiskerRight_ev {V W : X.Modules} (g : V ⟶ W) :
    (dualCurryMap g ▷ V) ≫ dualEv V = (dual W ◁ g) ≫ dualEv W := by
  unfold dualCurryMap
  rw [← dualCurry_symm_apply, Equiv.symm_apply_apply]

/-- `dualCurryMap (𝟙 V) = 𝟙 (V^∨)`. -/
theorem dualCurryMap_id (V : X.Modules) : dualCurryMap (𝟙 V) = 𝟙 (dual V) := by
  unfold dualCurryMap
  have h : (dual V ◁ 𝟙 V) ≫ dualEv V = (𝟙 (dual V) ▷ V) ≫ dualEv V := by
    rw [whiskerLeft_id, id_whiskerRight]
  exact (congrArg (dualCurry (dual V) V) h).trans (dualCurry_whiskerRight_ev (dual V) V _)

/-- `dualCurryMap (g ≫ h) = dualCurryMap h ≫ dualCurryMap g`. -/
theorem dualCurryMap_comp {V W Z : X.Modules} (g : V ⟶ W) (h : W ⟶ Z) :
    dualCurryMap (g ≫ h) = dualCurryMap h ≫ dualCurryMap g := by
  conv_rhs => unfold dualCurryMap
  rw [dualCurry_naturality_left]
  have e : (dualCurryMap h ▷ V) ≫ (dual W ◁ g) ≫ dualEv W = (dual Z ◁ (g ≫ h)) ≫ dualEv Z := by
    calc (dualCurryMap h ▷ V) ≫ (dual W ◁ g) ≫ dualEv W
        = ((dualCurryMap h ▷ V) ≫ (dual W ◁ g)) ≫ dualEv W := (Category.assoc _ _ _).symm
      _ = ((dual Z ◁ g) ≫ (dualCurryMap h ▷ W)) ≫ dualEv W := by rw [whisker_exchange]
      _ = (dual Z ◁ g) ≫ (dualCurryMap h ▷ W) ≫ dualEv W := Category.assoc _ _ _
      _ = (dual Z ◁ g) ≫ (dual Z ◁ h) ≫ dualEv Z := by rw [dualCurryMap_whiskerRight_ev h]
      _ = (dual Z ◁ (g ≫ h)) ≫ dualEv Z :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun t => t ≫ dualEv Z) (whiskerLeft_comp (dual Z) g h).symm)
  exact (congrArg (dualCurry (dual Z) V) e).symm

/-- `dualCurryMap 0 = 0`. -/
theorem dualCurryMap_zero (V W : X.Modules) : dualCurryMap (0 : V ⟶ W) = 0 := by
  unfold dualCurryMap
  rw [whiskerLeft_zeroMorphism]
  have h1 : (0 : dual W ⊗ V ⟶ dual W ⊗ W) ≫ dualEv W = ((0 : dual W ⟶ dual V) ▷ V) ≫ dualEv V := by
    rw [zeroMorphism_whiskerRight]
    exact zero_comp.trans zero_comp.symm
  exact (congrArg (dualCurry (dual W) V) h1).trans (dualCurry_whiskerRight_ev (dual W) V 0)

section Biproduct

variable (A B : X.Modules) [HasBinaryBiproduct A B]

/-- `dualCurryMap fst ≫ dualCurryMap inl = 𝟙 (A^∨)`. -/
theorem dualCurryMap_fst_comp_inl :
    dualCurryMap (biprod.fst : A ⊞ B ⟶ A) ≫ dualCurryMap (biprod.inl : A ⟶ A ⊞ B) = 𝟙 (dual A) := by
  rw [← dualCurryMap_comp, biprod.inl_fst, dualCurryMap_id]

/-- `dualCurryMap snd ≫ dualCurryMap inr = 𝟙 (B^∨)`. -/
theorem dualCurryMap_snd_comp_inr :
    dualCurryMap (biprod.snd : A ⊞ B ⟶ B) ≫ dualCurryMap (biprod.inr : B ⟶ A ⊞ B) = 𝟙 (dual B) := by
  rw [← dualCurryMap_comp, biprod.inr_snd, dualCurryMap_id]

/-- `dualCurryMap fst ≫ dualCurryMap inr = 0`. -/
theorem dualCurryMap_fst_comp_inr :
    dualCurryMap (biprod.fst : A ⊞ B ⟶ A) ≫ dualCurryMap (biprod.inr : B ⟶ A ⊞ B) = 0 := by
  rw [← dualCurryMap_comp, biprod.inr_fst, dualCurryMap_zero]

/-- `dualCurryMap snd ≫ dualCurryMap inl = 0`. -/
theorem dualCurryMap_snd_comp_inl :
    dualCurryMap (biprod.snd : A ⊞ B ⟶ B) ≫ dualCurryMap (biprod.inl : A ⟶ A ⊞ B) = 0 := by
  rw [← dualCurryMap_comp, biprod.inl_snd, dualCurryMap_zero]

/-- `dualCurryMap inl : (A ⊕ B)^∨ ⟶ A^∨` is a split epimorphism (section `dualCurryMap fst`). -/
theorem dualCurryMap_inl_isSplitEpi : IsSplitEpi (dualCurryMap (biprod.inl : A ⟶ A ⊞ B)) :=
  IsSplitEpi.mk' ⟨dualCurryMap (biprod.fst : A ⊞ B ⟶ A), dualCurryMap_fst_comp_inl A B⟩

/-- `dualCurryMap inr : (A ⊕ B)^∨ ⟶ B^∨` is a split epimorphism (section `dualCurryMap snd`). -/
theorem dualCurryMap_inr_isSplitEpi : IsSplitEpi (dualCurryMap (biprod.inr : B ⟶ A ⊞ B)) :=
  IsSplitEpi.mk' ⟨dualCurryMap (biprod.snd : A ⊞ B ⟶ B), dualCurryMap_snd_comp_inr A B⟩

/-- `dualCurryMap inl` is an epimorphism. -/
theorem dualCurryMap_inl_epi : Epi (dualCurryMap (biprod.inl : A ⟶ A ⊞ B)) :=
  haveI := dualCurryMap_inl_isSplitEpi A B
  IsSplitEpi.epi _

/-- `dualCurryMap inr` is an epimorphism. -/
theorem dualCurryMap_inr_epi : Epi (dualCurryMap (biprod.inr : B ⟶ A ⊞ B)) :=
  haveI := dualCurryMap_inr_isSplitEpi A B
  IsSplitEpi.epi _

end Biproduct

end AlgebraicGeometry.Scheme.Modules

end
