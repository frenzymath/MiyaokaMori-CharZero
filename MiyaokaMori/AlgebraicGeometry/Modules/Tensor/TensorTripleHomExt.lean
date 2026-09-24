import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowIsoSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence

/-! # Morphisms out of `A ⊗ (B ⊗ C)` are determined on `a ⊗ (b ⊗ c)`

`tensorObj_hom_ext` (`Stacks01cmTensorHom`) says that a morphism `F ⊗ G ⟶ H` of sheaves of modules
is determined by its values on the section pairings `tensorSections F G U s t`, `t ∈ Γ(G, U)` arbitrary. For
`G = B ⊗ C` this is not yet a statement about pure tensors: `Γ(B ⊗ C, U)` is the sheafification of the presheaf tensor
product, so a section `t` is only **locally** the image `τ (η z)` of an element `z` of the presheaf tensor product
`B(V) ⊗_{O(V)} C(V)` (Mathlib `Presheaf.imageSieve_mem` for `toSheafify`: `exists_tensorObj_section_locally_unit`),
and `z` is a finite sum of `b ⊗ₜ c`.

**Theorem** `tensorObj_tensorObj_hom_ext_right`: if `f g : A ⊗ (B ⊗ C) ⟶ K` agree on all
`tensorSections a (tensorSections b c)` over all opens, then `f = g`. Proof: `tensorObj_hom_ext`; fix `U`, `a`, `t`;
cover `U` by opens `V x` on which `t` is `τ (η (z x))`; restriction commutes with `f`, `g`
(`PresheafOfModules.naturality_apply`) and with `tensorSections` (`tensorSections_restrict`); on `V x` induct on
`z x` (`TensorProduct.induction_on`: zero, pure tensor = hypothesis, sum = additivity of `η`, `τ`, `tensorSections`
(`tensorSections_add_right`) and of `f`, `g`); conclude by separatedness of `K` (`TopCat.Sheaf.eq_of_locally_eq'`).
Same pattern as `tensorObj_hom_ext_of_isAffineOpen` (`SymCoeffHomMulHomogeneousAux`).

Also the generic section calculus used together with it (morphisms as variables, so that the concrete instantiation
elaborates cheaply): `whiskerLeft_comp_app_tensorSections`, `associator_inv_whiskerRight_comp_app_tensorSections`,
`eqToHom_app_self`, `eqToHom_app_eqToHom_app`.

Used for the morphism-level associativity of `twistMul` (`twistPairMul_assoc`).

Source: standard (sheafification is locally surjective).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The sheafification unit on the presheaf tensor product of the underlying presheaves. -/
abbrev tensorPreUnit (B C : X.Modules) (U : X.Opens) :
    (toPre B ⊗ toPre C).obj (op U) ⟶
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (toPre B ⊗ toPre C)).val.obj (op U) :=
  ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (toPre B ⊗ toPre C)).app (op U)

/-- `τ (η (b ⊗ₜ c)) = tensorSections b c` (definitional). -/
theorem tensorIsoTensorObj_hom_app_unit_tmul (B C : X.Modules) (U : X.Opens) (b : Γ(B, U)) (c : Γ(C, U)) :
    (tensorIsoTensorObj B C).hom.app U (tensorPreUnit B C U (b ⊗ₜ c)) = tensorSections B C U b c := rfl

/-- A section of `B ⊗ C` is locally `τ (η z)` for `z` in the presheaf tensor product. -/
theorem exists_tensorObj_section_locally_unit (B C : X.Modules) (U : X.Opens)
    (t : Γ(CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C, U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ z : (toPre B ⊗ toPre C).obj (op V),
      (tensorIsoTensorObj B C).hom.app V (tensorPreUnit B C V z) =
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C).val.map (homOfLE hVU).op t := by
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (toPre B ⊗ toPre C).presheaf)
    ((tensorIsoTensorObj B C).inv.app U t)
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨V, i, ⟨z, hz⟩, hxV⟩ := hmem x hx
  refine ⟨V, leOfHom i, hxV, z, ?_⟩
  have hz' : tensorPreUnit B C V z =
      (AlgebraicGeometry.Scheme.Modules.tensor B C).val.map (homOfLE (leOfHom i)).op
        ((tensorIsoTensorObj B C).inv.app U t) := hz
  have hnat : (tensorIsoTensorObj B C).hom.app V
      ((AlgebraicGeometry.Scheme.Modules.tensor B C).val.map (homOfLE (leOfHom i)).op
        ((tensorIsoTensorObj B C).inv.app U t)) =
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C).val.map (homOfLE (leOfHom i)).op
        ((tensorIsoTensorObj B C).hom.app U ((tensorIsoTensorObj B C).inv.app U t)) :=
    _root_.PresheafOfModules.naturality_apply (tensorIsoTensorObj B C).hom.val (homOfLE (leOfHom i)).op _
  have hii : (tensorIsoTensorObj B C).hom.app U ((tensorIsoTensorObj B C).inv.app U t) = t :=
    congrArg (fun φ : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C ⟶ _ => φ.app U t)
      (tensorIsoTensorObj B C).inv_hom_id
  rw [hz', hnat, hii]

private theorem tensorSections_zero_right' (A B : X.Modules) (U : X.Opens) (a : Γ(A, U)) :
    tensorSections A B U a 0 = 0 := by
  have h := tensorSections_add_right A B U a 0 0
  rw [zero_add] at h
  have h2 : tensorSections A B U a 0 + tensorSections A B U a 0 = tensorSections A B U a 0 + 0 := by
    rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- **Morphisms out of `A ⊗ (B ⊗ C)` are determined by their values on `a ⊗ (b ⊗ c)`.** -/
theorem tensorObj_tensorObj_hom_ext_right {A B C K : X.Modules}
    {f g : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C) ⟶ K}
    (h : ∀ (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)),
      f.app U (tensorSections A _ U a (tensorSections B C U b c)) =
        g.app U (tensorSections A _ U a (tensorSections B C U b c))) :
    f = g := by
  classical
  apply tensorObj_hom_ext
  intro U a t
  have hloc : ∀ x : (U : Set X), ∃ (V : X.Opens) (hVU : V ≤ U), (x : X) ∈ V ∧
      ∃ z : (toPre B ⊗ toPre C).obj (op V),
        (tensorIsoTensorObj B C).hom.app V (tensorPreUnit B C V z) =
          (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C).val.map (homOfLE hVU).op t :=
    fun x => exists_tensorObj_section_locally_unit B C U t x x.2
  choose V hVU hxV z hz using hloc
  let Sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨K.val.presheaf, K.isSheaf⟩
  refine Sh.eq_of_locally_eq' V U (fun x => homOfLE (hVU x)) (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
    _ _ (fun x => ?_)
  show K.val.map (homOfLE (hVU x)).op ((f.val.app (op U)).hom (tensorSections A _ U a t)) =
    K.val.map (homOfLE (hVU x)).op ((g.val.app (op U)).hom (tensorSections A _ U a t))
  have h3 : (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C)).val.map (homOfLE (hVU x)).op
        (tensorSections A _ U a t) =
      tensorSections A _ (V x) (A.val.map (homOfLE (hVU x)).op a)
        ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C).val.map (homOfLE (hVU x)).op t) :=
    tensorSections_restrict A _ (homOfLE (hVU x)) a t
  have key : ∀ w : (toPre B ⊗ toPre C).obj (op (V x)),
      f.app (V x) (tensorSections A _ (V x) (A.val.map (homOfLE (hVU x)).op a)
        ((tensorIsoTensorObj B C).hom.app (V x) (tensorPreUnit B C (V x) w))) =
      g.app (V x) (tensorSections A _ (V x) (A.val.map (homOfLE (hVU x)).op a)
        ((tensorIsoTensorObj B C).hom.app (V x) (tensorPreUnit B C (V x) w))) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => erw [map_zero, map_zero, tensorSections_zero_right', map_zero, map_zero]
    | tmul b c => exact h (V x) _ b c
    | add w₁ w₂ h₁ h₂ => erw [map_add, map_add, tensorSections_add_right, map_add, map_add, h₁, h₂]
  rw [← _root_.PresheafOfModules.naturality_apply f.val, ← _root_.PresheafOfModules.naturality_apply g.val, h3,
    ← hz x]
  exact key (z x)


/-! ### Generic section calculus for the associativity computation -/

/-- `(eqToHom h).app U w = w` for `h : M = M`. -/
theorem eqToHom_app_self' {M : X.Modules} (h : M = M) (U : X.Opens) (w : Γ(M, U)) :
    (CategoryTheory.eqToHom h).app U w = w := by
  rw [CategoryTheory.eqToHom_refl]; rfl

/-- Two inverse `eqToHom`s cancel on sections. -/
theorem eqToHom_app_eqToHom_app {M N : X.Modules} (h₁ : M = N) (h₂ : N = M) (U : X.Opens) (w : Γ(M, U)) :
    (CategoryTheory.eqToHom h₂).app U ((CategoryTheory.eqToHom h₁).app U w) = w := by
  subst h₁; rw [CategoryTheory.eqToHom_refl]; rfl

/-- The right whiskering on a section pairing. -/
private theorem whiskerRight_app_tensorSections_tte {A A' B : X.Modules} (f : A ⟶ A') (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) :
    (f ▷ B).app U (tensorSections A B U x y) = tensorSections A' B U (f.app U x) y := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id]
  exact tensorHom_tensorSections f (𝟙 B) U x y

/-- The inverse associator on `x ⊗ (y ⊗ z)`. -/
theorem associator_inv_app_tensorSections (A B C : X.Modules) (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U))
    (z : Γ(C, U)) :
    (α_ A B C).inv.app U (tensorSections A _ U x (tensorSections B C U y z)) =
      tensorSections _ C U (tensorSections A B U x y) z := by
  have h1 := congrArg (fun φ : (A ⊗ B) ⊗ C ⟶ (A ⊗ B) ⊗ C =>
    φ.app U (tensorSections _ C U (tensorSections A B U x y) z)) (α_ A B C).hom_inv_id
  rw [← associator_app_tensorSections]
  exact h1

/-- `((A ◁ (f ≫ e)) ≫ g ≫ e')` on `x ⊗ (y ⊗ z)`, evaluated. -/
theorem whiskerLeft_comp_app_tensorSections {A B C D D' E E' : X.Modules}
    (f : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C ⟶ D) (e : D ⟶ D')
    (g : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A D' ⟶ E) (e' : E ⟶ E')
    (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) (z : Γ(C, U)) :
    ((A ◁ (f ≫ e)) ≫ g ≫ e').app U (tensorSections A _ U x (tensorSections B C U y z)) =
      e'.app U (g.app U (tensorSections A D' U x (e.app U (f.app U (tensorSections B C U y z))))) := by
  exact congrArg (fun w => e'.app U (g.app U w))
    (whiskerLeft_app_tensorSections A (f ≫ e) U x (tensorSections B C U y z))

/-- `(α⁻¹ ≫ ((f ≫ e) ▷ C) ≫ g ≫ e')` on `x ⊗ (y ⊗ z)`, evaluated. -/
theorem associator_inv_whiskerRight_comp_app_tensorSections {A B C D D' E E' : X.Modules}
    (f : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B ⟶ D) (e : D ⟶ D')
    (g : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) D' C ⟶ E) (e' : E ⟶ E')
    (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) (z : Γ(C, U)) :
    ((α_ A B C).inv ≫ ((f ≫ e) ▷ C) ≫ g ≫ e').app U (tensorSections A _ U x (tensorSections B C U y z)) =
      e'.app U (g.app U (tensorSections D' C U (e.app U (f.app U (tensorSections A B U x y))) z)) := by
  exact (congrArg (fun w => e'.app U (g.app U (((f ≫ e) ▷ C).app U w)))
      (associator_inv_app_tensorSections A B C U x y z)).trans
    (congrArg (fun w => e'.app U (g.app U w))
      (whiskerRight_app_tensorSections_tte (f ≫ e) U (tensorSections A B U x y) z))


/-- **Associativity-shaped equality of morphisms out of `A ⊗ (B ⊗ C)` from a section-level identity**:
`(A ◁ (f ≫ e)) ≫ g ≫ e' = α⁻¹ ≫ ((f'' ≫ e'') ▷ C) ≫ g'' ≫ e'''` as soon as both sides agree on all `x ⊗ (y ⊗ z)`
(the two evaluations are `whiskerLeft_comp_app_tensorSections`, `associator_inv_whiskerRight_comp_app_tensorSections`). -/
theorem assoc_of_app_tensorSections {A B C D D' E S S' E' F : X.Modules}
    (f : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C ⟶ D) (e : D ⟶ D')
    (g : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A D' ⟶ E) (e' : E ⟶ F)
    (f'' : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B ⟶ S) (e'' : S ⟶ S')
    (g'' : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) S' C ⟶ E') (e''' : E' ⟶ F)
    (h : ∀ (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) (z : Γ(C, U)),
      e'.app U (g.app U (tensorSections A D' U x (e.app U (f.app U (tensorSections B C U y z))))) =
        e'''.app U (g''.app U (tensorSections S' C U (e''.app U (f''.app U (tensorSections A B U x y))) z))) :
    (A ◁ (f ≫ e)) ≫ g ≫ e' = (α_ A B C).inv ≫ ((f'' ≫ e'') ▷ C) ≫ g'' ≫ e''' := by
  apply tensorObj_tensorObj_hom_ext_right
  intro U x y z
  rw [whiskerLeft_comp_app_tensorSections, associator_inv_whiskerRight_comp_app_tensorSections]
  exact h U x y z

end AlgebraicGeometry.Scheme.Modules

end
