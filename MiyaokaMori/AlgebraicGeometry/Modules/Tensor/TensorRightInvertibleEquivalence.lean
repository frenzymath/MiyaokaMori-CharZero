import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Tensoring with an invertible object is an equivalence

(1) In a monoidal category `C`, if an object `L` is invertible (there are isomorphisms
`u : L ⊗ Lᵛ ≅ 𝟙_C` and `u' : Lᵛ ⊗ L ≅ 𝟙_C`), then `− ⊗ L` (`MonoidalCategory.tensorRight L`) is a
self-equivalence of `C` with quasi-inverse `− ⊗ Lᵛ`. (2) A line bundle `L` on a scheme `X`
(`[L.IsLineBundle]`) is invertible in `X.Modules`, so `− ⊗ L` is a self-equivalence of `X.Modules`; in
particular it preserves finite limits and colimits and is exact.

Proof:
1. Right tensoring is functorial in isomorphisms of objects: `e : A ≅ B` gives a natural isomorphism
   `tensorRight A ≅ tensorRight B` (components `Z ◁ e`, naturality is `whisker_exchange`).
2. Mathlib's `MonoidalCategory.tensorRightTensor L Lᵛ : tensorRight (L ⊗ Lᵛ) ≅ tensorRight L ⋙ tensorRight Lᵛ`
   (components the associators) and `rightUnitorNatIso C : tensorRight (𝟙_C) ≅ 𝟭 C` (components the
   right unitors). Transporting `u`, `u'` through step 1 gives natural isomorphisms
   `𝟭 ≅ (−⊗L) ⋙ (−⊗Lᵛ)` and `(−⊗Lᵛ) ⋙ (−⊗L) ≅ 𝟭`, and `CategoryTheory.Equivalence.mk` gives the
   equivalence (Mathlib's `mk` does not require the triangle identities; it corrects them with
   `adjointifyη`).
3. Line bundles are invertible: `SheafOfModules.IsLineBundle.tensor_dual_iso` (Stacks 01CT) gives
   `Scheme.Modules.tensor L (dual L) ≅ SheafOfModules.unit`; `tensorIsoTensorObj` passes from
   `Scheme.Modules.tensor` to the monoidal `⊗`, `unit_eq_tensorUnit` from the structure sheaf to `𝟙_`;
   on the other side the braiding `β_` of the symmetric structure on `X.Modules` turns `Lᵛ ⊗ L` into
   `L ⊗ Lᵛ`.
4. An equivalence preserves all limits and colimits (Mathlib instances) and is additive, hence
   preserves zero morphisms; so `ShortComplex.ShortExact.map_of_exact` applies.

Source: Stacks 01CT (invertible sheaves); the fact that tensoring with an invertible object is an
equivalence is standard.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An isomorphism of objects induces `− ⊗ A ≅ − ⊗ B`. -/
def tensorRightMapIso {A B : C} (e : A ≅ B) : tensorRight A ≅ tensorRight B :=
  NatIso.ofComponents (fun Z => whiskerLeftIso Z e) (by
    intro Z Z' f
    simpa using (whisker_exchange f e.hom).symm)

/-- Right tensoring with an invertible object is a self-equivalence. -/
def tensorRightEquivalenceOfInvertible {L Ld : C} (u : L ⊗ Ld ≅ 𝟙_ C) (u' : Ld ⊗ L ≅ 𝟙_ C) :
    C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight Ld)
    ((rightUnitorNatIso C).symm ≪≫ tensorRightMapIso u.symm ≪≫ tensorRightTensor L Ld)
    ((tensorRightTensor Ld L).symm ≪≫ tensorRightMapIso u' ≪≫ rightUnitorNatIso C)

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A line bundle is invertible for the monoidal structure: `L ⊗ L^∨ ≅ 𝟙_`. -/
theorem nonempty_tensorObj_dual_iso_tensorUnit (L : X.Modules) [L.IsLineBundle] :
    Nonempty ((L ⊗ AlgebraicGeometry.Scheme.Modules.dual L) ≅ 𝟙_ X.Modules) := by
  obtain ⟨e⟩ := SheafOfModules.IsLineBundle.tensor_dual_iso L
  exact ⟨(AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L _).symm ≪≫ e ≪≫
    eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)⟩

/-- Tensoring with a line bundle, `− ⊗ L`, is a self-equivalence of `X.Modules`; in particular it
preserves finite limits and finite colimits and is exact. -/
theorem isEquivalence_tensorRight_of_isLineBundle (L : X.Modules) [L.IsLineBundle] :
    (CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence := by
  obtain ⟨u⟩ := nonempty_tensorObj_dual_iso_tensorUnit L
  have u' : (AlgebraicGeometry.Scheme.Modules.dual L ⊗ L) ≅ 𝟙_ X.Modules := β_ _ _ ≪≫ u
  exact (CategoryTheory.MonoidalCategory.tensorRightEquivalenceOfInvertible u
    u').isEquivalence_functor

end AlgebraicGeometry.Scheme.Modules

end
