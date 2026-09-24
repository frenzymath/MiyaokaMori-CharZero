import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SchemeModulesPullbackFreeIso
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra

/-! # Compatibility of the pullback of the weighted polynomial algebra with multiplication and unit

The canonical pullback isomorphisms of the free sheaves underlying the weighted polynomial algebra
are compatible with the monomial multiplication and with the unit.

Proof: (1) expand the multiplication as `freeTensorFreeIso` followed by the index map (addition of
exponents) and use the naturality of the strong monoidal structure of the pullback; (2) check on the
generators of the free sheaves — pullback preserves `ιFree`, and the index map is still addition of
exponents; (3) the unit case likewise, on the generator of the zero monomial.

The key lemma is `μ_map_freeTensorFreeIso_hom_pullbackObjFreeIso_hom`:
`μ ≫ g^*(freeTensorFreeIso.hom) ≫ pullbackObjFreeIso.hom = (pullbackObjFreeIso.hom ⊗ pullbackObjFreeIso.hom) ≫ freeTensorFreeIso.hom`.
Both sides are reduced by two isomorphisms to morphisms out of `free (I × J)` and compared on the
generators `ιFree (a, b)` via `isColimitFreeCofan`: the left side becomes
`λ_.inv ≫ (ε ⊗ ε) ≫ μ 𝟙 𝟙 ≫ g^*(λ_.hom) ≫ ε⁻¹ ≫ ιFree (a, b)`, which equals `ιFree (a, b)` by the
left unitality of the strong monoidal structure (`Functor.LaxMonoidal.left_unitality`,
`leftUnitor_naturality`). Since `mulHom = freeTensorFreeIso.hom ≫ freeMap (addition of exponents)`,
the `freeMap` part is handled by `pullbackObjFreeIso_hom_naturality`.

The file-level `set_option backward.isDefEq.respectTransparency false` is needed because in
`X.Modules` the types `TopCat.Sheaf` and `Sheaf (grothendieckTopology)` are not equal at implicit
transparency, and the motive check of `rw` would otherwise fail (Mathlib's `PullbackFree.lean` does
the same). Reference: Stacks 01CD.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X)

/-- Scheme-level form of Mathlib's `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`:
`g^*(ιFree i) ≫ pullbackObjFreeIso.hom = pullbackUnitIso.hom ≫ ιFree i` (`pullbackUnitIso.hom` is
`pullbackObjUnitToUnit`). -/
theorem pullback_map_ιFree_comp_pullbackObjFreeIso_hom {I : Type u} (i : I) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).map
        (SheafOfModules.ιFree (R := X.ringCatSheaf) i :
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ SheafOfModules.free I) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g I).hom =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom ≫
        (SheafOfModules.ιFree (R := V.ringCatSheaf) i :
          (SheafOfModules.unit V.ringCatSheaf : V.Modules) ⟶ SheafOfModules.free I) :=
  haveI : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom g.toRingCatSheafHom i

/-- The inverse form of the previous lemma:
`ιFree i ≫ pullbackObjFreeIso.inv = pullbackUnitIso.inv ≫ g^*(ιFree i)`. -/
theorem ιFree_comp_pullbackObjFreeIso_inv {I : Type u} (i : I) :
    (SheafOfModules.ιFree (R := V.ringCatSheaf) i :
          (SheafOfModules.unit V.ringCatSheaf : V.Modules) ⟶ SheafOfModules.free I) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g I).inv =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback g).map
          (SheafOfModules.ιFree (R := X.ringCatSheaf) i :
            (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ SheafOfModules.free I) :=
  (Iso.comp_inv_eq _).mpr (by
    rw [Category.assoc, pullback_map_ιFree_comp_pullbackObjFreeIso_hom, Iso.inv_hom_id_assoc])

/-- The inverse form of `ιFree_tensor_ιFree_freeTensorFreeIso`:
`ιFree (i, j) ≫ freeTensorFreeIso.inv = λ_.inv ≫ (ιFree i ⊗ ιFree j)`. -/
theorem ιFree_comp_freeTensorFreeIso_inv {Y : AlgebraicGeometry.Scheme.{u}} {I J : Type u}
    (i : I) (j : J) :
    (SheafOfModules.ιFree (R := Y.ringCatSheaf) (i, j) :
          (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ SheafOfModules.free (I × J)) ≫
        (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := Y) I J).inv =
      (λ_ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)).inv ≫
        (SheafOfModules.ιFree (R := Y.ringCatSheaf) i ⊗ₘ SheafOfModules.ιFree (R := Y.ringCatSheaf) j) :=
  (Iso.comp_inv_eq _).mpr (by
    rw [Category.assoc, AlgebraicGeometry.Scheme.Modules.ιFree_tensor_ιFree_freeTensorFreeIso,
      Iso.inv_hom_id_assoc])

/-- Left unitality of the strong monoidal structure on the unit object:
`λ_.inv ≫ (ε ⊗ ε) ≫ μ 𝟙 𝟙 ≫ g^*(λ_ 𝟙).hom = ε`. From `tensorHom_def'`,
`Functor.LaxMonoidal.left_unitality` and `leftUnitor_naturality`. -/
theorem leftUnitor_inv_ε_tensor_ε_μ_tensorUnit :
    (λ_ (𝟙_ V.Modules)).inv ≫
        (Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback g) ⊗ₘ
          Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback g)) ≫
        Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback g) (𝟙_ X.Modules)
          (𝟙_ X.Modules) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback g).map (λ_ (𝟙_ X.Modules)).hom =
      Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback g) := by
  rw [MonoidalCategory.tensorHom_def', Category.assoc,
    ← Functor.LaxMonoidal.left_unitality (AlgebraicGeometry.Scheme.Modules.pullback g),
    MonoidalCategory.leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- The same, with the unit object spelled `SheafOfModules.unit` (matching the domain of `ιFree`
syntactically, for `rw`); definitionally equal, so `exact` suffices. -/
@[reassoc]
theorem leftUnitor_inv_ε_tensor_ε_μ :
    (λ_ (SheafOfModules.unit V.ringCatSheaf : V.Modules)).inv ≫
        (Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback g) ⊗ₘ
          Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback g)) ≫
        Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback g)
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) (SheafOfModules.unit X.ringCatSheaf) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback g).map
          (λ_ (SheafOfModules.unit X.ringCatSheaf : X.Modules)).hom =
      Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback g) :=
  leftUnitor_inv_ε_tensor_ε_μ_tensorUnit g

/-- The key compatibility: the strong monoidal structure `μ` of `g^*`, `freeTensorFreeIso` and
`pullbackObjFreeIso` commute:
`μ ≫ g^*(freeTensorFreeIso.hom) ≫ pullbackObjFreeIso.hom = (pullbackObjFreeIso.hom ⊗ pullbackObjFreeIso.hom) ≫ freeTensorFreeIso.hom`.

Proof: precompose both sides with the isomorphisms `(pullbackObjFreeIso ⊗ᵢ pullbackObjFreeIso).inv`
and `freeTensorFreeIso.inv` to get morphisms out of `free (I × J)`, and compare on the generators
`ιFree (a, b)` via `isColimitFreeCofan`; the right side is `ιFree (a, b)`, and the left side is
reduced step by step with `ιFree_comp_freeTensorFreeIso_inv`, `ιFree_comp_pullbackObjFreeIso_inv`,
`μ_natural`, `ιFree_tensor_ιFree_freeTensorFreeIso`, `pullback_map_ιFree_comp_pullbackObjFreeIso_hom`,
and finally `leftUnitor_inv_ε_tensor_ε_μ` and `ε = pullbackUnitIso.inv`. -/
@[reassoc]
theorem μ_map_freeTensorFreeIso_hom_pullbackObjFreeIso_hom (I J : Type u) :
    Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback g)
        (SheafOfModules.free (R := X.ringCatSheaf) I) (SheafOfModules.free (R := X.ringCatSheaf) J) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback g).map
        (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X) I J).hom ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g (I × J)).hom =
    ((AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g I).hom ⊗ₘ
        (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g J).hom) ≫
      (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := V) I J).hom := by
  rw [← MonoidalCategory.tensorIso_hom]
  rw [← cancel_epi ((AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g I ⊗ᵢ
    AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g J).inv),
    ← cancel_epi (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := V) I J).inv]
  apply Limits.Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (R := V.ringCatSheaf) (I × J))
  rintro ⟨a, b⟩
  simp only [SheafOfModules.freeCofan_inj, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  erw [Category.comp_id]
  rw [reassoc_of% (ιFree_comp_freeTensorFreeIso_inv (Y := V) a b), MonoidalCategory.tensorIso_inv,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    ιFree_comp_pullbackObjFreeIso_inv, ιFree_comp_pullbackObjFreeIso_inv,
    ← MonoidalCategory.tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc,
    ← Functor.map_comp_assoc, AlgebraicGeometry.Scheme.Modules.ιFree_tensor_ιFree_freeTensorFreeIso,
    Functor.map_comp_assoc, pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
    ← pullback_ε_eq, leftUnitor_inv_ε_tensor_ε_μ_assoc, pullback_ε_eq, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules

/-- The multiplication `μ ≫ g^*(mulHom)` of the pulled-back weighted polynomial algebra corresponds
under `pullbackObjFreeIso` to `mulHom` on the target. Since
`mulHom = freeTensorFreeIso.hom ≫ freeMap (addition of exponents)`, the `freeMap` part commutes by
`pullbackObjFreeIso_hom_naturality` and the `freeTensorFreeIso` part is
`μ_map_freeTensorFreeIso_hom_pullbackObjFreeIso_hom`. -/
theorem AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra_pullback_freeIso_map_mul
    {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X) {σ : Type u} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (i j : ℕ) :
    ((AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra X w hw).pullback g).mul i j ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g
          (weightedMonomials w (i + j))).hom =
      ((AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g
          (weightedMonomials w i)).hom ⊗ₘ
        (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g
          (weightedMonomials w j)).hom) ≫
        (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra V w hw).mul i j := by
  dsimp only [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback,
    AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra,
    AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.mulHom,
    AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.part]
  rw [Functor.map_comp, Category.assoc, Category.assoc,
    AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso_hom_naturality,
    AlgebraicGeometry.Scheme.Modules.μ_map_freeTensorFreeIso_hom_pullbackObjFreeIso_hom_assoc]

/-- The pulled-back unit `ε ≫ g^*(ιFree 0)` corresponds under `pullbackObjFreeIso` to `ιFree 0`:
after `pullback_map_ιFree_comp_pullbackObjFreeIso_hom` it remains to see
`ε ≫ pullbackUnitIso.hom = 𝟙` (`pullback_ε_eq`). -/
theorem AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra_pullback_freeIso_map_one
    {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X) {σ : Type u} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    ((AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra X w hw).pullback g).one ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g
          (weightedMonomials w 0)).hom =
      (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra V w hw).one := by
  dsimp only [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback,
    AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra,
    AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra.oneHom]
  rw [Category.assoc, AlgebraicGeometry.Scheme.Modules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
    AlgebraicGeometry.Scheme.Modules.pullback_ε_eq, Iso.inv_hom_id_assoc]

end
