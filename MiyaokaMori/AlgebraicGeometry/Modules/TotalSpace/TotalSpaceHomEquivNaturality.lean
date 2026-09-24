import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackCompMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback

/-! # Naturality of the section–morphism correspondence for the total space

Statement: the section–morphism correspondence `Hom_X(T, Tot V) ≃ Γ(T, g^*V)` (`totalSpaceHomEquiv`, `g = T.hom`) is
natural in `T`: for a scheme `T` over `X`, a morphism `j : S → T.left` and an `X`-morphism `m : T → Tot(V)`, viewing
`S` as a scheme over `X` via `(S, j ≫ g)`, the section corresponding to `j ≫ m` is the pullback along `j` of the section
corresponding to `m`, transported by the canonical isomorphism `j^*g^*V ≅ (j ≫ g)^*V` (`pullbackComp j g`):
`totalSpaceHomEquiv V (S, j≫g) (j ≫ m) = (pullbackComp j g).hom_V (j^*(totalSpaceHomEquiv V T m))`. Inverse form
(`totalSpaceHomEquiv_symm_naturality`): the morphism corresponding to the pullback of a section `s` along `j` is
`j ≫ (the morphism corresponding to s)`.

Proof (the steps correspond to the lemmas of this file):
1. `relativeSpec.toAlgebraMap_precomp`: `φ_{j≫m} = φ_m ≫ g_*(j^♯) ≫ (pushforwardComp j g).hom`, where
   `j^♯ = SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom`. On each open `U`: the component of `toAlgebraMap`
   is `pullbackSections = structureRingMap ≫ h.left.appLE`; for `j ≫ m` use `Scheme.Hom.appLE_comp_appLE`,
   `appLE_eq_app`, and `(j ≫ g)⁻¹U = j⁻¹(g⁻¹U)` is `rfl`.
2. `totalSpace.functionalOfHom_precomp`: `ψ_{j≫m} = (pullbackComp j g).inv ≫ j^*(ψ_m) ≫ (pullbackUnitIso j).hom`
   (`ψ_h := functionalOfHom V T h`, the `ψ` in the definition body of `toSection`). Transpose both sides along
   `adj_{j≫g}`: the left side is `symGen ≫ ι 1 ≫ φ_{j≫m}` by `Equiv.apply_symm_apply`; for the right side use the two
   transposition lemmas `homEquiv_pullbackComp_hom_app_comp` (under the composite adjunction the transpose of
   `pullbackComp.hom ≫ k` is the `adj_{j≫g}`-transpose followed by `pushforwardComp.inv`) and
   `homEquiv_comp_pullback_map_comp` (the transpose of `j^*a ≫ b` is the `adj_g`-transpose of `a` followed by
   `g_*(adj_j`-transpose of `b)`), the fact that the transpose of `pullbackUnitIso j` is `j^♯`
   (`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`), and step 1.
3. The coevaluation section: `ModuleSections.pullback_comp_inv`:
   `(pullbackComp j g).inv (pullback (j≫g) s) = pullback j (pullback g s)` (`conjugateEquiv_pullbackComp_inv` on
   `⊤`-sections).
4. `totalSpace.contractionOfFunctional_precomp`: `Ψ_h := contractionOfFunctional V g ψ_h = g^*(tensorIsoTensorObj) ≫ δ_g ≫ (ψ ▷ g^*V) ≫ λ`
   (the `Ψ` in the definition body of `toSection`, `toSection_eq` is `rfl`).
   `pullbackComp.hom ≫ Ψ_{j≫g}(pullbackComp.inv ≫ j^*ψ ≫ η_j) = j^*(Ψ_g ψ) ≫ pullbackComp.hom`: naturality of
   `pullbackComp.hom`, `pullbackComp_hom_app_pullbackTensorObjHom`, `tensorHom_def` + `whisker_exchange` +
   `leftUnitor_naturality`, then `δ_natural_left` and `left_unitality_hom` of the oplax structure
   (`pullbackTensorObjHom_eq_δ`, `pullback_η`).
5. Main theorem: unfold `toSection` on both sides (`toSection_eq`), replace `ψ` by step 2, on the right move `j^*` onto
   `Ψ` by `ModuleSections.pullback_naturality` (naturality of the adjunction unit), then by step 3 replace
   `pullback j (pullback g coev)` by `pullbackComp.inv (pullback (j≫g) coev)`; what remains is the morphism equation of
   step 4 applied at `⊤` to `pullback (j≫g) coev`.
6. Inverse form: apply `(totalSpaceHomEquiv …).symm` to both sides of the first statement and use `Equiv.symm_apply_eq`,
   `Equiv.apply_symm_apply`.

Reference: Hartshorne II Ex. 5.18 (functoriality of the total space); the constructions of `totalSpaceHomEquiv` are
natural in `T` step by step.
-/
/- `sectionPullbackAlong` is by definition the adjunction unit, and `ModuleSections.pullback` is its `Γ`-typed
reducible abbreviation. Sites that need the `Γ`-typed spelling bridge it with `rw [sectionPullbackAlong_eq_pullback <g> <s>]`
(explicit arguments: an inner occurrence whose argument is `Γ`-typed is not type-correct at reducible transparency, so
`simp only`/`rw` with metavariables cannot abstract it) or with a `change` to that spelling; sites that need the unit use
plain `unfold sectionPullbackAlong`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- The adjoint transpose of `pullbackUnitIso j` is Mathlib's `unitToPushforwardObjUnit` (the ring homomorphism `j^♯`). -/
private theorem homEquiv_pullbackUnitIso_hom_aux {S T : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T) :
    (Modules.pullbackPushforwardAdjunction j).homEquiv _ _ (Modules.pullbackUnitIso j).hom =
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom :=
  haveI : (SheafOfModules.pushforward.{u} j.toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction j).isRightAdjoint
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u} j.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
/-- Step 1: naturality of `toAlgebraMap` under precomposition with `j`: `φ_{j ≫ m} = φ_m ≫ g_*(j^♯) ≫ (pushforwardComp j g).hom`. -/
theorem relativeSpec.toAlgebraMap_precomp {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra)
    (T : CategoryTheory.Over X) {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left)
    (m : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) :
    relativeSpec.toAlgebraMap A (CategoryTheory.Over.mk (j ≫ T.hom))
        ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m) =
      relativeSpec.toAlgebraMap A T m ≫
        (Modules.pushforward T.hom).map
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
        (Modules.pushforwardComp j T.hom).hom.app (SheafOfModules.unit S.ringCatSheaf) := by
  ext U x
  have e1 : ∀ (T' : CategoryTheory.Over X) (h : T' ⟶ AlgebraicGeometry.Scheme.relativeSpec A)
      (W : X.Opens),
      CommRingCat.ofHom (relativeSpec.pullbackSections A T' h W) =
      (relativeSpec.structureRingMap A).app (Opposite.op W) ≫
        h.left.appLE ((relativeSpec A).hom ⁻¹ᵁ W) (T'.hom ⁻¹ᵁ W)
          (le_of_eq (show T'.hom ⁻¹ᵁ W = h.left ⁻¹ᵁ ((relativeSpec A).hom ⁻¹ᵁ W) by
            rw [← CategoryTheory.Over.w h]; rfl)) := fun _ _ _ => rfl
  have key : CommRingCat.ofHom (relativeSpec.pullbackSections A (CategoryTheory.Over.mk (j ≫ T.hom))
        ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m) U) =
      CommRingCat.ofHom (relativeSpec.pullbackSections A T m U) ≫ j.app (T.hom ⁻¹ᵁ U) := by
    rw [e1, e1, ← AlgebraicGeometry.Scheme.Hom.appLE_eq_app, Category.assoc,
      AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE]
    rfl
  exact congrArg (fun φ => φ.hom x) key

/-- The linear functional `ψ_h : g^*(V^∨) → O_T` corresponding to `h` (the `ψ` in the definition body of `toSection`). -/
def totalSpace.functionalOfHom {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    (Modules.pullback T.hom).obj (Modules.dual V) ⟶ 𝟙_ T.left.Modules :=
  ((Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _).symm
    (Modules.symGen (Modules.dual V) ≫
      CategoryTheory.Limits.Sigma.ι (Modules.symGradedAlgebra (Modules.dual V)).part 1 ≫
      relativeSpec.toAlgebraMap (Modules.symGradedAlgebra (Modules.dual V)).total T h)

/-- From a linear functional `ψ : g^*(V^∨) → O_T` to `g^*(V^∨ ⊗ V) → g^*V` (the `Ψ` in the definition body of `toSection`). -/
def totalSpace.contractionOfFunctional {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) {T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (ψ : (Modules.pullback g).obj (Modules.dual V) ⟶ 𝟙_ T.Modules) :
    (Modules.pullback g).obj (Modules.tensor (Modules.dual V) V) ⟶ (Modules.pullback g).obj V :=
  (Modules.pullback g).map (Modules.tensorIsoTensorObj (Modules.dual V) V).hom ≫
    Modules.pullbackTensorObjHom g (Modules.dual V) V ≫
    (ψ ▷ (Modules.pullback g).obj V) ≫
    (λ_ ((Modules.pullback g).obj V)).hom

theorem totalSpace.toSection_eq {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    totalSpace.toSection V T h =
      (totalSpace.contractionOfFunctional V T.hom (totalSpace.functionalOfHom V T h)).app ⊤
        (sectionPullbackAlong T.hom (Modules.coevSection V)) := rfl

/-- Step 2: naturality of `ψ` under precomposition with `j`. -/
theorem totalSpace.functionalOfHom_precomp {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left)
    (m : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    totalSpace.functionalOfHom V (CategoryTheory.Over.mk (j ≫ T.hom))
        ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m) =
      (Modules.pullbackComp j T.hom).inv.app (Modules.dual V) ≫
        (Modules.pullback j).map (totalSpace.functionalOfHom V T m) ≫
        (Modules.pullbackUnitIso j).hom := by
  apply ((Modules.pullbackPushforwardAdjunction (j ≫ T.hom)).homEquiv _ _).injective
  have hL : (Modules.pullbackPushforwardAdjunction (j ≫ T.hom)).homEquiv _ _
      (totalSpace.functionalOfHom V (CategoryTheory.Over.mk (j ≫ T.hom))
        ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m)) =
      Modules.symGen (Modules.dual V) ≫
        CategoryTheory.Limits.Sigma.ι (Modules.symGradedAlgebra (Modules.dual V)).part 1 ≫
        relativeSpec.toAlgebraMap (Modules.symGradedAlgebra (Modules.dual V)).total
          (CategoryTheory.Over.mk (j ≫ T.hom))
          ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m) :=
    Equiv.apply_symm_apply _ _
  have hR : (Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
      (totalSpace.functionalOfHom V T m) =
      Modules.symGen (Modules.dual V) ≫
        CategoryTheory.Limits.Sigma.ι (Modules.symGradedAlgebra (Modules.dual V)).part 1 ≫
        relativeSpec.toAlgebraMap (Modules.symGradedAlgebra (Modules.dual V)).total T m :=
    Equiv.apply_symm_apply _ _
  -- K := c.inv ≫ j^*ψ ≫ u.hom; under the composite adjunction, the transposes of c.hom ≫ K and of K agree
  have h1 := Modules.homEquiv_pullbackComp_hom_app_comp j T.hom (A := Modules.dual V)
    ((Modules.pullbackComp j T.hom).inv.app (Modules.dual V) ≫
      (Modules.pullback j).map (totalSpace.functionalOfHom V T m) ≫ (Modules.pullbackUnitIso j).hom)
  have h1' := congrArg
    (((Modules.pullbackPushforwardAdjunction T.hom).comp
      (Modules.pullbackPushforwardAdjunction j)).homEquiv (Modules.dual V) _)
    (Iso.hom_inv_id_app_assoc (Modules.pullbackComp j T.hom) (Modules.dual V)
      ((Modules.pullback j).map (totalSpace.functionalOfHom V T m) ≫ (Modules.pullbackUnitIso j).hom))
  have h4 := (Iso.comp_inv_eq ((Modules.pushforwardComp j T.hom).app
    (SheafOfModules.unit S.ringCatSheaf))).mp (h1.symm.trans h1')
  have h2 := Modules.homEquiv_comp_pullback_map_comp j T.hom (totalSpace.functionalOfHom V T m)
    (Modules.pullbackUnitIso j).hom
  have h2' := h2.trans (congrArg₂ (fun a b => a ≫ (Modules.pushforward T.hom).map b) hR
    (homEquiv_pullbackUnitIso_hom_aux j))
  refine hL.trans (Eq.trans ?_ h4.symm)
  refine Eq.trans ?_ (congrArg (fun a => a ≫ (Modules.pushforwardComp j T.hom).hom.app
    (SheafOfModules.unit S.ringCatSheaf)) h2'.symm)
  rw [relativeSpec.toAlgebraMap_precomp (Modules.symGradedAlgebra (Modules.dual V)).total T j m]
  exact (congrArg (fun x => Modules.symGen (Modules.dual V) ≫ x) (Category.assoc _ _ _)).symm

/-- Step 4: `Ψ` is compatible with `pullbackComp` (`pullbackComp` is a monoidal natural isomorphism). -/
theorem totalSpace.contractionOfFunctional_precomp {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) {S T : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T) (g : T ⟶ X)
    (ψ : (Modules.pullback g).obj (Modules.dual V) ⟶ 𝟙_ T.Modules) :
    (Modules.pullbackComp j g).hom.app (Modules.tensor (Modules.dual V) V) ≫
        totalSpace.contractionOfFunctional V (j ≫ g)
          ((Modules.pullbackComp j g).inv.app (Modules.dual V) ≫
            (Modules.pullback j).map ψ ≫ (Modules.pullbackUnitIso j).hom) =
      (Modules.pullback j).map (totalSpace.contractionOfFunctional V g ψ) ≫
        (Modules.pullbackComp j g).hom.app V := by
  unfold totalSpace.contractionOfFunctional
  rw [← NatTrans.naturality_assoc, Functor.comp_map,
    reassoc_of% (Modules.pullbackComp_hom_app_pullbackTensorObjHom j g (Modules.dual V) V),
    MonoidalCategory.tensorHom_def, Category.assoc, MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id_app_assoc,
    MonoidalCategory.leftUnitor_naturality, MonoidalCategory.comp_whiskerRight_assoc,
    Modules.pullbackTensorObjHom_eq_δ j, ← Modules.pullback_η j,
    Functor.OplaxMonoidal.δ_natural_left_assoc, Functor.OplaxMonoidal.left_unitality_hom_assoc]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme

/-- Naturality in `T` (precomposition with `j : S → T.left` ↔ pullback of the section along `j`, then `pullbackComp`). -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left)
    (m : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (j ≫ T.hom))
        ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m)
      = (((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app V).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong j (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m)) := by
  show AlgebraicGeometry.Scheme.totalSpace.toSection V (CategoryTheory.Over.mk (j ≫ T.hom))
      ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m) =
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app V).app ⊤
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback j (AlgebraicGeometry.Scheme.totalSpace.toSection V T m))
  rw [AlgebraicGeometry.Scheme.totalSpace.toSection_eq, AlgebraicGeometry.Scheme.totalSpace.toSection_eq,
    AlgebraicGeometry.Scheme.totalSpace.functionalOfHom_precomp]
  -- bridge the inner `T.hom^*coev` (its argument is `Γ`-typed, so a generic `rw`/`simp only` cannot abstract it);
  -- the explicit instance matches syntactically.
  rw [sectionPullbackAlong_eq_pullback T.hom (AlgebraicGeometry.Scheme.Modules.coevSection V)]
  rw [← AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_naturality, ← AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp_inv j T.hom]
  have key := AlgebraicGeometry.Scheme.totalSpace.contractionOfFunctional_precomp V j T.hom
    (AlgebraicGeometry.Scheme.totalSpace.functionalOfHom V T m)
  have key' : AlgebraicGeometry.Scheme.totalSpace.contractionOfFunctional V (j ≫ T.hom)
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).inv.app
            (AlgebraicGeometry.Scheme.Modules.dual V) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback j).map
            (AlgebraicGeometry.Scheme.totalSpace.functionalOfHom V T m) ≫
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso j).hom) =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).inv.app
          (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual V) V) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback j).map
          (AlgebraicGeometry.Scheme.totalSpace.contractionOfFunctional V T.hom
            (AlgebraicGeometry.Scheme.totalSpace.functionalOfHom V T m)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app V := by
    rw [← key, Iso.inv_hom_id_app_assoc]
  exact congrArg (fun φ => AlgebraicGeometry.Scheme.Modules.Hom.app φ ⊤
    (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (j ≫ T.hom) (AlgebraicGeometry.Scheme.Modules.coevSection V))) key'

/-- Inverse form: the morphism corresponding to the pullback of a section along `j` is the precomposition with `j`.
Immediate from the previous statement and the inverse laws of the `Equiv`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_symm_naturality {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left)
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (j ≫ T.hom))).symm
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app V).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong j s))
      = (CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T).symm s := by
  rw [Equiv.symm_apply_eq, AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality, Equiv.apply_symm_apply]

end
