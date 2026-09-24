import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseLiftCompOfPieces
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseLSectionPiece
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseCanonicalTriv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseZeroSectionPiece
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleOSection

/-! # `Tot(L)` is affine over the base and is the complement of the `L`-section in `ℙ(O ⊕ L)`

`Tot(L)` is affine over `X`, `Tot(L) ≅ Spec_X Sym(L^∨)`, and it is an open neighbourhood of the `O`-section
(§4 of the paper: "the subbundle `L ↪ O ⊕ L` defines a section of `ℙ(O ⊕ L)`, whose complement is naturally
`Tot(L)`; under this identification, the section defined by the other summand `O` is the zero section of
`Tot(L)`").

## Layout

The total space of `L` is `totalSpace L = Spec_X Sym(L^∨)` (it appears in the target statement
`realization`). The paper describes `Tot(L)` as the open subscheme `P(O ⊕ L) ∖ σ_L(X)`; this module proves that
description as **theorems about `totalSpace L`**:

* `tautologicalFunctional` ξ : p^*(L^∨) → O_Tot (the fibre coordinate);
* `toProjBundleQuotient` : p^*((O ⊕ L)^∨) → O_Tot, `(a, λ) ↦ a + λ(ξ)` (the point `[1 : ξ]`);
  **it is an epimorphism** (`toProjBundleQuotient_epi`: the O-component is split by the unit section);
* `toProjBundle` : Spec_X Sym(L^∨) → P(O ⊕ L) by the universal property `projBundle.lift`; it is a morphism over `X`
  (`toProjBundle_comp_hom`);
* its image avoids σ_L (`range_toProjBundle_le`, from `projBundle.lift_restrict` / `liftLocal_base_ne`
  (`TotLineAffineOverBaseLiftRestrict.lean`) and the two degree-1 lemmas `localRingHom_oCoordinate_isUnit`,
  `localRingHom_lSection_oCoordinate_eq_zero` (via `localRingHomComponent_one_symGen_apply`,
  `TotLineAffineOverBaseDegreeOne.lean`));
* **`toProjBundle` is an open immersion** (`toProjBundle_isOpenImmersion`, section `IsIsoGlue`): local on the target,
  on `π⁻¹W` it is the canonical piece `fromOfGlobalSections φ_W ≫ affineIso⁻¹ ≫ ι` (`lift_restrict`), and
  `Proj.isOpenImmersion_fromOfGlobalSections_of_bijective` applies by `toProjBundle_awayMap_bijective`
  (`(A(W)_T)_0 ≅ Sym(L^∨)(W)` via the graded model `A(W) ≅ Sym(L^∨)(W)[T]`, `TotLineAffineOverBaseGradedModel.lean` /
  `TotLineAffineOverBaseSymPolynomialModel.lean`, the criterion `TotLineAffineOverBaseAwayMapBijective.lean`, and the
  generator values `canonicalPiece_sectionsUnitHom`, `canonicalPiece_genSections_sLinear`,
  `TotLineAffineOverBaseDegreeOneTranspose.lean`);
* **its image is exactly `P(O ⊕ L) ∖ σ_L(X)`** (`compl_range_lSection_le_range_toProjBundle`, `range_toProjBundle_eq`):
  a point outside `σ_L` lies over a chart `W`; if it is in `D₊(T)` it is in the image by
  `Proj.mem_range_fromOfGlobalSections_of_bijective`, otherwise it is in `V₊(T) ⊆ σ_L(W)`
  (`mem_range_lSection_of_not_mem_basicOpen_oCoordinate`: `Proj.mem_range_fromOfGlobalSections_of_forall_mem_span`
  (`TotLineAffineOverBaseProjRangeOfKernel.lean`), the kernel lemma `TotLineAffineOverBaseSymSplitKernel.lean`, and the
  degree-one computation of the `L`-section piece `TotLineAffineOverBaseLSectionPiece.lean`);
* **the zero section is the O-section** (`zeroSection_comp_toProjBundle`: `projBundle.comp_lift_of_pieces`
  (`TotLineAffineOverBaseLiftCompOfPieces.lean`) + `Proj.comp_fromOfGlobalSections`
  (`TotLineAffineOverBaseFromOfGlobalSectionsComp.lean`) + `zeroSection_toProjBundle_pieces` (the
  ring-homomorphism comparison of the local pieces, values from `TotLineAffineOverBaseCanonicalTriv.lean` and
  `TotLineAffineOverBaseZeroSectionPiece.lean`)), hence the O-section avoids σ_L (`oSection_not_mem_range_lSection`).

Downstream, `ruledSurface.totalSpaceIncl L := toProjBundle L.toModules` (`TotalSpaceAgreesTotLine.lean`) is the open
immersion `Tot(L) ↪ W = P(O ⊕ L)` used for the ruled surface.

All dual maps are spelled in the `dual` world (`dualCurryMap`, `dualEv`, `dualCurry`;
`ModulesDualCurryMap.lean`), the same morphisms as `dualMap` / `internalHomEval`
(`ModulesDualCurry.lean` explains why the two spellings must not be mixed inside proofs).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The tautological linear functional `ξ : p^*(V^∨) → O_{Tot(V)}`: the morphism corresponding under the
pullback–pushforward adjunction to the inclusion of generators
`V^∨ → Sym^1(V^∨) → ⊕ Sym^m(V^∨) → p_*O_Tot` (`relativeSpec.structureHom`). For a line bundle `V` it is the
fiber coordinate. -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.tautologicalFunctional {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace V).hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace V).left.ringCatSheaf :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.Scheme.totalSpace V).hom).homEquiv _ _).symm
    (AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).totalIncl 1 ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total)

/-- `O_X^∨ → O_X`: evaluation at `1` (the evaluation `dualEv : O^∨ ⊗ O → O` after the right unitor).
`dualEv O` is `internalHomEval O O` transported along the definitional equation `dual O = 𝓗om(O, O)`
(`ModulesDualCurry.lean`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.dualUnitEval (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
  (ρ_ (AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf))).inv ≫
    AlgebraicGeometry.Scheme.Modules.dualEv (show X.Modules from SheafOfModules.unit X.ringCatSheaf)

/-- The unit section `O_X → O_X^∨`, `1 ↦ (1 ↦ 1)`: the currying of the right unitor `O ⊗ O ≅ O`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.unitDualSection (X : AlgebraicGeometry.Scheme.{u}) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
  AlgebraicGeometry.Scheme.Modules.dualCurry (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    (ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).hom

/-- The unit section followed by evaluation at `1` is the identity: `(1 ↦ (1 ↦ 1)) ≫ (φ ↦ φ(1)) = 𝟙`.
Proof: `u ≫ (ρ_ O^∨)⁻¹ = (ρ_ O)⁻¹ ≫ (u ▷ O)` (naturality of the right unitor), and `(u ▷ O) ≫ ev = (ρ_ O).hom`
(`dualCurry_symm_apply`: uncurrying is `ψ ↦ (ψ ▷ V) ≫ ev`). -/
theorem AlgebraicGeometry.Scheme.Modules.unitDualSection_comp_dualUnitEval (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫ AlgebraicGeometry.Scheme.Modules.dualUnitEval X =
      𝟙 (show X.Modules from SheafOfModules.unit X.ringCatSheaf) := by
  have hu : (AlgebraicGeometry.Scheme.Modules.unitDualSection X ▷
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) ≫
      AlgebraicGeometry.Scheme.Modules.dualEv (show X.Modules from SheafOfModules.unit X.ringCatSheaf) =
      (ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).hom := by
    unfold AlgebraicGeometry.Scheme.Modules.unitDualSection
    rw [← AlgebraicGeometry.Scheme.Modules.dualCurry_symm_apply, Equiv.symm_apply_apply]
  unfold AlgebraicGeometry.Scheme.Modules.dualUnitEval
  calc AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
        ((ρ_ (AlgebraicGeometry.Scheme.Modules.dual
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf))).inv ≫
          AlgebraicGeometry.Scheme.Modules.dualEv (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
      = (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
          (ρ_ (AlgebraicGeometry.Scheme.Modules.dual
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf))).inv) ≫
          AlgebraicGeometry.Scheme.Modules.dualEv (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
        (Category.assoc _ _ _).symm
    _ = ((ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (AlgebraicGeometry.Scheme.Modules.unitDualSection X ▷ 𝟙_ X.Modules)) ≫
          AlgebraicGeometry.Scheme.Modules.dualEv (show X.Modules from SheafOfModules.unit X.ringCatSheaf) := by
        rw [MonoidalCategory.rightUnitor_inv_naturality]
    _ = (ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).inv ≫
          ((AlgebraicGeometry.Scheme.Modules.unitDualSection X ▷
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) ≫
          AlgebraicGeometry.Scheme.Modules.dualEv (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :=
        Category.assoc _ _ _
    _ = (ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).hom :=
        congrArg (fun t => (ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).inv ≫ t) hu
    _ = 𝟙 (show X.Modules from SheafOfModules.unit X.ringCatSheaf) := Iso.inv_hom_id _

/-- **The other composite: `(φ ↦ φ(1)) ≫ (1 ↦ (1 ↦ 1)) = 𝟙 O^∨`.**
Uncurry both sides (`dualCurry_symm_apply`: `ψ ↦ (ψ ▷ O) ≫ ev`): the
left side is `(dualUnitEval ▷ O) ≫ (unitDualSection ▷ O) ≫ ev = (dualUnitEval ▷ O) ≫ (ρ_ O).hom = (ρ_ O^∨).hom ≫
dualUnitEval = ev` (`hu` of `unitDualSection_comp_dualUnitEval`, naturality of the right unitor,
`dualUnitEval = (ρ_ O^∨).inv ≫ ev`); the right side is `(𝟙 ▷ O) ≫ ev = ev`. -/
theorem AlgebraicGeometry.Scheme.Modules.dualUnitEval_comp_unitDualSection (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.Modules.dualUnitEval X ≫ AlgebraicGeometry.Scheme.Modules.unitDualSection X =
      𝟙 (AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) := by
  have hu : (AlgebraicGeometry.Scheme.Modules.unitDualSection X ▷
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) ≫
      AlgebraicGeometry.Scheme.Modules.dualEv (show X.Modules from SheafOfModules.unit X.ringCatSheaf) =
      (ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).hom := by
    unfold AlgebraicGeometry.Scheme.Modules.unitDualSection
    rw [← AlgebraicGeometry.Scheme.Modules.dualCurry_symm_apply, Equiv.symm_apply_apply]
  apply (AlgebraicGeometry.Scheme.Modules.dualCurry
    (AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).symm.injective
  rw [AlgebraicGeometry.Scheme.Modules.dualCurry_symm_apply, AlgebraicGeometry.Scheme.Modules.dualCurry_symm_apply,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.id_whiskerRight]
  erw [Category.id_comp, Category.assoc, hu]
  have hnat : (AlgebraicGeometry.Scheme.Modules.dualUnitEval X ▷ 𝟙_ X.Modules) ≫
      (ρ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).hom =
      (ρ_ (AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf))).hom ≫
        AlgebraicGeometry.Scheme.Modules.dualUnitEval X :=
    MonoidalCategory.rightUnitor_naturality _
  erw [hnat]
  unfold AlgebraicGeometry.Scheme.Modules.dualUnitEval
  erw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **`O^∨ ≅ O`**, `φ ↦ φ(1)` with inverse `1 ↦ (1 ↦ 1)` (`dualUnitEval`, `unitDualSection`). This is the
trivialization `ε` fed to the generic graded model `TotLineAffineOverBaseGradedModel.lean`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.unitDualIso (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ≅
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) where
  hom := AlgebraicGeometry.Scheme.Modules.dualUnitEval X
  inv := AlgebraicGeometry.Scheme.Modules.unitDualSection X
  hom_inv_id := AlgebraicGeometry.Scheme.Modules.dualUnitEval_comp_unitDualSection X
  inv_hom_id := AlgebraicGeometry.Scheme.Modules.unitDualSection_comp_dualUnitEval X

/-- The `O`-component `p^*((O ⊕ L)^∨) → O_Tot` of the invertible quotient: the dual of `inl`,
`dualCurryMap inl : (O ⊕ L)^∨ → O^∨`, then evaluation at `1` (`dualUnitEval`), then `p^*O ≅ O`. -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientO {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) ⟶
      (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
        SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
      (AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.inl (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
        AlgebraicGeometry.Scheme.Modules.dualUnitEval X) ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).hom

/-- The `L`-component `p^*((O ⊕ L)^∨) → O_Tot` of the invertible quotient: the dual of `inr`,
`dualCurryMap inr : (O ⊕ L)^∨ → L^∨`, followed by the tautological functional `ξ`. -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientL {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) ⟶
      (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
        SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
      (AlgebraicGeometry.Scheme.Modules.dualCurryMap
        (CategoryTheory.Limits.biprod.inr (C := X.Modules)
          (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
    AlgebraicGeometry.Scheme.totalSpace.tautologicalFunctional L

/-- The invertible quotient `p^*((O ⊕ L)^∨) → O_Tot`: `(a, λ) ↦ a + λ(ξ)`, i.e. the point `[1 : ξ]`
(the `O`-component plus the `L`-component). -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) ⟶
      SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf :=
  AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientO L +
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientL L

/-- A section `O_Tot → p^*((O ⊕ L)^∨)` of the invertible quotient, `1 ↦ (1, 0)`: the inverse of `p^*O ≅ O`,
the unit section `unitDualSection`, then the dual of `fst`, `dualCurryMap fst : O^∨ → (O ⊕ L)^∨`. -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
        SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
      (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
        AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.fst (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)))

/-- The section followed by the `O`-component is the identity: `(1, 0) ↦ 1`.
`dualCurryMap fst ≫ dualCurryMap inl = dualCurryMap (inl ≫ fst) = 𝟙`, then `unitDualSection_comp_dualUnitEval`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection_comp_O {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection L ≫
      AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientO L = 𝟙 _ := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
        AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.fst (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
      (AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.inl (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
        AlgebraicGeometry.Scheme.Modules.dualUnitEval X) =
      𝟙 (show X.Modules from SheafOfModules.unit X.ringCatSheaf) := by
    calc (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
          AlgebraicGeometry.Scheme.Modules.dualCurryMap
            (CategoryTheory.Limits.biprod.fst (C := X.Modules)
              (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        (AlgebraicGeometry.Scheme.Modules.dualCurryMap
            (CategoryTheory.Limits.biprod.inl (C := X.Modules)
              (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
          AlgebraicGeometry.Scheme.Modules.dualUnitEval X)
        = AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
          (AlgebraicGeometry.Scheme.Modules.dualCurryMap
            (CategoryTheory.Limits.biprod.fst (C := X.Modules)
              (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
          AlgebraicGeometry.Scheme.Modules.dualCurryMap
            (CategoryTheory.Limits.biprod.inl (C := X.Modules)
              (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
          AlgebraicGeometry.Scheme.Modules.dualUnitEval X := by
          rw [Category.assoc, Category.assoc]
      _ = AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
          𝟙 _ ≫ AlgebraicGeometry.Scheme.Modules.dualUnitEval X := by
          rw [AlgebraicGeometry.Scheme.Modules.dualCurryMap_fst_comp_inl]
      _ = AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
          AlgebraicGeometry.Scheme.Modules.dualUnitEval X := by rw [Category.id_comp]
      _ = 𝟙 _ := AlgebraicGeometry.Scheme.Modules.unitDualSection_comp_dualUnitEval X
  have e3 : (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
      ((AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
        AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.fst (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
      (AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.inl (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
        AlgebraicGeometry.Scheme.Modules.dualUnitEval X)) = 𝟙 _ :=
    (congrArg (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map h1).trans
      (CategoryTheory.Functor.map_id _ _)
  unfold AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientO
  calc (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
            AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.fst (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          (AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.inl (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
            AlgebraicGeometry.Scheme.Modules.dualUnitEval X) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).hom
      = (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
            AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.fst (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          (AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.inl (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
            AlgebraicGeometry.Scheme.Modules.dualUnitEval X)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).hom) :=
        congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫ t) (Category.assoc _ _ _).symm
    _ = (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          ((AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
            AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.fst (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
          (AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.inl (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
            AlgebraicGeometry.Scheme.Modules.dualUnitEval X)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).hom) :=
        congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫ (t ≫ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
            (AlgebraicGeometry.Scheme.totalSpace L).hom).hom)) (CategoryTheory.Functor.map_comp _ _ _).symm
    _ = (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        (𝟙 _ ≫ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).hom) :=
        congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫ (t ≫ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
            (AlgebraicGeometry.Scheme.totalSpace L).hom).hom)) e3
    _ = (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).hom :=
        congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫ t) (Category.id_comp _)
    _ = 𝟙 _ := Iso.inv_hom_id _

/-- The section followed by the `L`-component is zero: the `L`-component of `(1, 0)` is `0`.
`dualCurryMap fst ≫ dualCurryMap inr = dualCurryMap (inr ≫ fst) = dualCurryMap 0 = 0`, and the pullback
functor is additive (a left adjoint), hence preserves zero. -/
theorem AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection_comp_L {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection L ≫
      AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientL L = 0 := by
  haveI : (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).Additive :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.Scheme.totalSpace L).hom).left_adjoint_additive
  have h1 : (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
        AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.fst (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
      AlgebraicGeometry.Scheme.Modules.dualCurryMap
        (CategoryTheory.Limits.biprod.inr (C := X.Modules)
          (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) = 0 := by
    rw [Category.assoc, AlgebraicGeometry.Scheme.Modules.dualCurryMap_fst_comp_inr, comp_zero]
  have e3 : (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
      ((AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
        AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.fst (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
      AlgebraicGeometry.Scheme.Modules.dualCurryMap
        (CategoryTheory.Limits.biprod.inr (C := X.Modules)
          (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) = 0 :=
    (congrArg (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map h1).trans
      (CategoryTheory.Functor.map_zero _ _ _)
  unfold AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientL
  calc (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
            AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.fst (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          (AlgebraicGeometry.Scheme.Modules.dualCurryMap
            (CategoryTheory.Limits.biprod.inr (C := X.Modules)
              (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        AlgebraicGeometry.Scheme.totalSpace.tautologicalFunctional L
      = (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          (AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
            AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.fst (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          (AlgebraicGeometry.Scheme.Modules.dualCurryMap
            (CategoryTheory.Limits.biprod.inr (C := X.Modules)
              (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)))) ≫
        AlgebraicGeometry.Scheme.totalSpace.tautologicalFunctional L) :=
        congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫ t) (Category.assoc _ _ _).symm
    _ = (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).map
          ((AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
            AlgebraicGeometry.Scheme.Modules.dualCurryMap
              (CategoryTheory.Limits.biprod.fst (C := X.Modules)
                (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
          AlgebraicGeometry.Scheme.Modules.dualCurryMap
            (CategoryTheory.Limits.biprod.inr (C := X.Modules)
              (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        AlgebraicGeometry.Scheme.totalSpace.tautologicalFunctional L) :=
        congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
            (t ≫ AlgebraicGeometry.Scheme.totalSpace.tautologicalFunctional L)) (CategoryTheory.Functor.map_comp _ _ _).symm
    _ = (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        ((0 : (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
          (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
            (AlgebraicGeometry.Scheme.Modules.dual L)) ≫
          AlgebraicGeometry.Scheme.totalSpace.tautologicalFunctional L) :=
        congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
            (t ≫ AlgebraicGeometry.Scheme.totalSpace.tautologicalFunctional L)) e3
    _ = (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫
        (0 : (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
          (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
            SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf)) :=
        congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv ≫ t) zero_comp
    _ = (0 : (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
            SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf) ⟶
          (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
            SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf)) :=
        comp_zero (f := (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L).hom).inv)

/-- The section followed by the invertible quotient is the identity: `s ≫ (a + b) = s ≫ a + s ≫ b = 𝟙 + 0`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection_comp {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection L ≫
      AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L = 𝟙 _ := by
  unfold AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient
  calc AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection L ≫
        (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientO L +
          AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientL L)
      = AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection L ≫
          AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientO L +
        AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection L ≫
          AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientL L := Preadditive.comp_add _ _ _ _ _ _
    _ = 𝟙 _ + 0 :=
        congrArg₂ (· + ·) (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection_comp_O L)
          (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection_comp_L L)
    _ = 𝟙 _ := add_zero _

/-- **The invertible quotient `p^*((O ⊕ L)^∨) → O_Tot` is an epimorphism** (a split epimorphism, with section
`toProjBundleQuotientSection`, `1 ↦ (1, 0)`): the `O`-component takes the value `1` on the unit section of
`O^∨ = 𝓗om(O, O)`, and the `L`-component vanishes on it.
Source: Stacks 01O4 (morphisms to a projective bundle are given by invertible quotients); §4 of the paper. -/
theorem AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient_epi {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    CategoryTheory.Epi (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) :=
  haveI : IsSplitEpi (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) :=
    IsSplitEpi.mk' ⟨AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection L,
      AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection_comp L⟩
  IsSplitEpi.epi _

/-- `Tot(L) = Spec_X Sym(L^∨) → P(O ⊕ L)`: the universal property of the projective bundle (`projBundle.lift`)
applied to the invertible quotient above. -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.toProjBundle {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    (AlgebraicGeometry.Scheme.totalSpace L).left ⟶ (AlgebraicGeometry.Scheme.projBundle (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).left :=
  @AlgebraicGeometry.Scheme.projBundle.lift X (AlgebraicGeometry.Scheme.totalSpace L).left (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) _ _ (AlgebraicGeometry.Scheme.totalSpace L).hom
    (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf) _
    (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L)
    (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient_epi L)


/-- **The O-coordinate `T` on `P(O ⊕ L)`**, as a section of `Sym^1((O ⊕ L)^∨)` over `W ⊆ X`: the linear form
`(a, λ) ↦ a`, i.e. `dualCurryMap fst` applied to the unit section `1 ↦ (1 ↦ 1)` of `O^∨`, pushed into degree 1
of `Sym((O ⊕ L)^∨)` by `symGen`. In the graded sections ring `A(W) = ⊕_m Γ(W, Sym^m)` it is the homogeneous
degree-1 element `DirectSum.of _ 1 (oCoordinate L W)`; `σ_L = V₊(T)` and `Tot(L) = D₊(T)`
(§4 of the paper). -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.oCoordinate {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (W : X.Opens) :
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).part 1).val.obj (Opposite.op W) :=
  ((AlgebraicGeometry.Scheme.Modules.symGen
      (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).val.app (Opposite.op W)).hom
    (((AlgebraicGeometry.Scheme.Modules.unitDualSection X ≫
        AlgebraicGeometry.Scheme.Modules.dualCurryMap
          (CategoryTheory.Limits.biprod.fst (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).val.app
        (Opposite.op W)).hom (1 : Γ(X, W)))

section DegreeOneLeaves

set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle in
/-- **`toProjBundle` reads the O-coordinate as a unit.**
For any open `U ⊆ Tot(L)`, trivialization `e : O_Tot|_U ≅ O_U`, and open `W ⊆ X`, the local ring homomorphism
`Φ = projBundle.localRingHom (O ⊕ L) p O_Tot (toProjBundleQuotient L) U e W : A(W) → Γ(U ⊓ p⁻¹W, O)` sends the
degree-1 element `T_W = DirectSum.of _ 1 (oCoordinate L W)` to a unit.

Source: Stacks 01O4 (the morphism to `Proj` determined by an invertible quotient `ψ`; `Φ` in degree 1 is `ψ`
read through the trivialization); §4 of the paper (`Tot(L) = P(O ⊕ L) ∖ σ_L = {T ≠ 0}`).

## Proof
1. `localRingHom = DirectSum.toSemiring (localRingHomComponent …)`, so `Φ(DirectSum.of _ 1 x) =
   localRingHomComponent … 1 x` (`DirectSum.toSemiring_of`).
2. `localRingHomComponent … 1` is: pull the section `x ∈ Γ(W, Sym^1)` back along `g = (U ⊓ p⁻¹W) → Tot → X`
   (adjunction unit + restriction), then apply `Φ₁ = pullbackComp.inv ≫ g^*(symGradedPullbackDesc p ψ 1) ≫
   pullbackMonoidalPow ι M 1 ≫ monoidalPowMap e' 1 ≫ unitPowCollapse 1` on `Γ(U ⊓ p⁻¹W, -)`.
   In degree 1, `symGradedPullbackDesc p ψ 1` is `ψ` up to the identification `Sym^1 = id` (`symPowπ _ 1` is an
   isomorphism, `symGen = (λ_ _).inv ≫ symPowπ _ 1 ≫ eqToHom`, `WeightedSymGenerator.lean`), so `Φ₁` applied to
   the pull-back of `symGen(s)` is `e'(ψ(p^*s))` with `s = dualCurryMap fst (unitDualSection 1)`.
3. `p^*s` is the section `(1, 0)` of `p^*((O ⊕ L)^∨)`: it is `toProjBundleQuotientSection L` applied to `1`
   (`toProjBundleQuotientSection = pullbackUnitIso.inv ≫ p^*(unitDualSection ≫ dualCurryMap fst)`), and
   `toProjBundleQuotientSection ≫ toProjBundleQuotient = 𝟙` (`toProjBundleQuotientSection_comp`, proved), so
   `ψ(p^*s) = 1 ∈ Γ(U ⊓ p⁻¹W, O_Tot)`.
4. `e' : ι^*O_Tot ≅ O_{U ⊓ p⁻¹W}` is an isomorphism of modules; `1` generates `ι^*O_Tot`, so `e'(1)` generates
   `O`, i.e. is a unit of `Γ(U ⊓ p⁻¹W, O)` (`monoidalPowMap e' 1 ≫ unitPowCollapse 1` is `e'` up to the unitor).
   Hence `Φ(T_W)` is a unit.
Edge cases: `U ⊓ p⁻¹W = ∅` gives the zero ring, where `0` is a unit — the statement holds; `W` need not be affine.

## Formalization
Steps 1–2 are `DirectSum.toSemiring_of` + `projBundle.localRingHomComponent_one_symGen_apply`
(`TotLineAffineOverBaseDegreeOne.lean`; the sheaf-level form is `pullback_map_symGen_comp_localRingHomSheafHom_one`,
built on `Modules.pullback_map_symGen_comp_symGradedPullbackDesc_one` = oplax left unitality of `p^*`).
Step 3 is `toProjBundleQuotientSection_comp` rearranged (`Iso.inv_comp_eq`), step 4 is
`pullbackComp_hom_app_pullbackUnitIso_hom` + `homEquiv_pullbackUnitIso_hom_pbup` (the transposed morphism is
`g^♯` followed by the automorphism `k = pullbackUnitIso ι ⁻¹ ≫ e'` of `O_V`) and
`Modules.isUnit_unitIso_hom_sections_one` (`k(1)` is a unit). -/
theorem AlgebraicGeometry.Scheme.totalSpace.localRingHom_oCoordinate_isUnit {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (U : (AlgebraicGeometry.Scheme.totalSpace L).left.Opens)
    (e : (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
        SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf).restrict U.ι ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    IsUnit (AlgebraicGeometry.Scheme.projBundle.localRingHom
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
      (AlgebraicGeometry.Scheme.totalSpace L).hom
      (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
        SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf)
      (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) U e W
      (DirectSum.of _ 1 (AlgebraicGeometry.Scheme.totalSpace.oCoordinate L W))) := by
  -- Step 1: `localRingHom` on a degree-1 element is the degree-1 component (`DirectSum.toSemiring_of`).
  refine Eq.mpr (congrArg IsUnit (DirectSum.toSemiring_of _ _ _ 1 _)) ?_
  -- Step 2: the degree-1 component on `symGen s` is `ψ` read through the trivialization.
  refine Eq.mpr (congrArg IsUnit (projBundle.localRingHomComponent_one_symGen_apply _ _ _ _ U e W _)) ?_
  refine Eq.mpr (congrArg IsUnit (Modules.unit_presheaf_map_apply _ _)) ?_
  refine IsUnit.map _ ?_
  -- Step 3: `p^*(1 ↦ (1, 0)) ≫ ψ = (pullbackUnitIso p).hom` (`toProjBundleQuotientSection_comp`).
  have hψ : (Modules.pullback (totalSpace L).hom).map
        (Modules.unitDualSection X ≫ Modules.dualCurryMap
          (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        totalSpace.toProjBundleQuotient L = (Modules.pullbackUnitIso (totalSpace L).hom).hom := by
    have h := totalSpace.toProjBundleQuotientSection_comp L
    unfold AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotientSection at h
    rw [Category.assoc, Iso.inv_comp_eq, Category.comp_id] at h
    exact h
  -- Step 4: `pullbackUnitIso` is compatible with composition (`pullbackComp_hom_app_pullbackUnitIso_hom`).
  have e3 : (Modules.pullbackComp (projBundle.localRingHomIncl (totalSpace L).hom U W) (totalSpace L).hom).inv.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Modules.pullback (projBundle.localRingHomIncl (totalSpace L).hom U W)).map
        (Modules.pullbackUnitIso (totalSpace L).hom).hom ≫
      (Modules.pullbackUnitIso (projBundle.localRingHomIncl (totalSpace L).hom U W)).hom =
      (Modules.pullbackUnitIso (projBundle.localRingHomIncl (totalSpace L).hom U W ≫ (totalSpace L).hom)).hom := by
    rw [← Modules.pullbackComp_hom_app_pullbackUnitIso_hom]
    erw [Iso.inv_hom_id_app_assoc]
  -- Step 5: the morphism `g^*O_X → O_V` is `pullbackUnitIso g` followed by the automorphism `k` of `O_V`.
  have hθ : (Modules.pullback (projBundle.localRingHomBase (totalSpace L).hom U W)).map
        (Modules.unitDualSection X ≫ Modules.dualCurryMap
          (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        ((Modules.pullbackComp (projBundle.localRingHomIncl (totalSpace L).hom U W) (totalSpace L).hom).inv.app _ ≫
          (Modules.pullback (projBundle.localRingHomIncl (totalSpace L).hom U W)).map
            (totalSpace.toProjBundleQuotient L) ≫
          (projBundle.localRingHomTriv (totalSpace L).hom _ U e W).hom) =
      (Modules.pullbackUnitIso (projBundle.localRingHomBase (totalSpace L).hom U W)).hom ≫
        ((Modules.pullbackUnitIso (projBundle.localRingHomIncl (totalSpace L).hom U W)).symm ≪≫
          projBundle.localRingHomTriv (totalSpace L).hom _ U e W).hom := by
    unfold AlgebraicGeometry.Scheme.projBundle.localRingHomBase
    rw [(Modules.pullbackComp (projBundle.localRingHomIncl (totalSpace L).hom U W)
        (totalSpace L).hom).inv.naturality_assoc,
      Functor.comp_map,
      ← Category.assoc ((Modules.pullback (projBundle.localRingHomIncl (totalSpace L).hom U W)).map _),
      ← Functor.map_comp, hψ, ← e3, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
      Iso.hom_inv_id_assoc]
  -- Step 6: transpose (`homEquiv_naturality_left/right`, `homEquiv_pullbackUnitIso_hom_pbup`) and evaluate on
  -- `1 ∈ Γ(W, O_X)`: the value is `k(1)`, a unit (`isUnit_unitIso_hom_val_app_one`).
  have h1 := Adjunction.homEquiv_naturality_left
    (Modules.pullbackPushforwardAdjunction (projBundle.localRingHomBase (totalSpace L).hom U W))
    (Modules.unitDualSection X ≫ Modules.dualCurryMap
      (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)))
    ((Modules.pullbackComp (projBundle.localRingHomIncl (totalSpace L).hom U W) (totalSpace L).hom).inv.app _ ≫
      (Modules.pullback (projBundle.localRingHomIncl (totalSpace L).hom U W)).map
        (totalSpace.toProjBundleQuotient L) ≫
      (projBundle.localRingHomTriv (totalSpace L).hom _ U e W).hom)
  rw [hθ, Adjunction.homEquiv_naturality_right, Modules.homEquiv_pullbackUnitIso_hom_pbup] at h1
  have h2 := congrArg (fun m => (m.val.app (op W)).hom (1 : Γ(X, W))) h1
  have h4 : IsUnit (Modules.unitHomSections
      ((Modules.pullbackUnitIso (projBundle.localRingHomIncl (totalSpace L).hom U W)).symm ≪≫
        projBundle.localRingHomTriv (totalSpace L).hom _ U e W).hom
      (projBundle.localRingHomBase (totalSpace L).hom U W ⁻¹ᵁ W)
      (((projBundle.localRingHomBase (totalSpace L).hom U W).app W).hom (1 : Γ(X, W)))) := by
    rw [map_one]
    exact Modules.isUnit_unitIso_hom_sections_one _ _
  exact Eq.subst (motive := fun x : Γ((U ⊓ (totalSpace L).hom ⁻¹ᵁ W).toScheme,
    projBundle.localRingHomBase (totalSpace L).hom U W ⁻¹ᵁ W) => IsUnit x) h2 h4

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle in
/-- **`lSection` reads the O-coordinate as zero.**
For any open `U ⊆ X`, trivialization `e : L^∨|_U ≅ O_U`, and open `W ⊆ X`, the local ring homomorphism
`Ψ = projBundle.localRingHom (O ⊕ L) (𝟙 X) L^∨ (lSection.quotientMap L) U e W : A(W) → Γ(U ⊓ W, O)` kills the
degree-1 element `T_W = DirectSum.of _ 1 (oCoordinate L W)`: `σ_L ⊆ V₊(T)`.

Source: Stacks 01O4; §4 of the paper (`σ_L` is the section defined by the summand `L`, i.e. `{T = 0}`).

## Proof
1. As in `localRingHom_oCoordinate_isUnit`, `Ψ(DirectSum.of _ 1 x) = localRingHomComponent … 1 x`, and in degree
   1 this is `e'(ψ((𝟙)^*s))` with `ψ = lSection.quotientMap L = pullbackId.hom.app _ ≫ dualMap inr` and
   `s = dualCurryMap fst (unitDualSection 1)`.
2. `dualMap inr = dualCurryMap inr` (bridge `dualMap_eq`, `ModulesDualCurryMap.lean` /
   `ModulesDualMapFunctorial`), and `dualCurryMap fst ≫ dualCurryMap inr = dualCurryMap (inr ≫ fst) =
   dualCurryMap 0 = 0` (`dualCurryMap_fst_comp_inr`, proved). Hence `ψ((𝟙)^*s) = 0`, and `e'(0) = 0`.
Edge cases: `U ⊓ W = ∅`: both sides are `0` in the zero ring.

## Formalization
Same skeleton as `localRingHom_oCoordinate_isUnit` (`DirectSum.toSemiring_of`,
`projBundle.localRingHomComponent_one_symGen_apply`); the bridge `dualMap inr = dualCurryMap inr` is `rfl`
(`dualMap_eq`), so `(𝟙)^*(1 ↦ (1,0)) ≫ lSection.quotientMap L = 0` by naturality of `pullbackId` and
`dualCurryMap_fst_comp_inr`; `ι^*` and `homEquiv` are additive (`left_adjoint_additive`, `homAddEquiv`), and the
zero morphism has zero section maps (`(forget R).map_zero`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.localRingHom_lSection_oCoordinate_eq_zero
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (U : X.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.dual L).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.Opens) :
    AlgebraicGeometry.Scheme.projBundle.localRingHom
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
      (CategoryTheory.CategoryStruct.id X) (AlgebraicGeometry.Scheme.Modules.dual L)
      (AlgebraicGeometry.Scheme.lSection.quotientMap L) U e W
      (DirectSum.of _ 1 (AlgebraicGeometry.Scheme.totalSpace.oCoordinate L W)) = 0 := by
  -- Step 1: `localRingHom` on a degree-1 element is the degree-1 component (`DirectSum.toSemiring_of`).
  refine (DirectSum.toSemiring_of _ _ _ 1 _).trans ?_
  -- Step 2: the degree-1 component on `symGen s` is `ψ` read through the trivialization.
  refine (projBundle.localRingHomComponent_one_symGen_apply _ _ _ _ U e W _).trans ?_
  -- Step 3: `(𝟙)^*(1 ↦ (1, 0)) ≫ ψ = 0`: `dualMap inr = dualCurryMap inr` and `dualCurryMap fst ≫ dualCurryMap inr = 0`.
  have hu : (Modules.unitDualSection X ≫ Modules.dualCurryMap
        (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
      Modules.dualMap
        (biprod.inr (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) = 0 := by
    rw [Modules.dualMap_eq, Category.assoc]
    exact (congrArg (fun k => Modules.unitDualSection X ≫ k)
      (Modules.dualCurryMap_fst_comp_inr (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).trans
      comp_zero
  have hψ : (Modules.pullback (CategoryTheory.CategoryStruct.id X)).map
        (Modules.unitDualSection X ≫ Modules.dualCurryMap
          (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        lSection.quotientMap L = 0 := by
    unfold AlgebraicGeometry.Scheme.lSection.quotientMap
    rw [← Category.assoc, (Modules.pullbackId X).hom.naturality, Category.assoc, Functor.id_map, hu, comp_zero]
  haveI : (Modules.pullback (projBundle.localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).Additive :=
    (Modules.pullbackPushforwardAdjunction _).left_adjoint_additive
  have hθ : (Modules.pullback (projBundle.localRingHomBase (CategoryTheory.CategoryStruct.id X) U W)).map
        (Modules.unitDualSection X ≫ Modules.dualCurryMap
          (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        ((Modules.pullbackComp (projBundle.localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
            (CategoryTheory.CategoryStruct.id X)).inv.app _ ≫
          (Modules.pullback (projBundle.localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).map
            (lSection.quotientMap L) ≫
          (projBundle.localRingHomTriv (CategoryTheory.CategoryStruct.id X) _ U e W).hom) = 0 := by
    unfold AlgebraicGeometry.Scheme.projBundle.localRingHomBase
    rw [(Modules.pullbackComp (projBundle.localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
        (CategoryTheory.CategoryStruct.id X)).inv.naturality_assoc,
      Functor.comp_map,
      ← Category.assoc ((Modules.pullback (projBundle.localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).map _),
      ← Functor.map_comp, hψ, Functor.map_zero, zero_comp, comp_zero]
  -- Step 4: transpose (`homEquiv_naturality_left`, `homEquiv` is additive) and evaluate on `1`.
  haveI : (Modules.pullback (projBundle.localRingHomBase (CategoryTheory.CategoryStruct.id X) U W)).Additive :=
    (Modules.pullbackPushforwardAdjunction _).left_adjoint_additive
  have h1 := Adjunction.homEquiv_naturality_left
    (Modules.pullbackPushforwardAdjunction (projBundle.localRingHomBase (CategoryTheory.CategoryStruct.id X) U W))
    (Modules.unitDualSection X ≫ Modules.dualCurryMap
      (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)))
    ((Modules.pullbackComp (projBundle.localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
        (CategoryTheory.CategoryStruct.id X)).inv.app _ ≫
      (Modules.pullback (projBundle.localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).map
        (lSection.quotientMap L) ≫
      (projBundle.localRingHomTriv (CategoryTheory.CategoryStruct.id X) _ U e W).hom)
  rw [hθ] at h1
  have h0 : (Modules.pullbackPushforwardAdjunction
      (projBundle.localRingHomBase (CategoryTheory.CategoryStruct.id X) U W)).homEquiv _ _
      (0 : (Modules.pullback (projBundle.localRingHomBase (CategoryTheory.CategoryStruct.id X) U W)).obj
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
        (show (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.Modules from
          SheafOfModules.unit (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.ringCatSheaf)) = 0 :=
    map_zero ((Modules.pullbackPushforwardAdjunction
      (projBundle.localRingHomBase (CategoryTheory.CategoryStruct.id X) U W)).homAddEquiv _ _)
  rw [h0] at h1
  have h2 := congrArg (fun m => (m.val.app (op W)).hom (1 : Γ(X, W))) h1
  have h3 : ((0 : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (Modules.pushforward (projBundle.localRingHomBase (CategoryTheory.CategoryStruct.id X) U W)).obj
        (show (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.Modules from
          SheafOfModules.unit (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.ringCatSheaf)).val.app
        (op W)).hom (1 : Γ(X, W)) = 0 := by
    rw [show ((0 : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ _)).val = 0 from
      Functor.map_zero (SheafOfModules.forget _) _ _]
    rfl
  exact (congrArg ((Modules.presheaf
      (SheafOfModules.unit (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.ringCatSheaf)).map
      (homOfLE (projBundle.localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U W)).op).hom
    (h2.symm.trans h3)).trans (map_zero _)

end DegreeOneLeaves

/-- **The image lies in the complement `Tot(L) ⊆ P(O ⊕ L)` of `σ_L`** (the `O`-coordinate is everywhere
invertible).

Source: §4 of the paper; Stacks 01O4 (local construction of morphisms to `Proj`), 01M9/01MN (`D₊(f)`).

## Proof
Write `p : Tot = Spec_X Sym(L^∨) → X`, `π : P = P(O ⊕ L) → X`, `τ = toProjBundle L`. We show that for every
`t ∈ Tot`, `τ(t) ∉ σ_L(X)` (i.e. `τ(t) ∈ (Set.range (lSection L).base)ᶜ`).

1. **Local pieces.** The definition of `projBundle.lift` (`ProjectiveBundleUniversalProperty.lean`) chooses, for `t`,
   an open `U_t` trivializing `O_Tot` (here `M = O_Tot`, and the trivialization `e_t` is an automorphism of `O`,
   i.e. multiplication by a unit `u_t`), an affine neighbourhood `W_t ⊆ X` of `f(t)`, and an affine open `V_t ∋ t`
   with `V_t ⊆ U_t ⊓ p⁻¹W_t`, and glues the local pieces `liftLocal` along the cover `{V_t}`; by Mathlib's
   `Scheme.Cover.ι_glueMorphisms`, `τ|_{V_t} = liftLocal … V_t`, which is
   `Proj.fromOfGlobalSections φ_t ≫ (relativeProj.affineIso S W_t).inv ≫ (π⁻¹W_t).ι`,
   where `S = Sym((O ⊕ L)^∨)`, `A := S(W_t) = ⊕_m Γ(W_t, Sym^m((O ⊕ L)^∨))`, and `φ_t : A → Γ(V_t, O)` is
   `localRingHom` (each graded component is read from the `m`-th power of the invertible quotient
   `toProjBundleQuotient` through `e_t`).
2. **The `O`-coordinate.** Let `T ∈ A_1 = Γ(W_t, (O ⊕ L)^∨)` be the coordinate function `dualCurryMap fst (1)` of
   the `O`-component (i.e. `(a, λ) ↦ a`). `φ_t(T)` is the value of the invertible quotient on the pullback of `T`,
   read through `e_t`: the `O`-component of `toProjBundleQuotient` sends `(1, 0)` to `1`
   (`toProjBundleQuotientSection_comp_O`) and the `L`-component sends it to `0` (`…_comp_L`), so `φ_t(T) = u_t · 1`
   is a unit of `Γ(V_t, O)`. By Mathlib's `Proj.fromOfGlobalSections_preimage_basicOpen`,
   `(fromOfGlobalSections φ_t)⁻¹ D₊(T) = V_t.basicOpen (φ_t T) = V_t`, i.e. `τ(V_t) ⊆ image(D₊(T))` through
   `affineIso` and `ι`.
3. **`σ_L` lies in `V₊(T)`.** `lSection L = projBundle.lift … (dualMap inr)` is likewise locally
   `fromOfGlobalSections ψ_x`, and `ψ_x(T) = (dualMap fst ≫ dualMap inr)(1) = 0` (`dualCurryMap_fst_comp_inr`, via
   the bridge `dualMap = dualCurryMap`), so `(fromOfGlobalSections ψ_x)⁻¹ D₊(T) = basicOpen 0 = ∅`:
   `σ_L(X) ∩ image(D₊(T)) = ∅` (over `π⁻¹W_t`).
4. Hence `τ(t) ∈ image(D₊(T))`, which is disjoint from `σ_L(X)`, so `τ(t) ∉ σ_L(X)`.

## Formalization (the proof body is assembled from named lemmas)
* `projBundle.lift_restrict` (`TotLineAffineOverBaseLiftRestrict.lean`): `lift` restricted to any admissible piece
  `(U, e, W, V')` equals `liftLocal` (this depends only on `liftLocal_compat`) — so `toProjBundle` at `t` and
  `lSection` at `p(t)` can be read on the **same** affine chart `W` (the `choose` data of step 1 disappear);
* `projBundle.liftLocal_base_ne` (same file): two pieces on the same chart `W`, one of which reads a degree-one
  element `r` as a unit and the other as `0`, have disjoint images (Mathlib's
  `Proj.fromOfGlobalSections_preimage_basicOpen`; steps 2–4);
* `localRingHom_oCoordinate_isUnit`: step 2, `φ_t(T)` is a unit;
* `localRingHom_lSection_oCoordinate_eq_zero`: step 3, `ψ_x(T) = 0`.
In step 1, `x = p(t)` follows from `lift_hom` and `lSection_comp`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.range_toProjBundle_le {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    Set.range (AlgebraicGeometry.Scheme.totalSpace.toProjBundle L).base ⊆
      (Set.range (AlgebraicGeometry.Scheme.lSection L).base)ᶜ := by
  haveI hepi : CategoryTheory.Epi (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) :=
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient_epi L
  haveI hepi' : CategoryTheory.Epi (AlgebraicGeometry.Scheme.lSection.quotientMap L) :=
    AlgebraicGeometry.Scheme.lSection.quotientMap_epi L
  rintro q ⟨t, rfl⟩
  show (AlgebraicGeometry.Scheme.totalSpace.toProjBundle L).base t ∈
    (Set.range (AlgebraicGeometry.Scheme.lSection L).base)ᶜ
  rintro ⟨x, hx⟩
  -- Step 1: both points lie over `p t`, so `x = p t`.
  have hπl : (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom.base
        ((AlgebraicGeometry.Scheme.lSection L).base x) = x := by
    change (AlgebraicGeometry.Scheme.lSection L ≫ (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom).base x = x
    rw [AlgebraicGeometry.Scheme.lSection_comp]
    rfl
  have hπt : (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom.base
        ((AlgebraicGeometry.Scheme.totalSpace.toProjBundle L).base t) =
      (AlgebraicGeometry.Scheme.totalSpace L).hom.base t := by
    change (AlgebraicGeometry.Scheme.totalSpace.toProjBundle L ≫ (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom).base t = _
    rw [show AlgebraicGeometry.Scheme.totalSpace.toProjBundle L ≫ (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom =
        (AlgebraicGeometry.Scheme.totalSpace L).hom from
      AlgebraicGeometry.Scheme.projBundle.lift_hom _ _ _ _]
  have hxt : x = (AlgebraicGeometry.Scheme.totalSpace L).hom.base t := by
    have h := congrArg (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom.base hx
    rw [hπl, hπt] at h
    exact h
  subst hxt
  -- Step 2: a common affine chart `W ∋ p t` and admissible pieces for both lifts.
  obtain ⟨W, hWaff, hxW, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (x := (AlgebraicGeometry.Scheme.totalSpace L).hom.base t) (U := ⊤) trivial
  obtain ⟨U₁, htU₁, ⟨e₁⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial
    (M := (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
      SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf)) t
  obtain ⟨V₁, hV₁, htV₁, hV₁le⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t)
    (U := U₁ ⊓ (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W) ⟨htU₁, hxW⟩
  obtain ⟨U₂, hxU₂, ⟨e₂⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial
    (M := AlgebraicGeometry.Scheme.Modules.dual L) ((AlgebraicGeometry.Scheme.totalSpace L).hom.base t)
  obtain ⟨V₂, hV₂, hxV₂, hV₂le⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (x := (AlgebraicGeometry.Scheme.totalSpace L).hom.base t)
    (U := U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W) ⟨hxU₂, hxW⟩
  -- Step 3: read both points on the local pieces (`lift_restrict`).
  have h₁ : (AlgebraicGeometry.Scheme.totalSpace.toProjBundle L).base t =
      (AlgebraicGeometry.Scheme.projBundle.liftLocal _ (AlgebraicGeometry.Scheme.totalSpace L).hom _
        (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) U₁ e₁ ⟨W, hWaff⟩ V₁ hV₁ hV₁le).base
        ⟨t, htV₁⟩ := by
    rw [← AlgebraicGeometry.Scheme.projBundle.lift_restrict _ (AlgebraicGeometry.Scheme.totalSpace L).hom _
      (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) U₁ e₁ ⟨W, hWaff⟩ V₁ hV₁ hV₁le]
    rfl
  have h₂ : (AlgebraicGeometry.Scheme.lSection L).base ((AlgebraicGeometry.Scheme.totalSpace L).hom.base t) =
      (AlgebraicGeometry.Scheme.projBundle.liftLocal _ (CategoryTheory.CategoryStruct.id X) _
        (AlgebraicGeometry.Scheme.lSection.quotientMap L) U₂ e₂ ⟨W, hWaff⟩ V₂ hV₂ hV₂le).base
        ⟨_, hxV₂⟩ := by
    rw [← AlgebraicGeometry.Scheme.projBundle.lift_restrict _ (CategoryTheory.CategoryStruct.id X) _
      (AlgebraicGeometry.Scheme.lSection.quotientMap L) U₂ e₂ ⟨W, hWaff⟩ V₂ hV₂ hV₂le]
    rfl
  -- Step 4: the O-coordinate is a unit for `toProjBundle` and zero for `lSection`; the pieces are disjoint.
  exact AlgebraicGeometry.Scheme.projBundle.liftLocal_base_ne _
    (AlgebraicGeometry.Scheme.totalSpace L).hom _ (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L)
    (CategoryTheory.CategoryStruct.id X) _ (AlgebraicGeometry.Scheme.lSection.quotientMap L)
    ⟨W, hWaff⟩ U₁ e₁ V₁ hV₁ hV₁le U₂ e₂ V₂ hV₂ hV₂le ⟨t, htV₁⟩ ⟨_, hxV₂⟩
    (DirectSum.of _ 1 (AlgebraicGeometry.Scheme.totalSpace.oCoordinate L W))
    (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)
    (AlgebraicGeometry.Scheme.totalSpace.localRingHom_oCoordinate_isUnit L U₁ e₁ W)
    (AlgebraicGeometry.Scheme.totalSpace.localRingHom_lSection_oCoordinate_eq_zero L U₂ e₂ W)
    (h₁.symm.trans (hx.symm.trans h₂))

section IsIsoLeaves

/-! ## `toProjBundle` is an open immersion with image `P(O ⊕ L) ∖ σ_L(X)`: lemmas and glue

* **open immersion** (`toProjBundle_isOpenImmersion`): local on the target `P(O ⊕ L)`, covered by the `π⁻¹W`
  (`W ⊆ X` affine); on `π⁻¹W` the restriction of `toProjBundle` is the canonical local piece
  `liftLocal` over `V' = p⁻¹W` (`projBundle.lift_restrict`), i.e. `fromOfGlobalSections φ_W ≫ affineIso⁻¹ ≫ ι`,
  and `fromOfGlobalSections φ_W` is an open immersion because `φ_W(T)` is a unit and the degree-zero fraction map
  `(A(W)_T)_0 → Γ(p⁻¹W, O)[1/φ_W T]` is bijective (`toProjBundle_awayMap_bijective` +
  `Proj.isOpenImmersion_fromOfGlobalSections_of_bijective`, `TotLineAffineOverBaseFromOfGlobalSectionsIso.lean`).
* **image** (`compl_range_lSection_le_range_toProjBundle`, hence `range_toProjBundle_eq`): every point `q` of
  `P ∖ σ_L(X)` is in the image of `toProjBundle`. Over an affine chart `W ∋ π q` trivialising `L^∨`, move `q` to
  `Proj A(W)`; if `q ∈ D₊(T)` it is in the image of `fromOfGlobalSections φ_W` (same bijectivity), otherwise
  `q ∈ V₊(T) = σ_L(W)` (`mem_range_lSection_of_not_mem_basicOpen_oCoordinate`), contradicting `q ∉ σ_L(X)`.
-/

/-- **`structureHom` on the structure map**: `structureHom (sectionsUnit W r) = π^♯ r` for the relative Spec
`π : Spec_X A → X`. `sectionsUnit W r = A.one.app W (r • 1) = r • A.one.app W 1`, `structureHom` is
`O_X`-linear (`Hom.app_smul`) and sends `A.one.app W 1` to `1` (the unit clause of `relativeSpecHomEquiv … (𝟙 _)`),
and the `Γ(W, O_X)`-action on `Γ(π_* O, W) = Γ(Spec_X A, π⁻¹W)` is multiplication by `π^♯ r`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_sectionsUnit {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (W : X.Opens) (r : Γ(X, W)) :
    ((AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app W (A.sectionsUnit W r) :
      Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ W)) =
      (AlgebraicGeometry.Scheme.relativeSpec A).hom.app W r := by
  have h1 : A.sectionsUnit W r = A.one.app W (r • (show Γ(𝟙_ X.Modules, W) from (1 : Γ(X, W)))) := by
    show A.one.app W r = A.one.app W _
    congr 1
    exact (mul_one r).symm
  have hu : ((AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app W (A.one.app W (show Γ(X, W) from 1)) :
      Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ W)) =
      (1 : Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ W)) :=
    (AlgebraicGeometry.Scheme.relativeSpecHomEquiv A (AlgebraicGeometry.Scheme.relativeSpec A)
      (CategoryTheory.CategoryStruct.id _)).2.2 W
  rw [h1, AlgebraicGeometry.Scheme.Modules.Hom.app_smul, AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
  change r • ((AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app W (A.one.app W (show Γ(X, W) from 1))) = _
  rw [hu]
  show (AlgebraicGeometry.Scheme.relativeSpec A).hom.app W r * 1 = _
  exact mul_one _

/-- **The canonical local piece `φ_W` of `toProjBundle L` over an affine chart `W`**: the local ring homomorphism
`A(W) → Γ(p⁻¹W, O_Tot)` of `projBundle.lift (O ⊕ L) p O_Tot ψ` for `U = V' = p⁻¹W` and the canonical trivialization
`e = restrictUnitIso` (`projBundle.localRingHom`), restricted from `U ⊓ p⁻¹W = p⁻¹W ⊓ p⁻¹W` to `p⁻¹W`
(it is the ring homomorphism appearing in `toProjBundle_awayMap_bijective`). -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.canonicalPiece {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (W : X.affineOpens) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing W.1 →+*
      Γ(((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1).toScheme, ⊤) :=
  ((AlgebraicGeometry.Scheme.totalSpace L).left.homOfLE
      (le_inf le_rfl le_rfl : (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1 ≤
        (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1 ⊓
          (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom.comp
    (AlgebraicGeometry.Scheme.projBundle.localRingHom
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
      (AlgebraicGeometry.Scheme.totalSpace L).hom
      (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
        SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf)
      (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L)
      ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1)
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1).ι)
      W.1)

/-- `T_W = DirectSum.of 1 (oCoordinate L W)` is the degree-one generator `genSections (oFunctional ε W)` of the graded
model, for `ε = unitDualIso X` (definitional). -/
theorem AlgebraicGeometry.Scheme.totalSpace.of_oCoordinate_eq_genSections_oFunctional
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (W : X.Opens) :
    (DirectSum.of _ 1 (AlgebraicGeometry.Scheme.totalSpace.oCoordinate L W) :
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing W) =
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebra.genSections _ W
        (AlgebraicGeometry.Scheme.totalSpace.oFunctional L (AlgebraicGeometry.Scheme.Modules.unitDualIso X) W) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **`φ_W` in degree zero**: on the structure map
`sectionsUnitHom W r = DirectSum.of 0 (r • 1)` the canonical piece is the pull-back `p^♯ r` of `r` to `p⁻¹W`, which is
also `symSectionsToFunctions (algebraMap r)` (`TotLineAffineOverBaseGradedModel.lean`).

## Proof
* Left side: `localRingHom_sectionsUnit` (`ProjectiveBundleUniversalProperty.lean`) gives
  `φ(sectionsUnit W r) = (g.appLE W ⊤ _) r` with `g = localRingHomBase p (p⁻¹W) W = ι ≫ p`, `ι : (p⁻¹W ⊓ p⁻¹W) ↪ Tot`;
  composing with `(homOfLE _).appTop` gives `((homOfLE _ ≫ ι ≫ p).appLE W ⊤ _) r` (`Scheme.Hom.appLE_comp_appLE`,
  `comp_appLE`), and `homOfLE _ ≫ ι = (p⁻¹W).ι` (`Scheme.homOfLE_ι`), so the value is `((p⁻¹W).ι ≫ p).appLE W ⊤ _ r`.
* Right side: `symSectionsToFunctions_algebraMap` gives `topIso.inv (structureHom.app W (sectionsUnit W r))`;
  `sectionsUnit W r = r • 1` in `Γ(W, Sym(L^∨))` (`QCAlgebra.smul_eq_sectionsUnit_mul` with `a = 1`), `structureHom`
  is `O_X`-linear (`Hom.app_smul`) and unital (`structureHom_app_apply`: it is the ring-sheaf map `structureRingMap`),
  so `structureHom.app W (sectionsUnit W r) = r • 1 = p.appLE W (p⁻¹W) le_rfl r` (the `Γ(W, O_X)`-action on
  `Γ(p_* O_Tot, W) = Γ(Tot, p⁻¹W)` is through `p^♯`: `Modules.pushforward` is `restrictScalars` along `p^♯`,
  definitionally). Finally `topIso.inv = (p⁻¹W).ι.appLE (p⁻¹W) ⊤ _` (`Opens.topIso_inv`, `Opens.ι_appLE`), and
  `(p⁻¹W).ι.appLE _ ⊤ _ (p.appLE W _ _ r) = ((p⁻¹W).ι ≫ p).appLE W ⊤ _ r` (`appLE_comp_appLE`).
Edge cases: `W = ∅` (zero rings).
Formalized along exactly this route (`relativeSpec.structureHom_app_sectionsUnit` for the right side;
the left side is a composite of `presheaf.map`s of the total space, equal to the right side because morphisms of
opens are unique). -/
theorem AlgebraicGeometry.Scheme.totalSpace.canonicalPiece_sectionsUnitHom {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (W : X.affineOpens) (r : Γ(X, W.1)) :
    AlgebraicGeometry.Scheme.totalSpace.canonicalPiece L W
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsUnitHom W.1 r) =
      AlgebraicGeometry.Scheme.totalSpace.symSectionsToFunctions L W (algebraMap Γ(X, W.1) _ r) := by
  rw [AlgebraicGeometry.Scheme.totalSpace.symSectionsToFunctions_algebraMap,
    AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_sectionsUnit]
  show ((AlgebraicGeometry.Scheme.totalSpace L).left.homOfLE
      (le_inf le_rfl le_rfl : (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1 ≤
        (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1 ⊓
          (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom
    (AlgebraicGeometry.Scheme.projBundle.localRingHom _ (AlgebraicGeometry.Scheme.totalSpace L).hom _
      (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L)
      ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1) (AlgebraicGeometry.Scheme.Modules.restrictUnitIso _) W.1
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual _)).sectionsUnit
        W.1 r).1) = _
  rw [AlgebraicGeometry.Scheme.projBundle.localRingHom_sectionsUnit]
  unfold AlgebraicGeometry.Scheme.projBundle.localRingHomBase AlgebraicGeometry.Scheme.projBundle.localRingHomIncl
  rw [AlgebraicGeometry.Scheme.Hom.comp_appLE, AlgebraicGeometry.Scheme.Hom.comp_appLE,
    AlgebraicGeometry.Scheme.Opens.ι_app, AlgebraicGeometry.Scheme.homOfLE_appLE,
    AlgebraicGeometry.Scheme.homOfLE_appTop, AlgebraicGeometry.Scheme.Opens.topIso_inv]
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  erw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k => ((AlgebraicGeometry.Scheme.totalSpace L).left.presheaf.map k).hom
    (AlgebraicGeometry.Scheme.Hom.app (AlgebraicGeometry.Scheme.totalSpace L).hom W.1 r)) (Subsingleton.elim _ _)

section DegreeOneTranspose

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.totalSpace

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle

variable {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]

/-- **The transpose of the invertible quotient** `ψ = toProjBundleQuotient L : p^*((O ⊕ L)^∨) → O_Tot` along `p`:
`(inl)^∨ ≫ dualUnitEval ≫ p^♯ + (inr)^∨ ≫ θ`, `θ = symGen ≫ totalIncl 1 ≫ structureHom` (the `O`-part transposes
to the structure map of `O_Tot`, the `L`-part to `θ` because `ξ = tautologicalFunctional` is the transpose of `θ`). -/
theorem homEquiv_toProjBundleQuotient :
    (pullbackPushforwardAdjunction (totalSpace L).hom).homEquiv _ _ (toProjBundleQuotient L) =
      ((dualCurryMap (biprod.inl (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Y := L)) ≫ dualUnitEval X) ≫
        SheafOfModules.unitToPushforwardObjUnit (totalSpace L).hom.toRingCatSheafHom :
          dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) ⟶
            (Modules.pushforward (totalSpace L).hom).obj
              (SheafOfModules.unit (totalSpace L).left.ringCatSheaf)) +
      (dualCurryMap (biprod.inr (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Y := L)) ≫
        (symGen (dual L) ≫ (symGradedAlgebra (dual L)).totalIncl 1 ≫
          relativeSpec.structureHom (symGradedAlgebra (dual L)).total) :
          dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) ⟶
            (Modules.pushforward (totalSpace L).hom).obj
              (SheafOfModules.unit (totalSpace L).left.ringCatSheaf)) := by
  haveI : (Modules.pullback (totalSpace L).hom).Additive :=
    (pullbackPushforwardAdjunction (totalSpace L).hom).left_adjoint_additive
  unfold toProjBundleQuotient toProjBundleQuotientO toProjBundleQuotientL tautologicalFunctional
  rw [Adjunction.homAddEquiv_add, Adjunction.homEquiv_naturality_left, homEquiv_pullbackUnitIso_hom_pbup,
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]

theorem homEquiv_toProjBundleQuotient_app_sLinear (W : X.Opens) (n : Γ(dual L, W)) :
    Modules.Hom.app ((pullbackPushforwardAdjunction (totalSpace L).hom).homEquiv _ _ (toProjBundleQuotient L)) W
        (sLinear L W n) =
      Modules.Hom.app (symGen (dual L) ≫ (symGradedAlgebra (dual L)).totalIncl 1 ≫
        relativeSpec.structureHom (symGradedAlgebra (dual L)).total) W n := by
  have h0 : Modules.Hom.app (dualUnitEval X) W (Modules.Hom.app (dualCurryMap (biprod.inl (C := X.Modules)
      (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) W (sLinear L W n)) = 0 := by
    have := congrArg (fun k => Modules.Hom.app k W n) (show dualCurryMap (biprod.snd (C := X.Modules)
      (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
      dualCurryMap (biprod.inl (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
        (Y := L)) ≫ dualUnitEval X = 0 by rw [← Category.assoc, dualCurryMap_snd_comp_inl, zero_comp])
    exact this
  have h1 : Modules.Hom.app (dualCurryMap (biprod.inr (C := X.Modules)
      (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) W (sLinear L W n) = n := by
    have := congrArg (fun k => Modules.Hom.app k W n) (dualCurryMap_snd_comp_inr
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
    exact this
  rw [homEquiv_toProjBundleQuotient, Hom.add_app, AddCommGrpCat.hom_add_apply]
  simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [h0, h1, map_zero, zero_add]
  rfl

theorem homEquiv_toProjBundleQuotient_app_oFunctional (W : X.Opens) :
    Modules.Hom.app ((pullbackPushforwardAdjunction (totalSpace L).hom).homEquiv _ _ (toProjBundleQuotient L)) W
        (oFunctional L (unitDualIso X) W) = (1 : Γ((totalSpace L).left, (totalSpace L).hom ⁻¹ᵁ W)) := by
  have h0 : Modules.Hom.app (dualUnitEval X) W (Modules.Hom.app (dualCurryMap (biprod.inl (C := X.Modules)
      (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) W (oFunctional L (unitDualIso X) W)) =
      (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W) from (1 : Γ(X, W))) := by
    have := congrArg (fun k => Modules.Hom.app k W (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W)
      from (1 : Γ(X, W)))) (show (unitDualSection X ≫ dualCurryMap (biprod.fst (C := X.Modules)
        (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        dualCurryMap (biprod.inl (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Y := L)) ≫ dualUnitEval X = 𝟙 _ by
      rw [Category.assoc, ← Category.assoc (dualCurryMap _), dualCurryMap_fst_comp_inl, Category.id_comp,
        unitDualSection_comp_dualUnitEval])
    exact this
  have h1 : Modules.Hom.app (dualCurryMap (biprod.inr (C := X.Modules)
      (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) W (oFunctional L (unitDualIso X) W) =
      0 := by
    have := congrArg (fun k => Modules.Hom.app k W (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W)
      from (1 : Γ(X, W)))) (show (unitDualSection X ≫ dualCurryMap (biprod.fst (C := X.Modules)
        (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) ≫
        dualCurryMap (biprod.inr (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Y := L)) = 0 by rw [Category.assoc, dualCurryMap_fst_comp_inr, comp_zero])
    exact this
  rw [homEquiv_toProjBundleQuotient, Hom.add_app, AddCommGrpCat.hom_add_apply]
  simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [h0, h1, map_zero, map_zero, map_zero, add_zero]
  exact map_one ((totalSpace L).hom.toRingCatSheafHom.hom.app (op W)).hom

/-- `φ_W` on a degree-one generator `genSections m`, as an adjoint transpose (`localRingHomComponent_one_symGen_apply_transpose`). -/
theorem canonicalPiece_genSections_eq_transpose (W : X.affineOpens)
    (m : Γ(dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W.1)) :
    canonicalPiece L W (symGradedAlgebra.genSections _ W.1 m) =
      ((totalSpace L).left.homOfLE (le_inf le_rfl le_rfl : (totalSpace L).hom ⁻¹ᵁ W.1 ≤
          (totalSpace L).hom ⁻¹ᵁ W.1 ⊓ (totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom
        (((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit
            ((totalSpace L).hom ⁻¹ᵁ W.1 ⊓ (totalSpace L).hom ⁻¹ᵁ W.1).toScheme.ringCatSheaf)).map
            (homOfLE (localRingHomBase_top_le (totalSpace L).hom ((totalSpace L).hom ⁻¹ᵁ W.1) W.1)).op).hom
          (Modules.Hom.app (localRingHomUnitAut (totalSpace L).hom ((totalSpace L).hom ⁻¹ᵁ W.1)
              (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W.1).hom
            (localRingHomIncl (totalSpace L).hom ((totalSpace L).hom ⁻¹ᵁ W.1) W.1 ⁻¹ᵁ ((totalSpace L).hom ⁻¹ᵁ W.1))
            ((localRingHomIncl (totalSpace L).hom ((totalSpace L).hom ⁻¹ᵁ W.1) W.1).app ((totalSpace L).hom ⁻¹ᵁ W.1)
              (Modules.Hom.app ((pullbackPushforwardAdjunction (totalSpace L).hom).homEquiv _ _ (toProjBundleQuotient L))
                W.1 m)))) := by
  show ((totalSpace L).left.homOfLE (le_inf le_rfl le_rfl : (totalSpace L).hom ⁻¹ᵁ W.1 ≤
      (totalSpace L).hom ⁻¹ᵁ W.1 ⊓ (totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom
    (localRingHom _ (totalSpace L).hom _ (toProjBundleQuotient L)
    ((totalSpace L).hom ⁻¹ᵁ W.1) (restrictUnitIso _) W.1
    (DirectSum.of _ 1 (((symGen (dual _)).val.app (op W.1)).hom m))) = _
  unfold localRingHom
  erw [DirectSum.toSemiring_of]
  rw [localRingHomComponent_one_symGen_apply_transpose]

end AlgebraicGeometry.Scheme.totalSpace

end DegreeOneTranspose

set_option backward.isDefEq.respectTransparency.types false in
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle in
/-- **`φ_W` in degree one on the `L^∨`-generators**: for
`n ∈ Γ(W, L^∨)`, viewed as the functional `s n = (a, l) ↦ n(l)` on `O ⊕ L` (`sLinear`), the canonical piece sends the
degree-one generator `ι(s n) = DirectSum.of 1 (symGen (s n))` to `φ_W(T) · (fibre coordinate of n)`, where
`φ_W(T) = φ_W(DirectSum.of 1 (oCoordinate L W))` is the (unit) value on the `O`-coordinate and the fibre coordinate
of `n` is `symSectionsToFunctions (ι n) = structureHom (totalIncl 1 (symGen n))|_{p⁻¹W}` (`symSectionsToFunctions_ι`).

## Natural-language proof (self-contained; not yet formalized)
Write `ψ = toProjBundleQuotient L = ψ_O + ψ_L`, `ψ_O = p^*((inl)^∨ ≫ dualUnitEval) ≫ pullbackUnitIso.hom`,
`ψ_L = p^*((inr)^∨) ≫ ξ`, `ξ = tautologicalFunctional L = homEquiv⁻¹(θ)`, `θ = symGen ≫ totalIncl 1 ≫ structureHom :
L^∨ → p_* O_Tot`; `ι : V' = p⁻¹W ⊓ p⁻¹W ↪ Tot`, `g = ι ≫ p`, `e' = localRingHomTriv p O_Tot (p⁻¹W) (restrictUnitIso) W`,
and `k = (pullbackUnitIso ι).symm ≪≫ e' : O_{V'} ≅ O_{V'}` (an automorphism of the structure sheaf as a module, hence
multiplication by `k(1)`: `k(x) = k(x • 1) = x • k(1)`, `Hom.app_smul`).
1. `DirectSum.toSemiring_of` + `localRingHomComponent_one_symGen_apply` (`TotLineAffineOverBaseDegreeOne.lean`):
   `φ(DirectSum.of 1 (symGen m)) = res_{⊤ ≤ g⁻¹W} ((homEquiv_g (pullbackComp.inv ≫ ι^*ψ ≫ e'.hom)).app W m)` for every
   `m ∈ Γ(W, (O ⊕ L)^∨)`; the adjunction `homEquiv` is additive, so this splits as the `ψ_O`-part plus the `ψ_L`-part.
2. **`ψ_O`-part on `m = s n`**: `(inl)^∨ ∘ (snd)^∨ = ((inl ≫ snd))^∨ = 0` (`dualCurryMap_snd_comp_inl`), so
   `p^*((inl)^∨ ≫ dualUnitEval)` kills `p^*(s n)`; the part is `0`.
3. **`ψ_L`-part on `m = s n`**: `(inr)^∨ ∘ (snd)^∨ = 𝟙` (`dualCurryMap_snd_comp_inr`), so it is
   `res ((homEquiv_g (pullbackComp.inv ≫ ι^*ξ ≫ e'.hom)).app W n)`. Transposing along the composite adjunction
   (`homEquiv_pullbackComp_hom_app_comp`, `ModulesPullbackCompMonoidal.lean`; as in step 5 of
   `localRingHom_oCoordinate_isUnit`): `homEquiv_g (pullbackComp.inv ≫ ι^*ξ ≫ e') = homEquiv_p (ξ ≫ homEquiv_ι e')`
   `= θ ≫ p_*(homEquiv_ι e')` (`homEquiv_naturality_right`, `homEquiv (homEquiv⁻¹ θ) = θ`), and
   `homEquiv_ι e' = homEquiv_ι (pullbackUnitIso ι).hom ≫ ι_* k = unitToPushforwardObjUnit ι ≫ ι_* k`
   (`homEquiv_pullbackUnitIso_hom_pbup`), i.e. "restrict to `V'`, then apply `k`". On the section `n`:
   `k(res_{V'}(θ.app W n)) = res_{V'}(θ.app W n) • k(1)`.
4. **The unit**: by the same computation with `m = T` (steps 3–6 of `localRingHom_oCoordinate_isUnit`),
   `φ(DirectSum.of 1 (oCoordinate L W)) = res (k(g^♯ 1)) = res (k(1))`.
5. Assemble: `φ(ι(s n)) = res(res_{V'}(θ.app W n) • k(1)) = φ(T) · res(res_{V'}(θ.app W n))`, and the last factor is
   `topIso.inv (θ.app W n) = symSectionsToFunctions (ι n)` (`symSectionsToFunctions_ι`, restriction bookkeeping
   `homOfLE _ ≫ ι = (p⁻¹W).ι`, `Opens.topIso_inv`).
Edge cases: `W = ∅` (zero rings).
Formalized along exactly this route: the two-step transpose is
`localRingHomComponent_one_symGen_apply_transpose` (`TotLineAffineOverBaseDegreeOneTranspose.lean`), the transpose
of `ψ` is `homEquiv_toProjBundleQuotient` (evaluated in `homEquiv_toProjBundleQuotient_app_sLinear` /
`_app_oFunctional`), `k` is multiplication by `k(1)` (`unitHomSections_mul`), and the restriction bookkeeping is
`homOfLE_appTop_map_localRingHomIncl_app`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.canonicalPiece_genSections_sLinear {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (W : X.affineOpens) (n : Γ(AlgebraicGeometry.Scheme.Modules.dual L, W.1)) :
    AlgebraicGeometry.Scheme.totalSpace.canonicalPiece L W
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra.genSections
          (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) W.1
          (AlgebraicGeometry.Scheme.totalSpace.sLinear L W.1 n)) =
      AlgebraicGeometry.Scheme.totalSpace.canonicalPiece L W
          (DirectSum.of _ 1 (AlgebraicGeometry.Scheme.totalSpace.oCoordinate L W.1)) *
        AlgebraicGeometry.Scheme.totalSpace.symSectionsToFunctions L W
          (SymmetricAlgebra.ι Γ(X, W.1) Γ(AlgebraicGeometry.Scheme.Modules.dual L, W.1) n) := by
  rw [of_oCoordinate_eq_genSections_oFunctional, canonicalPiece_genSections_eq_transpose,
    canonicalPiece_genSections_eq_transpose, homEquiv_toProjBundleQuotient_app_sLinear,
    homEquiv_toProjBundleQuotient_app_oFunctional, map_one, symSectionsToFunctions_ι]
  set k := localRingHomUnitAut (totalSpace L).hom ((totalSpace L).hom ⁻¹ᵁ W.1)
    (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W.1 with hk
  set V'' := localRingHomIncl (totalSpace L).hom ((totalSpace L).hom ⁻¹ᵁ W.1) W.1 ⁻¹ᵁ ((totalSpace L).hom ⁻¹ᵁ W.1)
    with hV''
  have hlin : ∀ y : Γ(((totalSpace L).hom ⁻¹ᵁ W.1 ⊓ (totalSpace L).hom ⁻¹ᵁ W.1).toScheme, V''),
      y * unitHomSections k.hom V'' 1 = Modules.Hom.app k.hom V'' y := fun y => by
    have := unitHomSections_mul k.hom V'' y 1
    rw [mul_one] at this
    exact this.symm
  rw [← hlin, unit_presheaf_map_apply, unit_presheaf_map_apply]
  erw [map_mul, map_mul]
  rw [mul_comm]
  congr 1
  rw [← unit_presheaf_map_apply]
  exact homOfLE_appTop_map_localRingHomIncl_app (totalSpace L).hom W.1 _

/-- **The degree-zero fraction map of the canonical piece of `toProjBundle` is bijective**
(the algebraic core of "Tot(L)|_W = D₊(T) ≅ Spec (A(W)_T)_0 ≅ Spec Sym(L^∨)(W)"; §4 of the paper;
Stacks 01NS (D₊(f) ≅ Spec (A_f)_0), 01M9).

Statement. Let `W ⊆ X` be affine, `R = Γ(W, O)`, `A = A(W) = ⊕_m Γ(W, Sym^m((O ⊕ L)^∨))` (graded by
`sectionsGrading`), `T = oCoordinate L W ∈ A_1` the `O`-coordinate, and `φ = φ_W : A → Γ(p⁻¹W, O_Tot)` the local
ring homomorphism of the canonical piece `(U, e, V') = (p⁻¹W, restrictUnitIso, p⁻¹W)` of
`toProjBundle L = projBundle.lift (O ⊕ L) p O_Tot ψ`, `ψ = toProjBundleQuotient L`. Then
`ρ : (A_T)_0 → Γ(p⁻¹W, O)[1/φ T]`, `a/T^k ↦ φ(a)/φ(T)^k` (`Proj.awayMapOfGlobalSections`) is bijective.

## Natural-language proof (self-contained; not yet formalized)
Write `N = Γ(W, L^∨)` and `B = ⊕_j Γ(W, Sym^j(L^∨))` (the graded sections ring of `Sym(L^∨)` on `W`).
1. **`φ T` is a unit** (`localRingHom_oCoordinate_isUnit`, proved), so `Γ(p⁻¹W, O)[1/φ T] ≅ Γ(p⁻¹W, O)`
   (`IsLocalization.atUnits`); it suffices that `ρ' : (A_T)_0 → Γ(p⁻¹W, O)`, `a/T^k ↦ φ(a)·(φ T)^{-k}` is bijective.
2. **`Γ(p⁻¹W, O_Tot) ≅ B`** by `relativeSpec.sectionsIso` / `structureHom_app_affine`
   (`RelativeSpecStructureIso.lean`; `B` is `total.sectionsRing W`, identified with the graded direct sum
   `⊕_j Γ(W, Sym^j L^∨)` on the quasi-compact `W` by `GradedAlgebraTotalProjection`).
3. **`A = B[T]` with `T` in degree 1.** `(O ⊕ L)^∨ ≅ O^∨ ⊕ L^∨ = O ⊕ L^∨` (`dualCurryMap fst`, `dualCurryMap snd`
   are the two inclusions, `ModulesDualCurryMap.lean`), so `Sym((O ⊕ L)^∨) = Sym(O) ⊗ Sym(L^∨) = Sym(L^∨)[T]`
   and on sections `A_k = ⊕_{j ≤ k} T^{k-j}·B_j` (every `a ∈ A_k` is uniquely `Σ_j T^{k-j} ι(b_j)`, `b_j ∈ B_j`,
   `ι = Sym^j(dualCurryMap snd)`). Concretely: `A(W)` is the symmetric algebra of the `R`-module
   `Γ(W, (O ⊕ L)^∨) = R·T ⊕ N` (`symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction`,
   `TotalSpaceSectionsRingEquivMvPolynomial.lean`), `B` that of `N`, and the universal property gives the graded
   isomorphism `Sym(R·T ⊕ N) ≅ Sym(N)[T]`. With a frame of `L^∨|_W` this is `R[T, Y] ≅ R[Y][T]`
   (`totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial`; a frame is not needed for the statement).
4. **`φ` under these identifications is "set `T = 1`".** `φ` is a ring homomorphism out of `A`, generated in
   degree one (`SectionsRingGeneratedInDegreeOne`), so it is determined by degree 0 and degree 1:
   degree 0 is the restriction `R → Γ(p⁻¹W, O)` (`localRingHomComponent_zero_apply`); in degree 1
   (`localRingHomComponent_one_symGen_apply`, `TotLineAffineOverBaseDegreeOne.lean`) `φ(T) = e(ψ(p^*T)) = 1`
   (`toProjBundleQuotientSection_comp_O`, `restrictUnitIso` sends `1` to `1`) and `φ(ι λ) = e(ξ(p^*λ)) = λ`
   for `λ ∈ N` (`tautologicalFunctional` is the adjoint of `symGen ≫ totalIncl 1 ≫ structureHom`, so
   `ξ(p^*λ)` over `p⁻¹W` is `structureHom λ`, which is `λ ∈ B_1` under step 2; cf. `TotalSpaceHomEquivCoordinates`).
   Hence `φ(Σ_j T^{k-j} ι(b_j)) = Σ_j b_j`.
5. **Bijectivity.** `ρ'(a/T^k) = φ(a)` since `φ T = 1`. Surjective: `b = Σ_j b_j ∈ B` is `ρ'(Σ_j T^{m-j} ι(b_j) / T^m)`
   for `m ≥` all `j` with `b_j ≠ 0`. Injective: `ρ'(a/T^k) = 0` with `a = Σ_j T^{k-j} ι(b_j) ∈ A_k` gives
   `Σ_j b_j = 0` in the graded ring `B`, so all `b_j = 0`, `a = 0`, `a/T^k = 0`
   (`HomogeneousLocalization.Away.mk_surjective`, `HomogeneousLocalization.ext`/`val_injective`).

Edge cases: `W = ∅` — all rings are zero, bijective. `L` need not be trivial on `W` (step 3 uses no frame).
Estimate: 300+ lines, hard (steps 3 and 4 are the work: the graded model of `A(W)` and the identification of
`φ` with the augmentation `T ↦ 1`; a shared helper "graded `A(W) ≅ B[T]`, `T ↦ X`, `ι(b) ↦ C b`" would also serve
`mem_range_lSection_of_not_mem_basicOpen_oCoordinate`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.toProjBundle_awayMap_bijective {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (W : X.affineOpens) :
    Function.Bijective (AlgebraicGeometry.Proj.awayMapOfGlobalSections
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1)
      (((AlgebraicGeometry.Scheme.totalSpace L).left.homOfLE
          (le_inf le_rfl le_rfl : (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1 ≤
            (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1 ⊓
              (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom.comp
        (AlgebraicGeometry.Scheme.projBundle.localRingHom
          (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
          (AlgebraicGeometry.Scheme.totalSpace L).hom
          (show (AlgebraicGeometry.Scheme.totalSpace L).left.Modules from
            SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf)
          (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L)
          ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1)
          (AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1).ι)
          W.1))
      (DirectSum.of _ 1 (AlgebraicGeometry.Scheme.totalSpace.oCoordinate L W.1))) := by
  have hu : IsUnit (AlgebraicGeometry.Scheme.totalSpace.canonicalPiece L W
      (DirectSum.of _ 1 (AlgebraicGeometry.Scheme.totalSpace.oCoordinate L W.1))) := by
    unfold AlgebraicGeometry.Scheme.totalSpace.canonicalPiece
    exact IsUnit.map ((AlgebraicGeometry.Scheme.totalSpace L).left.homOfLE
        (le_inf le_rfl le_rfl : (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1 ≤
          (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1 ⊓
            (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom
      (AlgebraicGeometry.Scheme.totalSpace.localRingHom_oCoordinate_isUnit L
        ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1)
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1).ι) W.1)
  exact AlgebraicGeometry.Scheme.totalSpace.awayMap_bijective_of_generator_values L
    (AlgebraicGeometry.Scheme.Modules.unitDualIso X) W (AlgebraicGeometry.Scheme.totalSpace.canonicalPiece L W) rfl
    (AlgebraicGeometry.Scheme.totalSpace.canonicalPiece_sectionsUnitHom L W)
    (AlgebraicGeometry.Scheme.totalSpace.canonicalPiece_genSections_sLinear L W) hu

/-- **`V₊(T) ⊆ σ_L(X)` on a chart**: a point of `Proj A(W)` outside `D₊(T)` (`T = oCoordinate L W` the
`O`-coordinate) is, viewed in `P(O ⊕ L)` through `π⁻¹W ≅ Proj A(W)`, in the image of the `L`-section
(§4 of the paper: "the subbundle `L ↪ O ⊕ L` defines a section of `P(O ⊕ L)` whose complement is
naturally `Tot(L)`"; Stacks 01O4, 01M9). Together with `range_toProjBundle_le`
(`σ_L ∩ D₊(T) = ∅`) this says `σ_L(W) = V₊(T)`.

Hypotheses: `W ⊆ X` affine inside an open `U₂` on which `L^∨` is trivial (`e₂ : L^∨|_{U₂} ≅ O`).

## Natural-language proof (self-contained; not yet formalized)
Write `R = Γ(W, O)`, `A = A(W)`, `T ∈ A_1` the `O`-coordinate, and `Y = symGen(λ) ∈ A_1` where
`λ = (dualCurryMap inr)^{-1}`-lift of the frame: precisely `λ := ((dualCurryMap snd) (e₂⁻¹(1)))|_W ∈ Γ(W, (O ⊕ L)^∨)`,
the functional `(a, l) ↦ e₂⁻¹(1)(l)`.
1. **The `L`-section on the chart.** `lSection L = projBundle.lift (O ⊕ L) 𝟙 L^∨ (lSection.quotientMap L)` and
   `(W, U₂, e₂, V₂ := W)` is an admissible piece (`W ≤ U₂ ⊓ 𝟙⁻¹W`), so by `projBundle.lift_restrict`
   `W.ι ≫ lSection L = fromOfGlobalSections ψ ≫ affineIso⁻¹ ≫ ι` with
   `ψ = localRingHom (O ⊕ L) 𝟙 L^∨ (lSection.quotientMap L) U₂ e₂ W : A → Γ(W, O) = R` (restricted to `V₂ = W`).
   Hence it suffices to show `q ∈ Set.range (fromOfGlobalSections ψ).base`.
2. **Values of `ψ` in degree 1** (`localRingHomComponent_one_symGen_apply`, `TotLineAffineOverBaseDegreeOne.lean`):
   `ψ(T) = 0` (`localRingHom_lSection_oCoordinate_eq_zero`, proved) and `ψ(Y) = e₂(dualCurryMap inr (λ)) = e₂(e₂⁻¹(1)) = 1`
   (`dualCurryMap snd ≫ dualCurryMap inr = dualCurryMap (inr ≫ snd) = 𝟙`, `ModulesDualCurryMap.lean`); degree 0 is the
   identity of `R` (`localRingHomComponent_zero_apply`).
3. **`A = R[T, Y]`.** `Γ(W, (O ⊕ L)^∨)` is free on `(T, λ)` (dual basis of the frame `(1, e₂⁻¹(1))` of `O ⊕ L`),
   so `A ≅ R[T, Y]` as graded rings with `T ↦ T`, `Y ↦ Y` (`totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial`
   with the basis `(T, λ)`, `TotalSpaceSectionsRingEquivMvPolynomial.lean`; gradedness because both sides are
   generated in degree one). In particular the irrelevant ideal is `(T, Y)`.
4. **`q ∈ D₊(Y)`.** `q` is a relevant homogeneous prime (`q ⊉ A_+ = (T, Y)`) containing `T`, so `Y ∉ q`.
5. **Reduce to `Spec`.** `fromOfGlobalSections ψ` factors through `D₊(Y)` (`ψ Y = 1` is a unit,
   `fromOfGlobalSections_preimage_basicOpen`) as `toBasicOpenOfGlobalSections = toSpecΓ ≫ Spec.map ρ_Y ≫ basicOpenIsoSpec⁻¹`
   (`Proj.fromOfGlobalSections_resLE`, `Proj.toBasicOpenOfGlobalSections_eq`), with
   `ρ_Y : (A_Y)_0 → R`, `a/Y^k ↦ ψ(a)`. Under `basicOpenIsoSpec : D₊(Y) ≅ Spec (A_Y)_0` the point `q` goes to a prime
   `𝔮` containing `T/Y` (`Proj.awayι_preimage_basicOpen`: `q ∉ D₊(T)` iff `𝔮 ∌ T·Y^0/Y^1`).
6. **`𝔮` is in the image of `Spec.map ρ_Y`.** `ρ_Y` is surjective (`r ↦ r` on `R = A_0`) with kernel `(T/Y)`: by step 3
   every `a ∈ A_k` is `Σ_j r_j T^j Y^{k-j}`, so `a/Y^k = Σ_j r_j (T/Y)^j` and `ρ_Y(a/Y^k) = r_0`; thus
   `ker ρ_Y = (T/Y) ⊆ 𝔮`, and `Set.range (Spec.map ρ_Y) = zeroLocus (ker ρ_Y)` (`PrimeSpectrum.range_comap_of_surjective`)
   contains `𝔮`. Transport back through `basicOpenIsoSpec` and `D₊(Y).ι`.

Edge cases: `W = ∅` — no points, vacuous. Without a frame on `W` the statement is still true (`σ_L(W) = V₊(T)` for
every affine `W`) but the proof would shrink `W`; the hypothesis `W ≤ U₂` is what the glue provides.

Formalized along this route with two changes: step 3 uses the frame-free graded model
`A(W) ≅ Sym_R(R·T ⊕ N)`, `N = Γ(W, L^∨)` (`TotLineAffineOverBaseGradedModel.lean`) together with the bijection
`N ≅ R`, `n ↦ ψ(genSections (s n))`, coming from `e₂` (`lSectionPiece_genSections_sLinear_bijective`,
`TotLineAffineOverBaseLSectionPiece.lean`), and steps 4–6 are the generic Proj lemma
`Proj.mem_range_fromOfGlobalSections_of_forall_mem_span` (`TotLineAffineOverBaseProjRangeOfKernel.lean`: `q ∈ D₊(s)`,
`ρ_s` surjective with `ker ρ_s ⊆ 𝔮`, transport through `toSpecAway`, `basicOpenIsoSpec`), whose kernel hypothesis
`ker ψ ∩ A(W)_k ⊆ (T)` is `SymmetricAlgebra.ModuleSplitting.mem_span_ι_T_of_mem_symmetricPiece_of_eq_zero`
(`TotLineAffineOverBaseSymSplitKernel.lean`). The main file only substitutes `ε = unitDualIso X`
(`of_oCoordinate_eq_genSections_oFunctional`, `rfl`) and `localRingHom_lSection_oCoordinate_eq_zero`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.mem_range_lSection_of_not_mem_basicOpen_oCoordinate
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (W : X.affineOpens) (U₂ : X.Opens)
    (e₂ : (AlgebraicGeometry.Scheme.Modules.dual L).restrict U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf)
    (hW : W.1 ≤ U₂)
    (q : AlgebraicGeometry.Proj ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1))
    (hq : q ∉ AlgebraicGeometry.Proj.basicOpen ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1)
      (DirectSum.of _ 1 (AlgebraicGeometry.Scheme.totalSpace.oCoordinate L W.1))) :
    ((AlgebraicGeometry.Scheme.relativeProj.affineIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))) W).inv ≫
      ((AlgebraicGeometry.Scheme.relativeProj (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)))).hom ⁻¹ᵁ W.1).ι).base q ∈
      Set.range (AlgebraicGeometry.Scheme.lSection L).base :=
  AlgebraicGeometry.Scheme.totalSpace.mem_range_lSection_of_not_mem_basicOpen_genSections_oFunctional L U₂ e₂ W
    (AlgebraicGeometry.Scheme.Modules.unitDualIso X) hW
    (AlgebraicGeometry.Scheme.totalSpace.localRingHom_lSection_oCoordinate_eq_zero L U₂ e₂ W.1) q hq

/-- `toProjBundle⁻¹(π⁻¹W) = p⁻¹W` (`toProjBundle ≫ π = p`, `projBundle.lift_hom`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.toProjBundle_preimage_preimage {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (W : X.Opens) :
    AlgebraicGeometry.Scheme.totalSpace.toProjBundle L ⁻¹ᵁ
        ((AlgebraicGeometry.Scheme.projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom ⁻¹ᵁ W) =
      (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W := by
  have hepi : CategoryTheory.Epi (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) :=
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient_epi L
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage]
  rw [show AlgebraicGeometry.Scheme.totalSpace.toProjBundle L ≫ (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom =
        (AlgebraicGeometry.Scheme.totalSpace L).hom from
      AlgebraicGeometry.Scheme.projBundle.lift_hom _ _ _ _]

end IsIsoLeaves

section IsIsoGlue

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle in
/-- **`toProjBundle : Spec_X Sym(L^∨) → P(O ⊕ L)` is an open immersion.** Local on the target (Mathlib
`IsZariskiLocalAtTarget @IsOpenImmersion`, cover `{π⁻¹W}`, `W ⊆ X` affine); on `π⁻¹W` the restriction is the
canonical piece `liftLocal` over `p⁻¹W` (`projBundle.lift_restrict`), i.e. `fromOfGlobalSections φ_W ≫ affineIso⁻¹ ≫ ι`,
and `fromOfGlobalSections φ_W` is an open immersion by `Proj.isOpenImmersion_fromOfGlobalSections_of_bijective`
(`φ_W T` is a unit: `localRingHom_oCoordinate_isUnit`; bijectivity: leaf `toProjBundle_awayMap_bijective`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.toProjBundle_isOpenImmersion {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Scheme.totalSpace.toProjBundle L) := by
  have hepi : CategoryTheory.Epi (totalSpace.toProjBundleQuotient L) := totalSpace.toProjBundleQuotient_epi L
  have hcov : ⨆ W : X.affineOpens, (projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom ⁻¹ᵁ W.1 = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨W, hWaff, hq, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (x := (projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom.base q) (U := ⊤) trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hWaff⟩, hq⟩
  rw [AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @AlgebraicGeometry.IsOpenImmersion) _ hcov]
  intro W
  have : AlgebraicGeometry.IsAffineHom (totalSpace L).hom := relativeSpec_isAffineHom _
  have hVaff : AlgebraicGeometry.IsAffineOpen ((totalSpace L).hom ⁻¹ᵁ W.1) := W.2.preimage _
  have : AlgebraicGeometry.IsAffine ((totalSpace L).hom ⁻¹ᵁ W.1).toScheme := hVaff
  have hpre := totalSpace.toProjBundle_preimage_preimage L W.1
  have hres : (totalSpace.toProjBundle L ∣_ ((projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom ⁻¹ᵁ W.1)) ≫
        ((projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom ⁻¹ᵁ W.1).ι =
      ((totalSpace L).left.isoOfEq hpre).hom ≫
        (AlgebraicGeometry.Proj.fromOfGlobalSections _
          (((totalSpace L).left.homOfLE (le_inf le_rfl le_rfl : (totalSpace L).hom ⁻¹ᵁ W.1 ≤
              (totalSpace L).hom ⁻¹ᵁ W.1 ⊓ (totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom.comp
            (localRingHom _ (totalSpace L).hom _ (totalSpace.toProjBundleQuotient L) ((totalSpace L).hom ⁻¹ᵁ W.1)
              (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W.1))
          (localRingHom_map_irrelevant _ (totalSpace L).hom _ (totalSpace.toProjBundleQuotient L)
            ((totalSpace L).hom ⁻¹ᵁ W.1) (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W
            ((totalSpace L).hom ⁻¹ᵁ W.1) hVaff (le_inf le_rfl le_rfl)) ≫
        (relativeProj.affineIso (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))) W).inv ≫
        ((relativeProj (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)))).hom ⁻¹ᵁ W.1).ι) := by
    rw [AlgebraicGeometry.morphismRestrict_ι, ← (totalSpace L).left.isoOfEq_hom_ι hpre, CategoryTheory.Category.assoc]
    dsimp only [totalSpace.toProjBundle]
    rw [lift_restrict _ (totalSpace L).hom _ (totalSpace.toProjBundleQuotient L) ((totalSpace L).hom ⁻¹ᵁ W.1)
        (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W ((totalSpace L).hom ⁻¹ᵁ W.1) hVaff (le_inf le_rfl le_rfl)]
    rfl
  have hoi : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Proj.fromOfGlobalSections _
      (((totalSpace L).left.homOfLE (le_inf le_rfl le_rfl : (totalSpace L).hom ⁻¹ᵁ W.1 ≤
          (totalSpace L).hom ⁻¹ᵁ W.1 ⊓ (totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom.comp
        (localRingHom _ (totalSpace L).hom _ (totalSpace.toProjBundleQuotient L) ((totalSpace L).hom ⁻¹ᵁ W.1)
          (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W.1))
      (localRingHom_map_irrelevant _ (totalSpace L).hom _ (totalSpace.toProjBundleQuotient L)
        ((totalSpace L).hom ⁻¹ᵁ W.1) (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W
        ((totalSpace L).hom ⁻¹ᵁ W.1) hVaff (le_inf le_rfl le_rfl))) :=
    AlgebraicGeometry.Proj.isOpenImmersion_fromOfGlobalSections_of_bijective _ _ _ Nat.one_pos
      (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)
      (IsUnit.map ((totalSpace L).left.homOfLE (le_inf le_rfl le_rfl : (totalSpace L).hom ⁻¹ᵁ W.1 ≤
          (totalSpace L).hom ⁻¹ᵁ W.1 ⊓ (totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom
        (totalSpace.localRingHom_oCoordinate_isUnit L ((totalSpace L).hom ⁻¹ᵁ W.1)
          (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W.1))
      (totalSpace.toProjBundle_awayMap_bijective L W)
  have : AlgebraicGeometry.IsOpenImmersion ((totalSpace.toProjBundle L ∣_ ((projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom ⁻¹ᵁ W.1)) ≫
        ((projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom ⁻¹ᵁ W.1).ι) := by
    rw [hres]
    exact @AlgebraicGeometry.IsOpenImmersion.isoHom_comp_comp_isoInv_comp_ι _ _ _ _ _ _ _ hoi _
  exact AlgebraicGeometry.IsOpenImmersion.of_comp _ ((projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom ⁻¹ᵁ W.1).ι

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle in
/-- **Every point of `P(O ⊕ L)` outside the `L`-section is in the image of `toProjBundle`** (the converse of
`range_toProjBundle_le`; together they give `range_toProjBundle_eq`). Over an affine chart `W ∋ π q` inside an open trivialising `L^∨`, move `q` to
`Proj A(W)` by `relativeProj.affineIso`: if `q ∈ D₊(T)` it is in the image of `fromOfGlobalSections φ_W`
(`Proj.mem_range_fromOfGlobalSections_of_bijective` with the leaf `toProjBundle_awayMap_bijective`), hence of the
canonical piece `liftLocal = W.ι ≫ toProjBundle` (`lift_restrict`); otherwise `q ∈ V₊(T) ⊆ σ_L(X)`
(leaf `mem_range_lSection_of_not_mem_basicOpen_oCoordinate`), contradicting `q ∈ Tot(L) = P ∖ σ_L(X)`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.compl_range_lSection_le_range_toProjBundle {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    (Set.range (AlgebraicGeometry.Scheme.lSection L).base)ᶜ ⊆
      Set.range (AlgebraicGeometry.Scheme.totalSpace.toProjBundle L).base := by
  have hepi : CategoryTheory.Epi (totalSpace.toProjBundleQuotient L) := totalSpace.toProjBundleQuotient_epi L
  intro q hq
  obtain ⟨U₂, hxU₂, ⟨e₂⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := dual L)
    ((projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom.base (q))
  obtain ⟨W, hWaff, hxW, hWU₂⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (x := (projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom.base (q)) (U := U₂) hxU₂
  have : AlgebraicGeometry.IsAffineHom (totalSpace L).hom := relativeSpec_isAffineHom _
  have hVaff : AlgebraicGeometry.IsAffineOpen ((totalSpace L).hom ⁻¹ᵁ W) := hWaff.preimage _
  have : AlgebraicGeometry.IsAffine ((totalSpace L).hom ⁻¹ᵁ W).toScheme := hVaff
  -- the point in the chart `Proj A(W)`
  set q' := (relativeProj.affineIso (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))) ⟨W, hWaff⟩).hom.base
    (⟨q, hxW⟩ : (projBundle (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom ⁻¹ᵁ W) with hq'def
  have hq' : ((relativeProj.affineIso (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))) ⟨W, hWaff⟩).inv ≫
        ((relativeProj (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)))).hom ⁻¹ᵁ W).ι).base q' =
      q := by
    change ((relativeProj.affineIso (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))) ⟨W, hWaff⟩).hom ≫
        (relativeProj.affineIso (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))) ⟨W, hWaff⟩).inv ≫
        ((relativeProj (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)))).hom ⁻¹ᵁ W).ι).base
        ⟨q, hxW⟩ = _
    rw [CategoryTheory.Iso.hom_inv_id_assoc]
    rfl
  by_cases hD : q' ∈ AlgebraicGeometry.Proj.basicOpen ((symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W)
    (DirectSum.of _ 1 (totalSpace.oCoordinate L W))
  · obtain ⟨t, ht⟩ := AlgebraicGeometry.Proj.mem_range_fromOfGlobalSections_of_bijective _
      (((totalSpace L).left.homOfLE (le_inf le_rfl le_rfl : (totalSpace L).hom ⁻¹ᵁ W ≤
          (totalSpace L).hom ⁻¹ᵁ W ⊓ (totalSpace L).hom ⁻¹ᵁ W)).appTop.hom.comp
        (localRingHom _ (totalSpace L).hom _ (totalSpace.toProjBundleQuotient L) ((totalSpace L).hom ⁻¹ᵁ W)
          (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W).ι) W))
      (localRingHom_map_irrelevant _ (totalSpace L).hom _ (totalSpace.toProjBundleQuotient L)
        ((totalSpace L).hom ⁻¹ᵁ W) (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W).ι) ⟨W, hWaff⟩
        ((totalSpace L).hom ⁻¹ᵁ W) hVaff (le_inf le_rfl le_rfl))
      Nat.one_pos (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)
      (IsUnit.map ((totalSpace L).left.homOfLE (le_inf le_rfl le_rfl : (totalSpace L).hom ⁻¹ᵁ W ≤
          (totalSpace L).hom ⁻¹ᵁ W ⊓ (totalSpace L).hom ⁻¹ᵁ W)).appTop.hom
        (totalSpace.localRingHom_oCoordinate_isUnit L ((totalSpace L).hom ⁻¹ᵁ W)
          (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W).ι) W))
      (totalSpace.toProjBundle_awayMap_bijective L ⟨W, hWaff⟩) hD
    refine ⟨((totalSpace L).hom ⁻¹ᵁ W).ι.base t, ?_⟩
    change (((totalSpace L).hom ⁻¹ᵁ W).ι ≫ totalSpace.toProjBundle L).base t = _
    dsimp only [totalSpace.toProjBundle]
    rw [lift_restrict _ (totalSpace L).hom _ (totalSpace.toProjBundleQuotient L)
      ((totalSpace L).hom ⁻¹ᵁ W) (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W).ι) ⟨W, hWaff⟩
      ((totalSpace L).hom ⁻¹ᵁ W) hVaff (le_inf le_rfl le_rfl)]
    exact (congrArg (fun y => ((relativeProj.affineIso (symGradedAlgebra (dual (CategoryTheory.Limits.biprod
      (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))) ⟨W, hWaff⟩).inv ≫
        ((relativeProj (symGradedAlgebra (dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)))).hom ⁻¹ᵁ W).ι).base y) ht).trans hq'
  · exact absurd (hq' ▸ totalSpace.mem_range_lSection_of_not_mem_basicOpen_oCoordinate L ⟨W, hWaff⟩ U₂ e₂ hWU₂ q' hD) hq

end IsIsoGlue

/-- `toProjBundle` is a morphism over `X`: `toProjBundle L ≫ π = p` (the `hom` clause of `projBundle.lift`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.toProjBundle_comp_hom {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Scheme.totalSpace.toProjBundle L ≫
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom =
    (AlgebraicGeometry.Scheme.totalSpace L).hom := by
  haveI : CategoryTheory.Epi (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) :=
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient_epi L
  exact AlgebraicGeometry.Scheme.projBundle.lift_hom _ _ _ _

/-- **`Tot(L) = Spec_X Sym(L^∨)` is the open subscheme `P(O ⊕ L) ∖ σ_L(X)`**: the image of the open immersion
`toProjBundle` (`toProjBundle_isOpenImmersion`) is exactly the complement of the `L`-section
(`range_toProjBundle_le` ⊆, `compl_range_lSection_le_range_toProjBundle` ⊇).

Source: §4 of the paper ("the subbundle `L ↪ O ⊕ L` defines a section of `P(O ⊕ L)`, whose complement is
naturally `Tot(L)`"). The paper's description of `Tot(L)` is thus a theorem about the total space `totalSpace L`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.range_toProjBundle_eq {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    Set.range (AlgebraicGeometry.Scheme.totalSpace.toProjBundle L).base =
      (Set.range (AlgebraicGeometry.Scheme.lSection L).base)ᶜ :=
  Set.Subset.antisymm (AlgebraicGeometry.Scheme.totalSpace.range_toProjBundle_le L)
    (AlgebraicGeometry.Scheme.totalSpace.compl_range_lSection_le_range_toProjBundle L)


set_option backward.isDefEq.respectTransparency.types false in
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle in
/-- **The local pieces of `zeroSection L ≫ toProjBundle L` and of `oSection L` agree** (the ring-homomorphism
form of "the section defined by the summand `O` is the zero section of `Tot(L)`", §4 of the paper;
Stacks 01O4, functoriality of the universal property in the source).

Statement. For every `x : X` there are an affine chart `W ∋ x` of `X`, an admissible piece `(U₁, e₁, V₁)` of
`toProjBundle L = projBundle.lift (O ⊕ L) p O_Tot ψ` (`U₁ ⊆ Tot(L)` trivializing `O_Tot`, `V₁ ⊆ U₁ ⊓ p⁻¹W`
affine) and an admissible piece `(U₂, e₂, V₂)` of `oSection L = projBundle.lift (O ⊕ L) 𝟙 O^∨ (oSection.quotientMap L)`
(`U₂ ⊆ X` trivializing `O^∨`, `V₂ ⊆ U₂ ⊓ W` affine) with `x ∈ V₂ ≤ z⁻¹V₁` (`z = zeroSection L`), such that
the two local ring homomorphisms `A(W) = ⊕_m Γ(W, Sym^m((O ⊕ L)^∨)) → Γ(V₂, O_X)` agree:
`(z|_{V₂})^♯ ∘ res ∘ localRingHom (O⊕L) p O_Tot ψ U₁ e₁ W = res ∘ localRingHom (O⊕L) 𝟙 O^∨ (oSection.quotientMap L) U₂ e₂ W`.
Together with `projBundle.comp_lift_of_pieces` (`TotLineAffineOverBaseLiftCompOfPieces.lean`) this gives
`zeroSection_comp_toProjBundle`.

## Proof
Fix `x`. **Choices.** Take any affine `W ∋ x` (`exists_isAffineOpen_mem_and_subset`; no frame of `L` is needed).
Take `U₁ = V₁ = p⁻¹W ⊆ Tot(L)` (affine because `p` is an affine morphism, `IsAffineOpen.preimage`) with the canonical
trivialization `e₁ = restrictUnitIso (p⁻¹W).ι` — so the piece is the canonical piece `canonicalPiece L W` of
`toProjBundle`; take `U₂ = ⊤ ⊆ X`, `e₂ = (restrictFunctor ⊤.ι).mapIso (unitDualIso X) ≪≫ restrictUnitIso ⊤.ι`
(`unitDualIso X : O^∨ ≅ O` is `dualUnitEval` with inverse `unitDualSection`, both composites proved in this file),
and `V₂ = W` (`W ≤ z⁻¹(p⁻¹W)` since `z ≫ p = 𝟙`, `le_zeroSection_preimage`).
**Ring-homomorphism equality.** `A(W)` is the image of `Sym_R Γ(W, (O ⊕ L)^∨)` under `symLiftHom`
(`symLiftHom_surjective`, `W` affine, `(O ⊕ L)^∨` quasi-coherent), so two ring homomorphisms out of `A(W)` agree once
they agree on `sectionsUnitHom W r` (`r ∈ R`) and on the degree-one generators `genSections m`, `m ∈ Γ(W, (O ⊕ L)^∨)`
(`ringHom_ext_of_algebraMap_of_ι`, `symLiftHom_algebraMap`, `symLiftHom_ι`).
* Degree 0: left `= z^♯(topIso⁻¹(p^♯ r)) = r` (`canonicalPiece_sectionsUnitHom`, `symSectionsToFunctions_algebraMap`,
  `relativeSpec.structureHom_app_sectionsUnit`, `zeroSection_resLE_appTop_topIso_inv_app`); right `= r`
  (`homOfLE_appTop_localRingHom_id_sectionsUnitHom`, `TotLineAffineOverBaseCanonicalTriv.lean`).
* Degree 1 on `genSections m`: left `= z^♯(topIso⁻¹((homEquiv_p ψ)(m)))` (`homOfLE_appTop_localRingHom_genSections_restrictUnitIso`),
  and `homEquiv_p ψ = (inl)^∨ ≫ dualUnitEval ≫ p^♯ + (inr)^∨ ≫ θ` (`homEquiv_toProjBundleQuotient`), so the value is
  `z^♯(topIso⁻¹(p^♯(ev₁(m∘inl)))) + z^♯(topIso⁻¹(θ(m∘inr))) = ev₁(m∘inl) + 0`
  (`zeroSection_resLE_appTop_topIso_inv_app`, `zeroSection_resLE_appTop_topIso_inv_structureHom_totalIncl_one`:
  the zero section is the augmentation, which kills degree one; `TotLineAffineOverBaseZeroSectionPiece.lean`);
  right `= ε(φ(m)) = ev₁(m∘inl)` with `φ = dualMap inl` (`homOfLE_appTop_localRingHom_id_genSections_of_triv`;
  `oSection.quotientMap L = pullbackId ≫ dualMap inl` by definition, `dualMap = dualCurryMap` is `rfl`). -/
theorem AlgebraicGeometry.Scheme.zeroSection_toProjBundle_pieces {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (x : X) :
    ∃ (W : X.affineOpens) (U₁ : (AlgebraicGeometry.Scheme.totalSpace L).left.Opens)
      (e₁ : AlgebraicGeometry.Scheme.Modules.restrict
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf) U₁.ι ≅
        SheafOfModules.unit U₁.toScheme.ringCatSheaf)
      (V₁ : (AlgebraicGeometry.Scheme.totalSpace L).left.Opens) (hV₁ : AlgebraicGeometry.IsAffineOpen V₁)
      (hle₁ : V₁ ≤ U₁ ⊓ (AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ W.1)
      (U₂ : X.Opens)
      (e₂ : (AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).restrict
        U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf)
      (V₂ : X.Opens) (hV₂ : AlgebraicGeometry.IsAffineOpen V₂)
      (hle₂ : V₂ ≤ U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1)
      (hg : V₂ ≤ AlgebraicGeometry.Scheme.zeroSection L ⁻¹ᵁ V₁),
      x ∈ V₂ ∧
        ((AlgebraicGeometry.Scheme.zeroSection L).resLE V₁ V₂ hg).appTop.hom.comp
          (((AlgebraicGeometry.Scheme.totalSpace L).left.homOfLE hle₁).appTop.hom.comp
            (AlgebraicGeometry.Scheme.projBundle.localRingHom
              (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
              (AlgebraicGeometry.Scheme.totalSpace L).hom
              (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf)
              (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) U₁ e₁ W.1)) =
        (X.homOfLE hle₂).appTop.hom.comp
          (AlgebraicGeometry.Scheme.projBundle.localRingHom
            (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
            (CategoryTheory.CategoryStruct.id X)
            (AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
            (AlgebraicGeometry.Scheme.oSection.quotientMap L) U₂ e₂ W.1) := by
  obtain ⟨W₀, hW₀, hxW, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let W : X.affineOpens := ⟨W₀, hW₀⟩
  have hp : AlgebraicGeometry.IsAffineHom (totalSpace L).hom := by
    change AlgebraicGeometry.IsAffineHom (relativeSpec ((symGradedAlgebra (dual L)).total)).hom
    infer_instance
  refine ⟨W, (totalSpace L).hom ⁻¹ᵁ W.1, restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι,
    (totalSpace L).hom ⁻¹ᵁ W.1, W.2.preimage (totalSpace L).hom, le_inf le_rfl le_rfl, ⊤,
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).mapIso (unitDualIso X) ≪≫ restrictUnitIso (⊤ : X.Opens).ι, W.1, W.2,
    le_inf le_top (Scheme.Hom.id_preimage W.1).ge, totalSpace.le_zeroSection_preimage L W.1, hxW, ?_⟩
  haveI := totalSpace.dual_biprod_isQuasicoherent L
  -- both ring homomorphisms out of `A(W) ≅ Sym_R Γ(W, (O ⊕ L)^∨)` are determined by `R` and the generators
  have key : (((zeroSection L).resLE ((totalSpace L).hom ⁻¹ᵁ W.1) W.1
        (totalSpace.le_zeroSection_preimage L W.1)).appTop.hom.comp
          (((totalSpace L).left.homOfLE (le_inf le_rfl le_rfl : (totalSpace L).hom ⁻¹ᵁ W.1 ≤
              (totalSpace L).hom ⁻¹ᵁ W.1 ⊓ (totalSpace L).hom ⁻¹ᵁ W.1)).appTop.hom.comp
            (localRingHom (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
              (totalSpace L).hom (SheafOfModules.unit (totalSpace L).left.ringCatSheaf)
              (totalSpace.toProjBundleQuotient L) ((totalSpace L).hom ⁻¹ᵁ W.1)
              (restrictUnitIso ((totalSpace L).hom ⁻¹ᵁ W.1).ι) W.1))).comp
          (symGradedAlgebra.symLiftHom _ W.1) =
      ((X.homOfLE (le_inf le_top (Scheme.Hom.id_preimage W.1).ge :
          W.1 ≤ ⊤ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1)).appTop.hom.comp
        (localRingHom (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
          (CategoryTheory.CategoryStruct.id X) (dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
          (oSection.quotientMap L) ⊤
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).mapIso (unitDualIso X) ≪≫ restrictUnitIso (⊤ : X.Opens).ι) W.1)).comp
        (symGradedAlgebra.symLiftHom _ W.1) := by
    refine SymmetricAlgebra.ModuleSplitting.ringHom_ext_of_algebraMap_of_ι ?_ ?_
    · -- degree zero: both sides send `sectionsUnitHom r` to `r`
      intro r
      simp only [RingHom.comp_apply]
      rw [symGradedAlgebra.symLiftHom_algebraMap, homOfLE_appTop_localRingHom_id_sectionsUnitHom _ _ _ _ _ _ le_top r]
      show ((zeroSection L).resLE ((totalSpace L).hom ⁻¹ᵁ W.1) W.1 (totalSpace.le_zeroSection_preimage L W.1)).appTop.hom
        (totalSpace.canonicalPiece L W ((symGradedAlgebra (dual (biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsUnitHom W.1 r)) = _
      rw [totalSpace.canonicalPiece_sectionsUnitHom, totalSpace.symSectionsToFunctions_algebraMap,
        relativeSpec.structureHom_app_sectionsUnit]
      -- `totalSpace L` is by definition the relative Spec, so the two spellings of `p^♯ r` agree
      exact totalSpace.zeroSection_resLE_appTop_topIso_inv_app L W.1 r
    · -- degree one: on a generator `m ∈ Γ(W, (O ⊕ L)^∨)`
      intro m
      simp only [RingHom.comp_apply]
      rw [symGradedAlgebra.symLiftHom_ι, homOfLE_appTop_localRingHom_genSections_restrictUnitIso]
      unfold oSection.quotientMap
      rw [homOfLE_appTop_localRingHom_id_genSections_of_triv _ _ _ _ _ _ le_top m,
        totalSpace.homEquiv_toProjBundleQuotient, Hom.add_app, AddCommGrpCat.hom_add_apply]
      erw [map_add, map_add]
      have hA := totalSpace.zeroSection_resLE_appTop_topIso_inv_app L W.1
        (show Γ(X, W.1) from (dualUnitEval X).app W.1
          ((dualCurryMap (biprod.inl (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
            (Y := L))).app W.1 m))
      have hB := totalSpace.zeroSection_resLE_appTop_topIso_inv_structureHom_totalIncl_one L W.1
        ((dualCurryMap (biprod.inr (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Y := L))).app W.1 m)
      refine (congrArg₂ (· + ·) hA hB).trans ?_
      rw [add_zero]
      rfl
  ext a
  obtain ⟨b, rfl⟩ := symGradedAlgebra.symLiftHom_surjective _ W.2 a
  exact RingHom.congr_fun key b

/-- **The zero section followed by `toProjBundle` is the `O`-section**: `zeroSection L ≫ toProjBundle L = oSection L`.

Source: §4 of the paper ("the section defined by the other summand `O` is the zero section of `Tot(L)`");
Stacks 01O4 (the uniqueness part of the universal property of the projective bundle).

## Proof
Both sides are morphisms `X → P(O ⊕ L)` over `X` (`zeroSection_comp`, `lift_hom`).
1. `oSection L = projBundle.lift (O ⊕ L) (𝟙 X) O_X (oSection.quotientMap L)`, whose invertible quotient is the
   evaluation of the `O`-component `(𝟙)^*(O ⊕ L)^∨ → O^∨ → O`.
2. `zeroSection L ≫ toProjBundle L` is the pullback of `projBundle.lift` along `z = zeroSection L`; both sides are
   compared chart by chart with `projBundle.lift_restrict`: on an admissible piece,
   `V.ι ≫ toProjBundle L = fromOfGlobalSections φ₁ ≫ affineIso.inv ≫ ι_W` and
   `V.ι ≫ oSection L = fromOfGlobalSections φ₂ ≫ …`, and `Proj.fromOfGlobalSections` is functorial in the source
   (`Proj.comp_fromOfGlobalSections`, `TotLineAffineOverBaseFromOfGlobalSectionsComp.lean`), so the claim reduces
   to the equality of the local ring homomorphisms `(z|_V)^♯ ∘ φ₁ = φ₂ : A(W) → Γ(V, O)`.
3. That equality is `zeroSection_toProjBundle_pieces` above: `z^*(toProjBundleQuotient)` has `L`-component
   `z^*(dualCurryMap inr ≫ ξ) = 0` (the tautological functional `ξ` restricted to the zero section is the
   augmentation `Sym(L^∨) → O`, which vanishes on `L^∨`) and `O`-component
   `z^*(dualCurryMap inl ≫ dualUnitEval ≫ p^*O ≅ O)`, which through `z^*p^* ≅ (𝟙)^*` is `oSection.quotientMap L`.
4. The geometric plumbing `g ≫ lift = lift'` once the local ring homomorphisms of admissible pieces agree along `g`
   is `projBundle.comp_lift_of_pieces` (`TotLineAffineOverBaseLiftCompOfPieces.lean`). -/
theorem AlgebraicGeometry.Scheme.zeroSection_comp_toProjBundle {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Scheme.zeroSection L ≫ AlgebraicGeometry.Scheme.totalSpace.toProjBundle L =
      AlgebraicGeometry.Scheme.oSection L := by
  haveI : CategoryTheory.Epi (AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient L) :=
    AlgebraicGeometry.Scheme.totalSpace.toProjBundleQuotient_epi L
  haveI : CategoryTheory.Epi (AlgebraicGeometry.Scheme.oSection.quotientMap L) :=
    AlgebraicGeometry.Scheme.oSection.quotientMap_epi L
  exact AlgebraicGeometry.Scheme.projBundle.comp_lift_of_pieces _ _ _ _ _ _ _ (AlgebraicGeometry.Scheme.zeroSection L)
    (AlgebraicGeometry.Scheme.zeroSection_toProjBundle_pieces L)

/-- **The O-section avoids the L-section**, i.e. it lies in `Tot(L) = P(O ⊕ L) ∖ σ_L(X)`.
Proof: the O-section is the image of the zero section (`zeroSection_comp_toProjBundle`), and the image of
`toProjBundle` avoids `σ_L` (`range_toProjBundle_le`). Source: §4 of the paper. -/
theorem AlgebraicGeometry.Scheme.oSection_not_mem_range_lSection {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (x : X) :
    (AlgebraicGeometry.Scheme.oSection L).base x ∉ Set.range (AlgebraicGeometry.Scheme.lSection L).base := by
  have h : (AlgebraicGeometry.Scheme.oSection L).base x =
      (AlgebraicGeometry.Scheme.totalSpace.toProjBundle L).base
        ((AlgebraicGeometry.Scheme.zeroSection L).base x) := by
    rw [← AlgebraicGeometry.Scheme.zeroSection_comp_toProjBundle L]
    rfl
  exact AlgebraicGeometry.Scheme.totalSpace.range_toProjBundle_le L ⟨_, h.symm⟩

end
