import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUnitBiprodGeometry
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphismComp
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverIffProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleOSection

/-! # The ruled surface

The ruled surface `W = P(O_C̃ ⊕ L)`: a smooth projective surface with a fibration `π_W : W → C̃`; `Tot(L)` is the
open subscheme obtained by removing the `L`-section, compatibly with `π_W` (§2 of the paper).

`projectiveBundle_unit_biprod_geometry` needs `[IsLocallyNoetherian X]` (its dimension conjunct is false for
non-Noetherian bases); a smooth projective curve over a field is locally Noetherian via
`LocallyOfFiniteType.isLocallyNoetherian`, supplied by `letI` at each call site.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The data of `ruledSurface` (the underlying scheme `P(O ⊕ L)` with the `k`-structure `π ≫ (C ↘ Spec k)`) are
   explicit; each well-definedness obligation is a named theorem, and the definition is assembled in three layers:
   `ruledSurface.variety` → `ruledSurface.smoothProjectiveVariety` → `ruledSurface`. -/

/-- The structure morphism `W → C̃ → Spec k` of `W`. -/

noncomputable abbrev ruledSurface.structureHom {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).left ⟶
      AlgebraicGeometry.Spec (CommRingCat.of k) :=
  (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom ≫
    (C.toVariety.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- Integrality: `C̃` is integral, `P(E) → C̃` is locally `P^1_U → U` (`U` affine integral) and `P^1_U` is integral;
irreducibility from irreducible fibers, irreducible base and `π` open; reducedness is checked locally. -/
theorem ruledSurface.isIntegral {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    AlgebraicGeometry.IsIntegral
      (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).left := by
  letI : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  letI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  exact (projectiveBundle_unit_biprod_geometry L.toModules).1

theorem ruledSurface.isSeparated {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    AlgebraicGeometry.IsSeparated (ruledSurface.structureHom L) := by
  have hC : AlgebraicGeometry.IsSeparated
      (C.toVariety.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := C.isSeparated
  letI : AlgebraicGeometry.IsSeparated
      (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom :=
    AlgebraicGeometry.Scheme.relativeProj_isSeparated _
  change AlgebraicGeometry.IsSeparated
    ((AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom ≫
      (C.toVariety.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  infer_instance

/-- Finite type: `P(E) → C̃` is of finite type (locally `P^1_U → U`), composed with `C̃ → Spec k` of finite type. -/
theorem ruledSurface.isOfFiniteType {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    AlgebraicGeometry.IsOfFiniteType (ruledSurface.structureHom L) := by
  letI : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  letI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let h := projectiveBundle_unit_biprod_geometry L.toModules
  letI : AlgebraicGeometry.IsProjectiveMorphism
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom := h.2.2.1
  have hp := AlgebraicGeometry.IsProjectiveMorphism.isQuasiProjective_isProper
    (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom
  letI : AlgebraicGeometry.LocallyOfFiniteType
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom :=
    hp.1.locallyOfFiniteType
  letI : AlgebraicGeometry.QuasiCompact
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom :=
    hp.1.quasiCompact
  change AlgebraicGeometry.IsOfFiniteType
    ((AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom ≫
      (C.toVariety.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  exact { toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }

/-- `W = P(O_C̃ ⊕ L)` as a variety. -/

noncomputable def ruledSurface.variety {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) : Variety k where
  carrier := (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).left
  «over» := ⟨ruledSurface.structureHom L⟩
  integral := ruledSurface.isIntegral L
  separated := ruledSurface.isSeparated L
  finiteType := ruledSurface.isOfFiniteType L

/-- Smoothness: `P(E) → C̃` is smooth (locally `P^1_U → U`), composed with `C̃ → Spec k` smooth. -/
theorem ruledSurface.isSmoothOver {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    IsSmoothOver k (ruledSurface.variety L).carrier := by
  letI : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  letI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let h := projectiveBundle_unit_biprod_geometry L.toModules
  letI : AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom := h.2.1
  letI : AlgebraicGeometry.Smooth
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth 1 _
  letI : AlgebraicGeometry.Smooth
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := C.smooth
  change AlgebraicGeometry.Smooth
    ((AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom ≫
      (C.toVariety.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  infer_instance

/-- Projectivity: `E = O ⊕ L` is a vector bundle on a projective curve, `P(E) → C̃` is projective
(`O_{P(E)}(1) ⊗ π^*(ample)^N` is ample), and the composite is still projective. -/
theorem ruledSurface.isProjectiveOver {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    IsProjectiveOver k (ruledSurface.variety L).carrier := by
  letI : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  letI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let h := projectiveBundle_unit_biprod_geometry L.toModules
  letI : AlgebraicGeometry.IsProjectiveMorphism
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom := h.2.2.1
  have hC := (isProjectiveOver_iff_isProjectiveMorphism k C.toScheme).mp C.projective
  letI : AlgebraicGeometry.IsProjectiveMorphism
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hC
  apply (isProjectiveOver_iff_isProjectiveMorphism k
    (ruledSurface.variety L).carrier).mpr
  change AlgebraicGeometry.IsProjectiveMorphism
    ((AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
        (show C.toVariety.toScheme.Modules from
          SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom ≫
      (C.toVariety.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  exact IsProjectiveMorphism.comp _ _

/-- Connectedness: immediate from integrality (irreducibility); stated here because it goes through `ruledSurface.isIntegral`. -/
theorem ruledSurface.connectedSpace {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    ConnectedSpace (ruledSurface.variety L).carrier.carrier := by
  haveI : AlgebraicGeometry.IsIntegral (ruledSurface.variety L).carrier := ruledSurface.isIntegral L
  infer_instance

noncomputable def ruledSurface.smoothProjectiveVariety {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) : SmoothProjectiveVariety k where
  toVariety := ruledSurface.variety L
  smooth := ruledSurface.isSmoothOver L
  projective := ruledSurface.isProjectiveOver L
  connected := ruledSurface.connectedSpace L

/-- `dim W = 2`: the dimension of a `P^1`-bundle is the dimension of the base plus `1`, and `dim C̃ = 1`. -/
theorem ruledSurface.dim_eq_two {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    (ruledSurface.smoothProjectiveVariety L).toVariety.dim = 2 := by
  letI : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  letI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hdim : topologicalKrullDim (ruledSurface.variety L).carrier =
      (2 : WithBot ℕ∞) := by
    change topologicalKrullDim
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).left = _
    rw [(projectiveBundle_unit_biprod_geometry L.toModules).2.2.2, C.dim_one]
    norm_num
  rw [Variety.dim_spec] at hdim
  exact_mod_cast hdim

noncomputable def ruledSurface {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) : SmoothProjectiveSurface k where
  toSmoothProjectiveVariety := ruledSurface.smoothProjectiveVariety L
  dim_eq_two := ruledSurface.dim_eq_two L

noncomputable def ruledSurface.π {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) : (ruledSurface L).toScheme ⟶ C.toScheme :=
  (AlgebraicGeometry.Scheme.projBundle
    (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom

theorem ruledSurface.toScheme_eq {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    Nonempty ((ruledSurface L).toScheme ≅
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
          (show C.toVariety.toScheme.Modules from
            SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).left) :=
  ⟨CategoryTheory.Iso.refl _⟩

/- The fact that `Tot(L)` is an open subscheme of `W` compatible with the projections is
   `ruledSurface.totalSpaceIncl_isOpenImmersion` and `ruledSurface.totalSpaceIncl_comp_π`
   (`TotalSpaceAgreesTotLine`), stated for the total space `totalSpace L`. -/

instance {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) : AlgebraicGeometry.Surjective (ruledSurface.π L) :=
  by
    have hcomp : AlgebraicGeometry.Surjective
        (AlgebraicGeometry.Scheme.oSection L.toModules ≫
          (AlgebraicGeometry.Scheme.projBundle
            (CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
              (show C.toVariety.toScheme.Modules from
                SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules)).hom) := by
      rw [AlgebraicGeometry.Scheme.oSection_comp]
      infer_instance
    change AlgebraicGeometry.Surjective
      (AlgebraicGeometry.Scheme.oSection L.toModules ≫ ruledSurface.π L) at hcomp
    exact AlgebraicGeometry.Surjective.of_comp
      (AlgebraicGeometry.Scheme.oSection L.toModules) (ruledSurface.π L)

end
