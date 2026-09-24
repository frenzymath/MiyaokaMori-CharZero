import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteCodimOnePointsOutsideOpen
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.Stacks02r1
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02og
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02nx
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ClosedPointCoheightOne
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierFiniteSupport
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree

/-! # A generically finite morphism from a proper curve to a smooth projective curve is finite

Statement: a `k`-morphism `g : Γ → C` from an integral proper one-dimensional `k`-scheme `Γ` to a
smooth projective curve `C` that sends the generic point to the generic point is **finite**, and its
function-field degree `[K(Γ) : K(C)]` is **positive**.

Source: Stacks 02OG (proper + finite fibres ⇒ finite) together with Stacks 02NX (the generic fibre
of a dominant morphism of integral schemes of finite type is a single point iff the function-field
extension is finite) and 02R1 (equal dimension ⇒ finite function-field extension); in the paper
this is used for `ρ₀ = π_κ ∘ ι ∘ ν` (finite, with `e₀ = deg ρ₀ > 0`).

Proof sketch:
1. `Γ` and `C` are varieties of the same dimension `1`, and `g` is dominant (generic point to generic
   point), so `K(Γ)/K(C)` is finite (02R1: `Variety.residueFieldMap_genericPoint_finite_of_dim_eq`);
   hence `functionFieldDegree g = [K(Γ) : K(C)] > 0` (`Module.finrank_pos`).
2. Fibres of `g` are finite. Over a closed point `y`: the fibre is a closed subset of `Γ` not containing
   the generic point (which maps to the generic point of `C ≠ y`), so it consists of points of
   coheight `1` outside the non-empty open `g⁻¹(C ∖ {y})`, a finite set
   (`finite_coheight_one_not_mem`). Over a non-closed point `y`: `C` has dimension `1`, so `y` is the
   generic point, and by 02NX the fibre over it is `{η_Γ}`.
3. `g` is proper (cancel the proper structure morphism of `Γ` against the separated one of `C`), so
   02OG gives that `g` is finite. ∎ -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Finite residue-field extension at the generic point ⇒ positive function-field degree
(`Module.finrank_pos`; rules out the `0` fallback of `finrank`). Same statement as
`functionFieldDegree_pos_of_finite` in `DegreeZeroIffConstant`, restated here
to keep this module's import closure small. -/
theorem functionFieldDegree_pos_of_residueFieldMap_finite {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y)
    (hfin : (f.residueFieldMap (genericPoint X)).hom.Finite) : 0 < functionFieldDegree f := by
  unfold functionFieldDegree AlgebraicGeometry.Scheme.Hom.residueDegree
  let _ := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  have : Module.Finite (Y.residueField (f.base (genericPoint X)))
      (X.residueField (genericPoint X)) := hfin
  exact Module.finrank_pos

theorem isFinite_and_functionFieldDegree_pos_of_curve_to_curve {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K}
    (Γ : AlgebraicGeometry.Scheme.{u}) [Γ.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Γ] (hΓ : IsProperOver K Γ) (hdim : SchemeIsOneDimensional Γ)
    (g : Γ ⟶ C.toScheme) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hg : g.base (genericPoint Γ) = genericPoint C.toScheme) :
    AlgebraicGeometry.IsFinite g ∧ 0 < functionFieldDegree g := by
  have hgeneric_residue_finite :
      (g.residueFieldMap (genericPoint Γ)).hom.Finite := by
    letI : AlgebraicGeometry.IsProper
        (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hΓ
    letI : AlgebraicGeometry.LocallyOfFiniteType
        (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
      AlgebraicGeometry.IsProper.toLocallyOfFiniteType
    letI : AlgebraicGeometry.QuasiCompact
        (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := inferInstance
    let ΓV : Variety K :=
      { carrier := Γ
        integral := inferInstance
        separated := hΓ.toIsSeparated
        finiteType := AlgebraicGeometry.IsOfFiniteType.mk }
    have hdimΓ : ΓV.toScheme.dimension = 1 := by
      change Γ.dimension = 1
      rw [AlgebraicGeometry.Scheme.dimension, hdim]
      norm_num
    have hdimC : C.toScheme.dimension = 1 := by
      unfold AlgebraicGeometry.Scheme.dimension
      rw [C.dim_one]
      simp
    exact Variety.residueFieldMap_genericPoint_finite_of_dim_eq
      (X := ΓV) (Y := C.toVariety) g hg (hdimΓ.trans hdimC.symm)
  have hfinite_fiber : ∀ y : C.toScheme, (g.base ⁻¹' {y}).Finite := by
    letI : AlgebraicGeometry.IsNoetherian Γ :=
      AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
        (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
    intro y
    by_cases hy : IsClosed ({y} : Set C.toScheme)
    · let U : C.toScheme.Opens := ⟨({y} : Set C.toScheme)ᶜ, hy.isOpen_compl⟩
      let V : Γ.Opens := TopologicalSpace.Opens.comap ⟨g.base, g.continuous⟩ U
      have hgeneric_not_closed : ¬ IsClosed ({genericPoint C.toScheme} : Set C.toScheme) := by
        intro h
        have hone := AlgebraicGeometry.Scheme.closedPoint_coheight_eq_one_of_dimension_one
          C.toScheme C.dim_one (genericPoint C.toScheme) h
        have hzero : Order.coheight (genericPoint C.toScheme) = 0 :=
          Order.coheight_eq_zero.mpr (isMax_top (α := C.toScheme))
        exact one_ne_zero (hone.symm.trans hzero)
      have hgen_ne_y : genericPoint C.toScheme ≠ y := by
        intro h
        apply hgeneric_not_closed
        simpa [h] using hy
      have hVnonempty : Nonempty V := by
        refine ⟨⟨genericPoint Γ, ?_⟩⟩
        rw [TopologicalSpace.Opens.mem_comap]
        simp only [U]
        intro h
        apply hgen_ne_y
        change g.base (genericPoint Γ) = y at h
        exact hg ▸ h
      have hfinite := AlgebraicGeometry.Scheme.finite_coheight_one_not_mem V
      refine hfinite.subset ?_
      intro x hx
      have hxnotgen : x ≠ genericPoint Γ := by
        intro hxgen
        subst x
        apply hgen_ne_y
        change g.base (genericPoint Γ) = y at hx
        exact hg ▸ hx
      have hco_pos : 0 < Order.coheight x := by
        exact Order.coheight_pos_of_lt_top (lt_of_le_not_ge le_top (by
          intro htop
          apply hxnotgen
          have hle : x ≤ (⊤ : Γ) := le_top
          have hspec1 : x ⤳ (⊤ : Γ) :=
            AlgebraicGeometry.Scheme.le_iff_specializes.mp htop
          have hspec2 : (⊤ : Γ) ⤳ x :=
            AlgebraicGeometry.Scheme.le_iff_specializes.mp hle
          exact (hspec1.antisymm hspec2).eq))
      have hkrull : Order.krullDim Γ ≤ 1 := by
        rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Γ))]
        exact le_of_eq hdim
      have hco_le : Order.coheight x ≤ 1 := by
        exact WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans hkrull)
      have hco : Order.coheight x = 1 := by
        apply le_antisymm hco_le
        exact Order.one_le_iff_ne_zero.mpr (ne_of_gt hco_pos)
      constructor
      · exact hco
      · change g.base x ∉ ({y} : Set C.toScheme)ᶜ
        exact fun h' => h' hx
    · have hdimCtop : topologicalKrullDim C.toScheme ≤ 1 := by
        rw [C.dim_one]
      have hkrullC : Order.krullDim C.toScheme ≤ 1 := by
        rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C.toScheme))]
        exact hdimCtop
      have hco_le : Order.coheight y ≤ 1 := by
        exact WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim y).trans hkrullC)
      have hygen : y = genericPoint C.toScheme := by
        by_cases hzero : Order.coheight y = 0
        · have hmax : IsMax y := Order.coheight_eq_zero.mp hzero
          have hle : y ≤ genericPoint C.toScheme :=
            AlgebraicGeometry.Scheme.le_iff_specializes.mpr (genericPoint_specializes y)
          have hgen_le : genericPoint C.toScheme ≤ y := hmax hle
          have hs1 : y ⤳ genericPoint C.toScheme :=
            AlgebraicGeometry.Scheme.le_iff_specializes.mp hgen_le
          have hs2 : genericPoint C.toScheme ⤳ y := genericPoint_specializes y
          exact (hs1.antisymm hs2).eq
        · have hco : Order.coheight y = 1 := by
            apply le_antisymm hco_le
            exact Order.one_le_iff_ne_zero.mpr hzero
          have hyclosed : IsClosed ({y} : Set C.toScheme) :=
            AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one hdimCtop y hco
          exact (hy hyclosed).elim
      letI : AlgebraicGeometry.LocallyOfFiniteType g := by
        have hcomp : g ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
            Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of K) := by
          exact comp_over g _
        have hsource : AlgebraicGeometry.LocallyOfFiniteType
            (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
          hΓ.toLocallyOfFiniteType
        letI : AlgebraicGeometry.LocallyOfFiniteType
            (g ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := by
          rw [hcomp]
          exact hsource
        exact AlgebraicGeometry.locallyOfFiniteType_of_comp g
          (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
      have hfiber :=
        (AlgebraicGeometry.functionField_finite_iff_generic_fiber g hg).mp
          hgeneric_residue_finite
      rw [hygen]
      have hfiber' : g.base ⁻¹' {genericPoint C.toScheme} = {genericPoint Γ} := by
        simpa [hg] using hfiber
      rw [hfiber']
      exact Set.finite_singleton _
  letI : AlgebraicGeometry.LocallyOfFiniteType
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    C.isProper.toLocallyOfFiniteType
  letI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  letI : AlgebraicGeometry.IsProper (g ≫
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := by
    rw [comp_over g]
    exact hΓ
  letI : AlgebraicGeometry.IsSeparated
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := C.isSeparated
  letI : AlgebraicGeometry.IsProper g := AlgebraicGeometry.IsProper.of_comp g
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  refine ⟨AlgebraicGeometry.isFinite_of_isProper_of_finite_fibers g hfinite_fiber, ?_⟩
  exact functionFieldDegree_pos_of_residueFieldMap_finite g hgeneric_residue_finite

end
