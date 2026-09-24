import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.CyclePushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycleLemmas
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackDegreeOnCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.CurveFieldNormalizationFunctionField
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles

/-! # The normalization of a curve pushes its fundamental class to the fundamental class

The composite of the normalization map `ν₀ : Γ^ν → Γ` with the closed immersion `Γ ↪ X` sends the
fundamental class of the normalized curve to `Γ.fundamentalClass`, by the definition of the pushforward
of one-cycles.

Proof:
1. `curveCycleClassPushforward ν` is `cyclePushforward ν 1 C.cycleClass` (same definition), whose
   underlying cycle is Mathlib's `AlgebraicGeometry.AlgebraicCycle.properPushforward ν [C]`
   (`cyclePushforward_coe`); `[C] = single η_C 1` (`SmoothProjectiveCurve.cycleClass_eq_single`) and
   `[Γ] = single (ι η_Γ) 1` (`IntegralCurve.fundamentalClass_coe_eq_single`).
2. The pushforward of a single-point cycle is `single (ν η_C) (mapCoeff ν η_C)` (`properPushforward_single`).
   Both `eqToHom` and the dominant morphism `ν₀` send generic points to generic points
   (`AlgebraicGeometry.Scheme.dominantMap_genericPoint`), so `ν η_C = ι η_Γ`.
3. `mapCoeff`: both heights are `1` (`genericPoint_mem_oneCycle`, `IntegralCurve.height_image_genericPoint`)
   and residue degrees multiply along composition (`residueDegree_comp`): `eqToHom` and the closed
   immersion have residue degree `1`; the stalk map of `ν₀` at the generic point is surjective —
   `curveFieldNormalizationFunctionFieldMap_comp` (the composite is the identity for `L = K(Γ)`) together
   with `curveFieldNormalizationFunctionFieldMap_injective` shows that `dominantFunctionFieldMap ν₀` is
   surjective, and it is `stalkCongr ≫ ν₀.stalkMap η`; a surjective local homomorphism induces a
   surjective (hence bijective) map of residue fields, of degree `1`.

Source: the normalization `ρ : C̃ → C` in Theorem 1.1 and §4 of the paper; Stacks 035L, 0BXS.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The relative normalization of an integral scheme `X` in its own function field: the stalk map of
the projection at the generic point is surjective (it is the identity of `K(X)` up to the canonical
identifications; `curveFieldNormalizationFunctionFieldMap_comp` with `L = K(X)`). -/
theorem AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap_stalkMap_genericPoint_surjective
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] :
    Function.Surjective
      ((AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X X.functionField).stalkMap
        (genericPoint (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X X.functionField))) := by
  have hcomp := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationFunctionFieldMap_comp X X.functionField
  have hinj := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationFunctionFieldMap_injective X X.functionField
  have hsurj : Function.Surjective
      (AlgebraicGeometry.Scheme.dominantFunctionFieldMap
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X X.functionField)) := by
    intro y
    refine ⟨AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationFunctionFieldMap X X.functionField y, ?_⟩
    apply hinj
    have := congrArg (fun f : X.functionField ⟶ CommRingCat.of X.functionField =>
      f (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationFunctionFieldMap X X.functionField y)) hcomp
    rw [CommRingCat.comp_apply] at this
    exact this
  intro z
  obtain ⟨a, ha⟩ := hsurj z
  unfold AlgebraicGeometry.Scheme.dominantFunctionFieldMap at ha
  rw [CommRingCat.comp_apply] at ha
  exact ⟨_, ha⟩

/-- The projection from the relative normalization of `X` in `K(X)` has residue degree `1` at the
generic point: the stalk map there is surjective, so the induced residue-field map is a surjective
(hence bijective) field homomorphism. -/
theorem AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap_residueDegree_genericPoint
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] :
    (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X X.functionField).residueDegree
      (genericPoint (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X X.functionField)) = 1 := by
  set f := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap X X.functionField
  set x := genericPoint (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X X.functionField)
  let : Algebra (X.residueField (f.base x))
      ((AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X X.functionField).residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank (X.residueField (f.base x))
    ((AlgebraicGeometry.Scheme.Covers.curveFieldNormalization X X.functionField).residueField x) = 1
  apply Module.finrank_of_bijective_algebraMap
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro y
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, rfl⟩ :=
    AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap_stalkMap_genericPoint_surjective X s
  refine ⟨IsLocalRing.residue _ r, ?_⟩
  change IsLocalRing.ResidueField.map (f.stalkMap x).hom (IsLocalRing.residue _ r) = _
  exact IsLocalRing.ResidueField.map_residue _ r

theorem AlgebraicGeometry.Scheme.eqToHom_base_genericPoint {A B : AlgebraicGeometry.Scheme.{u}}
    [IrreducibleSpace A] [IrreducibleSpace B]
    (h : A = B) : (eqToHom h).base (genericPoint A) = genericPoint B := by
  subst h
  simp

theorem AlgebraicGeometry.Scheme.eqToHom_residueDegree {A B : AlgebraicGeometry.Scheme.{u}}
    (h : A = B) (a : A) : (eqToHom h).residueDegree a = 1 := by
  subst h
  simp

theorem SmoothProjectiveCurve.height_genericPoint {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) :
    Order.height (genericPoint C.toVariety.toScheme) = (1 : ℕ∞) := by
  classical
  have hmem := SmoothProjectiveCurve.genericPoint_mem_oneCycle C
  change ∀ x : C.toVariety.toScheme,
    (Function.locallyFinsuppWithin.single (genericPoint C.toVariety.toScheme) (1 : ℤ) :
      AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) x ≠ 0 →
    Order.height x = ((1 : ℕ) : ℕ∞) at hmem
  have := hmem (genericPoint C.toVariety.toScheme) (by simp)
  simpa using this

theorem curveFieldNormalization_cyclePushforward_fundamentalClass
    {k : Type u} [Field k] [PerfectField k]
    {X : SmoothProjectiveVariety k} (Γ : IntegralCurve k X.toScheme)
    (C : SmoothProjectiveCurve k)
    (ν : C.toScheme ⟶ X.toScheme)
    [ν.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hcarrier : C.toScheme =
      AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField)
    (hν : ν = eqToHom hcarrier ≫
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField ≫ Γ.ι)) :
    curveCycleClassPushforward ν = Γ.fundamentalClass := by
  classical
  have hproper : AlgebraicGeometry.IsProper ν := SmoothProjectiveCurve.isProper_of_isOver ν
  apply Subtype.ext
  have h1 : (curveCycleClassPushforward ν : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward ν
        (C.cycleClass : AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) :=
    cyclePushforward_coe (X := C.toVariety) (Y := X.toVariety) ν 1 C.cycleClass
  rw [h1, SmoothProjectiveCurve.cycleClass_eq_single,
    AlgebraicGeometry.AlgebraicCycle.properPushforward_single,
    IntegralCurve.fundamentalClass_coe_eq_single]
  set ηC := genericPoint C.toVariety.toScheme with hηC
  have hgen : ν.base ηC = Γ.ι.base (genericPoint Γ.carrier) := by
    rw [hν, AlgebraicGeometry.Scheme.Hom.comp_base, AlgebraicGeometry.Scheme.Hom.comp_base]
    change Γ.ι.base ((AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField).base
      ((eqToHom hcarrier).base ηC)) = _
    rw [AlgebraicGeometry.Scheme.eqToHom_base_genericPoint]
    congr 1
    exact AlgebraicGeometry.Scheme.dominantMap_genericPoint _
  have hdeg : ν.residueDegree ηC = 1 := by
    rw [hν, AlgebraicGeometry.Intersection.residueDegree_comp, AlgebraicGeometry.Intersection.residueDegree_comp,
      AlgebraicGeometry.Scheme.eqToHom_residueDegree, mul_one]
    rw [AlgebraicGeometry.Scheme.eqToHom_base_genericPoint,
      AlgebraicGeometry.Intersection.closedImmersion_residueDegree_eq_one,
      AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap_residueDegree_genericPoint, mul_one]
  have hcoeff : AlgebraicGeometry.AlgebraicCycle.mapCoeff ν (Order.height (α := C.toScheme))
      (Order.height (α := X.toScheme)) ηC = 1 := by
    unfold AlgebraicGeometry.AlgebraicCycle.mapCoeff
    rw [if_pos, hdeg]
    rw [hgen, IntegralCurve.height_image_genericPoint]
    exact SmoothProjectiveCurve.height_genericPoint C
  rw [hgen, hcoeff]
  simp

end
