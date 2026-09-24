import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.Artinian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a21
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.ZeroSchemeCycleApplyOfCoheightEqOne
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineBundleSectionGermGenericNeZero

/-! # The zero scheme of a nonzero section on a smooth projective curve is discrete

Let `C` be a smooth projective curve (integral, `dim C = 1`), `A` a line bundle, `s ≠ 0` a global
section and `Z := Z(s)` the closed subscheme of `idealSheafOfSection A s`. Then the underlying
space of `Z` is discrete (hence a finite set of points).

Proof sketch:
1. `s ≠ 0` implies that the germ of `s` at the generic point `η` is nonzero
   (`germ_genericPoint_ne_zero`), so `η ∉ supp Z(s)` (`genericPoint_notMem_idealSheafOfSection_support`).
2. `C` is integral, locally of finite type over `K`, `dim C = 1`: `height x + coheight x = 1`
   (Stacks 0A21, `height_add_coheight_eq_of_locallyOfFiniteType`). If `x ≠ η` then `x < η` (`η` is
   the greatest element of the specialization order), so `coheight x ≥ 1`, `height x = 0`, and `x`
   is minimal in the specialization order (a closed point).
3. The closed immersion `ι : Z → C` reflects the specialization order (`le_iff_of_isClosedImmersion`)
   and `ι(Z) = supp` does not contain `η`, so every point of `Z` is minimal; hence `krullDim Z ≤ 0`
   (`Order.krullDim_nonpos_iff_forall_isMin`) and `topologicalKrullDim Z ≤ 0`
   (`irreducibleSetEquivPoints`).
4. `Z` is locally Noetherian (a closed immersion is locally of finite type) with
   `topologicalKrullDim Z ≤ 0`, hence locally Artinian
   (`IsLocallyArtinian.of_topologicalKrullDim_le_zero`), hence discrete
   (`IsLocallyArtinian.discreteTopology`).

Sources: Stacks 0BCH (effective Cartier divisors), Stacks 00J7 / 0A21; Hartshorne II.6. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.ZeroSchemeOfCurveSectionDiscrete

open AlgebraicGeometry

/-- If every point of a scheme is minimal in the specialization order, its topological Krull
dimension is `≤ 0`. -/
theorem topologicalKrullDim_le_zero_of_forall_isMin (Z : AlgebraicGeometry.Scheme.{u})
    (h : ∀ z : Z, IsMin z) : topologicalKrullDim Z ≤ 0 := by
  have hk : Order.krullDim Z = topologicalKrullDim Z :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints Z _ _ _ : IrreducibleCloseds Z ≃o Z)).symm
  rw [← hk]
  exact Order.krullDim_nonpos_iff_forall_isMin.mpr h

/-- A locally Noetherian scheme all of whose points are minimal has discrete underlying space. -/
theorem discreteTopology_of_forall_isMin (Z : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian Z] (h : ∀ z : Z, IsMin z) : DiscreteTopology Z := by
  have : AlgebraicGeometry.IsLocallyArtinian Z :=
    AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero
      (topologicalKrullDim_le_zero_of_forall_isMin Z h)
  infer_instance

/-- On a smooth projective curve, a point other than the generic point is closed (minimal in the
specialization order). -/
theorem isMin_of_ne_genericPoint {K : Type u} [Field K] (C : SmoothProjectiveCurve K)
    {x : C.toScheme} (hx : x ≠ genericPoint C.toScheme) : IsMin x := by
  have : AlgebraicGeometry.IsProper (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    C.isProper
  have hdim : topologicalKrullDim C.toScheme = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [Nat.cast_one]; exact C.dim_one
  have h := AlgebraicGeometry.height_add_coheight_eq_of_locallyOfFiniteType (k := K) C.toScheme 1 hdim x
  have hlt : x < genericPoint C.toScheme :=
    lt_of_le_not_ge (AlgebraicGeometry.Scheme.le_iff_specializes.mpr (genericPoint_specializes x))
      (fun h => hx ((AlgebraicGeometry.Scheme.le_iff_specializes.mp h).antisymm
        (genericPoint_specializes x)).eq)
  have h1 : Order.coheight (genericPoint C.toScheme) + 1 ≤ Order.coheight x :=
    Order.coheight_add_one_le hlt
  have h2 : (1 : ℕ∞) ≤ Order.coheight x := le_trans le_add_self h1
  rw [← Order.height_eq_zero]
  have h3 : Order.height x + 1 ≤ (1 : ℕ∞) := by
    calc Order.height x + 1 ≤ Order.height x + Order.coheight x := add_le_add_right h2 _
      _ = 1 := by rw [h]; rfl
  have h4 : Order.height x ≤ 0 := by
    have := (ENat.add_le_add_iff_right (by exact ENat.one_ne_top)).mp
      (show Order.height x + 1 ≤ 0 + 1 by rw [zero_add]; exact h3)
    exact this
  exact le_antisymm h4 bot_le

/-- The zero scheme of a nonzero section of a line bundle on a smooth projective curve has
discrete underlying space. -/
theorem discreteTopology_zeroScheme {K : Type u} [Field K] (C : SmoothProjectiveCurve K)
    (A : C.toScheme.Modules) [A.IsLineBundle] (sA : Γ(A, ⊤)) (hsA : sA ≠ 0) :
    DiscreteTopology (AlgebraicGeometry.Scheme.idealSheafOfSection A sA).subscheme := by
  set I := AlgebraicGeometry.Scheme.idealSheafOfSection A sA with hI
  have : AlgebraicGeometry.IsProper (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    C.isProper
  have : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  have : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  apply discreteTopology_of_forall_isMin
  intro z w hwz
  have hη : genericPoint C.toScheme ∉ I.support :=
    AlgebraicGeometry.Scheme.genericPoint_notMem_idealSheafOfSection_support A sA
      (AlgebraicGeometry.Scheme.Modules.germ_genericPoint_ne_zero A sA hsA)
  have hz : I.subschemeι.base z ≠ genericPoint C.toScheme := by
    intro h
    apply hη
    have hmem : I.subschemeι.base z ∈ Set.range I.subschemeι.base := ⟨z, rfl⟩
    rw [I.range_subschemeι] at hmem
    rw [← h]
    exact hmem
  have hmin := isMin_of_ne_genericPoint C hz
  have hle : I.subschemeι.base w ≤ I.subschemeι.base z :=
    (I.subschemeι.le_iff_of_isClosedImmersion w z).mpr hwz
  exact (I.subschemeι.le_iff_of_isClosedImmersion z w).mp (hmin hle)

end MiyaokaMori.ZeroSchemeOfCurveSectionDiscrete

end
