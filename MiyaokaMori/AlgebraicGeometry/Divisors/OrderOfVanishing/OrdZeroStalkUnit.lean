import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.RegularScheme
import MiyaokaMori.RingTheory.RegularLocalRing.LocalFactorialUnitCriterion
import MiyaokaMori.RingTheory.OrderOfVanishing.RegularLocalRingDVR
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Properties

/-! # Vanishing order zero on all nearby prime divisors makes a rational function a unit

On a regular integral scheme, a rational function whose order of vanishing is `0` at all prime divisors
in a neighbourhood of a point is a unit of the local ring at that point (the geometric core of the
injectivity half of Hartshorne II.6.11, and of the gluing step of the surjectivity half).

Source: Hartshorne, *Algebraic Geometry*, Prop. II.6.11, end of the first paragraph of the proof ("if the
Weil divisor of `f_i` on `U_i` is `0` then `f_i ∈ Γ(U_i, O^*)`"). Hartshorne uses II.6.3A (algebraic
Hartogs); here the route is **affine opens and local rings that are UFDs** (the unit criterion for
locally factorial rings), avoiding Hartogs.

Proof (`exists_units_stalk_algebraMap_eq_of_forall_ord_eq_zero`): take an affine open neighbourhood
`V ⊆ W` of `w`, `A := Γ(V, O_X)`, `K = K(X)` the fraction field of `A` (Mathlib
`functionField_isFractionRing_of_isAffineOpen`), `O_{X,w} = A_𝔪` (`𝔪 = primeIdealOf w`,
`IsAffineOpen.isLocalization_stalk`), a regular local ring and hence a UFD (hypothesis `hufd`). For every
height-one prime `p` of `A`, `z := fromSpec p ∈ V` is a point of `X`; open immersions preserve coheight
and on `Spec A` coheight equals the height of the ideal (Mathlib `coheight_eq_of_isOpenImmersion`,
`idealHeight_eq_coheight`), so `coheight z = 1` and `z` is a prime divisor. `O_{X,z}` is a regular local
ring of dimension `1`, i.e. a DVR (Stacks 00PD); `ord_z f = 0` says `ordFrac f = 1`, so `f` is the image
of a unit of `O_{X,z}` (`Ring.exists_units_algebraMap_eq_of_ordFrac_eq_one`). Since `O_{X,z} = A_p`
(`isLocalization_stalk'`), writing this unit as `u/s` with `u, s ∈ A ∖ p` gives the hypothesis of the
unit criterion for locally factorial rings; conclusion: `f ∈ O_{X,w}^×`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]

/-- On a regular integral scheme the local ring at a point of coheight `1` is a DVR (a regular local ring of
dimension `1`, Stacks 00PD). -/
theorem isDiscreteValuationRing_stalk_of_isRegular [X.IsRegular] (z : X)
    (hz : Order.coheight z = 1) : IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.Scheme.IsRegular.locallyNoetherian (X := X)
  have : IsRegularLocalRing (X.presheaf.stalk z) :=
    AlgebraicGeometry.Scheme.IsRegular.isRegularLocalRing_stalk (X := X) z
  apply MiyaokaMori.RingTheory.isDiscreteValuationRing_of_regularLocalRing_dimension_one
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight z, hz]
  rfl

/-- At a point `z` of coheight `1` whose local ring is a DVR: `ord_z f = 0` implies that `f` is the image of a
unit of `O_{X,z}`. -/
theorem exists_units_stalk_algebraMap_eq_of_ord_eq_zero [AlgebraicGeometry.IsLocallyNoetherian X]
    (z : X) (hz : Order.coheight z = 1) [IsDiscreteValuationRing (X.presheaf.stalk z)]
    {f : X.functionField} (hf : f ≠ 0) (h : X.ord f z = 0) :
    ∃ v : (X.presheaf.stalk z)ˣ, algebraMap (X.presheaf.stalk z) X.functionField v = f := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hz.le
  have h1 : X.ordHom z hz f = 1 := by
    have h0 := (AlgebraicGeometry.Scheme.ord_eq_iff hz hf).mp h
    rw [h0]
    rfl
  exact Ring.exists_units_algebraMap_eq_of_ordFrac_eq_one h1

/-- **Main lemma**: let `X` be a regular integral scheme whose local rings are UFDs, `W` open, `w ∈ W`, and
`f ∈ K(X)^×`. If `f` has order of vanishing `0` at every point of coheight `1` in `W`, then `f` is the image
of a unit of `O_{X,w}`. -/
theorem exists_units_stalk_algebraMap_eq_of_forall_ord_eq_zero
    [AlgebraicGeometry.IsLocallyNoetherian X] [X.IsRegular]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (W : X.Opens) {w : X} (hw : w ∈ W) {f : X.functionField} (hf : f ≠ 0)
    (h : ∀ z ∈ W, Order.coheight z = 1 → X.ord f z = 0) :
    ∃ v : (X.presheaf.stalk w)ˣ, algebraMap (X.presheaf.stalk w) X.functionField v = f := by
  obtain ⟨V, hV, hwV, hVW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hw
  have : Nonempty V := ⟨⟨w, hwV⟩⟩
  have : IsFractionRing Γ(X, V) X.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X V hV
  let : Algebra Γ(X, V) (X.presheaf.stalk w) := X.presheaf.algebra_section_stalk ⟨w, hwV⟩
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk w) X.functionField :=
    AlgebraicGeometry.functionField_isScalarTower X V ⟨w, hwV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk w) (hV.primeIdealOf ⟨w, hwV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨w, hwV⟩
  have : UniqueFactorizationMonoid (X.presheaf.stalk w) := hufd w
  apply IsLocalization.AtPrime.exists_units_algebraMap_eq_of_forall_height_one
    (hV.primeIdealOf ⟨w, hwV⟩).asIdeal (X.presheaf.stalk w) hf
  intro p hp hph
  let y : PrimeSpectrum Γ(X, V) := ⟨p, hp⟩
  have hzV : hV.fromSpec y ∈ V := by
    have hmem : hV.fromSpec y ∈ Set.range hV.fromSpec := Set.mem_range_self y
    rwa [hV.range_fromSpec] at hmem
  have hz : Order.coheight (hV.fromSpec y) = 1 := by
    have h1 := AlgebraicGeometry.coheight_eq_of_isOpenImmersion hV.fromSpec (x := y)
    have h2 := AlgebraicGeometry.idealHeight_eq_coheight Γ(X, V) y
    exact h1.trans (h2.symm.trans hph)
  have : IsDiscreteValuationRing (X.presheaf.stalk (hV.fromSpec y)) :=
    isDiscreteValuationRing_stalk_of_isRegular _ hz
  obtain ⟨v, hv⟩ := exists_units_stalk_algebraMap_eq_of_ord_eq_zero _ hz hf (h _ (hVW hzV) hz)
  let : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) :=
    X.presheaf.algebra_section_stalk ⟨hV.fromSpec y, hzV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) p :=
    hV.isLocalization_stalk' y hzV
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) X.functionField :=
    AlgebraicGeometry.functionField_isScalarTower X V ⟨hV.fromSpec y, hzV⟩
  obtain ⟨⟨u, s⟩, hus⟩ := IsLocalization.surj p.primeCompl (v : X.presheaf.stalk (hV.fromSpec y))
  -- hus : v * algebraMap s = algebraMap u
  have hu : u ∈ p.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (hV.fromSpec y)) p, ← hus]
    exact v.isUnit.mul (IsLocalization.map_units (X.presheaf.stalk (hV.fromSpec y)) s)
  refine ⟨u, s, hu, s.2, ?_⟩
  have hK := congrArg (algebraMap (X.presheaf.stalk (hV.fromSpec y)) X.functionField) hus
  rw [map_mul, hv, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hK
  rw [mul_comm]
  exact hK

end AlgebraicGeometry.Scheme

end
