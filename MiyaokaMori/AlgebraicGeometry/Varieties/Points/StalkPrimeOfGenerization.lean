import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Generizations of a point and primes of its local ring

`X` a scheme, `w ⤳ z`. The prime `q_w := (𝔪_w).comap (O_{X,z} → O_{X,w})` of `A := O_{X,z}` is the
point of `Spec A` over `w` (`X.fromSpecStalk z q_w = w`), `O_{X,w}` is the localization of `A` at
`q_w` (algebra structure via `stalkSpecializes`), and `height q_w = coheight w`. Hence
`w ↦ q_w` is a bijection `{w ⤳ z, coheight w = 1} ≃ {q : Spec A, height q = 1}`.

Source: Stacks 01J7 / 02IJ (points of `Spec O_{X,z}` are the generizations of `z`); Mathlib
`range_fromSpecStalk`, `IsAffineOpen.isLocalization_stalk`, `IsLocalization.isLocalization_of_submonoid_le`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The prime of `O_{X,z}` corresponding to the generization `w ⤳ z`: the preimage of the maximal
ideal of `O_{X,w}` under the specialization map `O_{X,z} → O_{X,w}`. -/
def stalkPrimeOfSpecializes {w z : X} (h : w ⤳ z) : PrimeSpectrum (X.presheaf.stalk z) :=
  PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom
    (IsLocalRing.closedPoint (X.presheaf.stalk w))

theorem stalkPrimeOfSpecializes_asIdeal {w z : X} (h : w ⤳ z) :
    (stalkPrimeOfSpecializes h).asIdeal =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk w)).comap (X.presheaf.stalkSpecializes h).hom :=
  rfl

theorem mem_stalkPrimeOfSpecializes_iff {w z : X} (h : w ⤳ z) (a : X.presheaf.stalk z) :
    a ∈ (stalkPrimeOfSpecializes h).asIdeal ↔ ¬ IsUnit (X.presheaf.stalkSpecializes h a) :=
  Iff.rfl

/-- `stalkPrimeOfSpecializes` depends only on the point `w`, not on the proof of `w ⤳ z`. -/
theorem stalkPrimeOfSpecializes_congr {w w' z : X} (e : w = w') (h : w ⤳ z) (h' : w' ⤳ z) :
    stalkPrimeOfSpecializes h = stalkPrimeOfSpecializes h' := by
  subst e; rfl

/-- `Spec O_{X,z} → X` sends `q_w` to `w`. -/
theorem fromSpecStalk_stalkPrimeOfSpecializes {w z : X} (h : w ⤳ z) :
    X.fromSpecStalk z (stalkPrimeOfSpecializes h) = w := by
  have h1 := congrArg (fun φ : Spec (X.presheaf.stalk w) ⟶ X =>
    φ (IsLocalRing.closedPoint (X.presheaf.stalk w))) (SpecMap_stalkSpecializes_fromSpecStalk h)
  simp only [Scheme.Hom.comp_apply] at h1
  exact h1.trans fromSpecStalk_closedPoint

theorem stalkPrimeOfSpecializes_injective {w w' z : X} (h : w ⤳ z) (h' : w' ⤳ z)
    (e : stalkPrimeOfSpecializes h = stalkPrimeOfSpecializes h') : w = w' := by
  rw [← fromSpecStalk_stalkPrimeOfSpecializes h, ← fromSpecStalk_stalkPrimeOfSpecializes h']
  exact congrArg _ e

/-- Every prime of `O_{X,z}` is `q_w` for the generization `w := (Spec O_{X,z} → X) q`. -/
theorem stalkPrimeOfSpecializes_fromSpecStalk {z : X} (q : PrimeSpectrum (X.presheaf.stalk z)) :
    ∃ h : X.fromSpecStalk z q ⤳ z, (stalkPrimeOfSpecializes h) = q := by
  have hw : X.fromSpecStalk z q ⤳ z := by
    have := Set.mem_range_self (f := (X.fromSpecStalk z).base) q
    rw [range_fromSpecStalk] at this
    exact this
  refine ⟨hw, (X.fromSpecStalk z).isEmbedding.injective ?_⟩
  exact fromSpecStalk_stalkPrimeOfSpecializes hw

/-- `O_{X,w}` is the localization of `O_{X,z}` at `q_w` (algebra via `stalkSpecializes`). -/
theorem isLocalization_atPrime_stalkSpecializes {w z : X} (h : w ⤳ z) :
    letI : Algebra (X.presheaf.stalk z) (X.presheaf.stalk w) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk w) (stalkPrimeOfSpecializes h).asIdeal := by
  let : Algebra (X.presheaf.stalk z) (X.presheaf.stalk w) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  obtain ⟨U, hU, hzU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (Set.mem_univ z)
  have hwU : w ∈ U := h.mem_open U.isOpen hzU
  let : Algebra Γ(X, U) (X.presheaf.stalk z) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzU⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk w) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨w, hwU⟩
  have hz : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  have hw : IsLocalization.AtPrime (X.presheaf.stalk w) (hU.primeIdealOf ⟨w, hwU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨w, hwU⟩
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk z) (X.presheaf.stalk w) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change X.presheaf.germ U w hwU r = X.presheaf.stalkSpecializes h (X.presheaf.germ U z hzU r)
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  -- p_w ≤ p_z
  have hle : (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl ≤
      (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl := by
    have hspec : hU.primeIdealOf ⟨w, hwU⟩ ⤳ hU.primeIdealOf ⟨z, hzU⟩ :=
      hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp (by
        rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]
        exact h)
    have hle' : hU.primeIdealOf ⟨w, hwU⟩ ≤ hU.primeIdealOf ⟨z, hzU⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr hspec
    intro r hr hr'
    exact hr (hle' hr')
  have := IsLocalization.isLocalization_of_submonoid_le (X.presheaf.stalk z)
    (X.presheaf.stalk w) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
    (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl hle
  refine IsLocalization.of_le (Submonoid.map (algebraMap Γ(X, U) (X.presheaf.stalk z))
    (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl) _ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    change ¬ (algebraMap Γ(X, U) (X.presheaf.stalk z) y ∈ (stalkPrimeOfSpecializes h).asIdeal)
    rw [mem_stalkPrimeOfSpecializes_iff, not_not]
    have := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk w)
      (hU.primeIdealOf ⟨w, hwU⟩).asIdeal y).mpr hy
    rwa [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z) (X.presheaf.stalk w)] at this
  · intro r hr
    exact not_not.mp ((mem_stalkPrimeOfSpecializes_iff h r).not.mp hr)

/-- `height q_w = coheight w`. -/
theorem height_stalkPrimeOfSpecializes {w z : X} (h : w ⤳ z) :
    (stalkPrimeOfSpecializes h).asIdeal.height = Order.coheight w := by
  let : Algebra (X.presheaf.stalk z) (X.presheaf.stalk w) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have := isLocalization_atPrime_stalkSpecializes h
  have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height (stalkPrimeOfSpecializes h).asIdeal
    (X.presheaf.stalk w)
  rw [ringKrullDim_stalk_eq_coheight] at h1
  exact (WithBot.coe_eq_coe.mp h1).symm

/-- The bijection `{w ⤳ z, coheight w = 1} ≃ {q : Spec O_{X,z}, height q = 1}`, `w ↦ q_w`. -/
def stalkPrimeEquiv (z : X) :
    {w : X // w ⤳ z ∧ Order.coheight w = 1} ≃
      {q : PrimeSpectrum (X.presheaf.stalk z) // q.asIdeal.height = 1} :=
  Equiv.ofBijective
    (fun w => ⟨stalkPrimeOfSpecializes w.2.1, (height_stalkPrimeOfSpecializes w.2.1).trans w.2.2⟩)
    ⟨fun w w' e => Subtype.ext (stalkPrimeOfSpecializes_injective w.2.1 w'.2.1
        (congrArg Subtype.val e)),
      fun q => by
        obtain ⟨hw, hq⟩ := stalkPrimeOfSpecializes_fromSpecStalk q.1
        refine ⟨⟨X.fromSpecStalk z q.1, hw, ?_⟩, Subtype.ext hq⟩
        rw [← height_stalkPrimeOfSpecializes hw, hq]
        exact q.2⟩

theorem stalkPrimeEquiv_apply_val (z : X) (w : {w : X // w ⤳ z ∧ Order.coheight w = 1}) :
    (stalkPrimeEquiv z w).1 = stalkPrimeOfSpecializes w.2.1 := rfl

/-- Scalar tower `O_{X,z} → O_{X,w} → K(X)` for the `stalkSpecializes` algebra structure. -/
theorem isScalarTower_stalkSpecializes_functionField [IrreducibleSpace X] {w z : X} (h : w ⤳ z) :
    letI : Algebra (X.presheaf.stalk z) (X.presheaf.stalk w) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsScalarTower (X.presheaf.stalk z) (X.presheaf.stalk w) X.functionField := by
  let : Algebra (X.presheaf.stalk z) (X.presheaf.stalk w) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  change X.presheaf.stalkSpecializes _ a =
    X.presheaf.stalkSpecializes _ (X.presheaf.stalkSpecializes h a)
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

end AlgebraicGeometry.Scheme

end
