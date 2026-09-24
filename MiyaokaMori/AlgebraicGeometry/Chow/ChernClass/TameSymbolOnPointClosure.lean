import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameSymbolUnitTwist
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointGeneric
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldEqResidueFieldAtGenericPoint
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionPullbackDominant
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdGenerator
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdRestrict
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureTransport
import MiyaokaMori.RingTheory.KeyLemma.Stacks0eax
import MiyaokaMori.RingTheory.KeyLemma.TameOrdBridge
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.StalkPrimeOfGenerization
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureStalkQuotient
import MiyaokaMori.RingTheory.KeyLemma.TameSymbolRingEquivInvariance

/-! # tame symbol as a rational function on the point closure (Stacks 0AYC, step (G2))

`X` integral, locally Noetherian, `w : X` of coheight 1, `B_w := O_{X,w}` (one-dimensional Noetherian
local domain, fraction field `K(X)`).  The tame symbol `∂_{B_w}(f, g) ∈ κ(w)^*` (Stacks 0EAQ,
`Ring.tameSymbol`) is transported to `K(W_w)^*`, `W_w := X.pointClosure w`, along the canonical field
homomorphism `κ(w) → κ_{W_w}(η) ≅ K(W_w)` (Stacks 0AYC uses `κ(ξ_i) = K(Z_i)` tacitly).

Source: Stacks 0AYC (chow-lemma-key-formula), second paragraph; 0EAQ; 0EAS(4)(6); 0EAN.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The canonical field homomorphism `κ(w) → K(W_w)`: identify `w` with `ι_w(η)`, apply the
residue field map of the closed immersion `ι_w` at the generic point `η` of `W_w`, then
`κ_{W_w}(η) ≅ K(W_w)` (`functionFieldIsoResidueField`). It is a ring homomorphism between fields,
hence injective; it is in fact bijective (closed immersion ⇒ surjective stalk map), which is only
needed in proofs. -/
def residueFieldToPointClosureFunctionField (w : X) :
    X.residueField w →+* (X.pointClosure w).functionField :=
  ((X.residueFieldCongr (pointClosureι_genericPoint w).symm).hom ≫
    (X.pointClosureι w).residueFieldMap (genericPoint (X.pointClosure w)) ≫
    (X.pointClosure w).functionFieldIsoResidueField.inv).hom

/-- The image of a unit `a ∈ O_{X,w}^*` in `K(W_w)^*` (its residue class). -/
def residueUnitOnPointClosure (w : X) (a : (X.presheaf.stalk w)ˣ) :
    (X.pointClosure w).functionFieldˣ :=
  Units.map (X.residueFieldToPointClosureFunctionField w).toMonoidHom
    (Units.map (X.residue w).hom.toMonoidHom a)

/-- `κ(w) → K(W_w)` applied to the residue class of `b ∈ O_{X,w}` is `ι_w^♯(b)` (moved to the stalk at `ι_w η`). -/
theorem residueFieldToPointClosureFunctionField_residue (w : X) (b : X.presheaf.stalk w) :
    X.residueFieldToPointClosureFunctionField w (X.residue w b) =
      ((X.pointClosureι w).stalkMap (genericPoint (X.pointClosure w))).hom
        (X.presheaf.stalkSpecializes (specializes_of_eq (pointClosureι_genericPoint w)) b) := by
  have h1 := congrArg (fun f => f.hom b)
    (residue_residueFieldCongr X (pointClosureι_genericPoint w).symm)
  have h2 := congrArg (fun f => f.hom ((X.presheaf.stalkCongr
      (Inseparable.of_eq (pointClosureι_genericPoint w).symm)).hom b))
    (residue_residueFieldMap (X.pointClosureι w) (genericPoint (X.pointClosure w)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
  show ((X.pointClosure w).functionFieldIsoResidueField.inv.hom
    (((X.pointClosureι w).residueFieldMap (genericPoint (X.pointClosure w))).hom
      ((X.residueFieldCongr (pointClosureι_genericPoint w).symm).hom.hom ((X.residue w).hom b)))) = _
  rw [h1, h2]
  have h3 := congrArg (fun f => f.hom (((X.pointClosureι w).stalkMap (genericPoint (X.pointClosure w))).hom
      ((X.presheaf.stalkCongr (Inseparable.of_eq (pointClosureι_genericPoint w).symm)).hom b)))
    (X.pointClosure w).functionFieldIsoResidueField.hom_inv_id
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at h3
  refine h3.trans ?_
  rw [TopCat.Presheaf.stalkCongr_hom]

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The tame symbol `∂_{O_{X,w}}(f, g)` as an element of `K(W_w)^*` (Stacks 0AYC, `∂_{B_i}(f_i, g_i)`).
Requires `coheight w = 1` (so that `O_{X,w}` is one-dimensional) and the finiteness of the normalization
of `O_{X,w}` inside `K(X)` (the `hfin` of `Ring.tameSymbol`, needed for 0EAN). -/
def keyFormulaTameSymbol (w : X) (hw : Order.coheight w = 1)
    (hfin : Module.Finite (X.presheaf.stalk w) (integralClosure (X.presheaf.stalk w) X.functionField))
    (f g : X.functionFieldˣ) : (X.pointClosure w).functionFieldˣ :=
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
  Units.map (X.residueFieldToPointClosureFunctionField w).toMonoidHom
    (Units.mk0 (Ring.tameSymbol (X.presheaf.stalk w) hfin f g) (Ring.tameSymbol_ne_zero _ hfin f g))

/-- The cycle `(ι_w)_* div(∂_{O_{X,w}}(f, g))` on `X` (Stacks 0AYC: `(Z_i → X)_* div(∂_{B_i}(f_i, g_i))`). -/
def keyFormulaTameCycle (w : X) (hw : Order.coheight w = 1)
    (hfin : Module.Finite (X.presheaf.stalk w) (integralClosure (X.presheaf.stalk w) X.functionField))
    (f g : X.functionFieldˣ) : AlgebraicCycle X ℤ :=
  haveI : IsLocallyNoetherian (X.pointClosure w) := isLocallyNoetherian_pointClosure w
  AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
    ((X.pointClosure w).principalCycle (X.keyFormulaTameSymbol w hw hfin f g))

/-- `(ι_w)_* div(ā)` for a unit `a ∈ O_{X,w}^*`. -/
def residueUnitCycle (w : X) (a : (X.presheaf.stalk w)ˣ) : AlgebraicCycle X ℤ :=
  haveI : IsLocallyNoetherian (X.pointClosure w) := isLocallyNoetherian_pointClosure w
  AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
    ((X.pointClosure w).principalCycle (X.residueUnitOnPointClosure w a))

/-- `keyFormulaTameCycle` is a Stacks 02RW generator of `ratEquivZero X n` when `height w = n + 1`. -/
theorem isRatEquivGen_keyFormulaTameCycle (w : X) (hw : Order.coheight w = 1)
    (hfin : Module.Finite (X.presheaf.stalk w) (integralClosure (X.presheaf.stalk w) X.functionField))
    (f g : X.functionFieldˣ) (n : ℕ) (hn : Order.height w = ((n + 1 : ℕ) : ℕ∞)) :
    IsRatEquivGen X n w (X.keyFormulaTameCycle w hw hfin f g) :=
  ⟨hn, isIntegral_pointClosure w, inferInstance, isLocallyNoetherian_pointClosure w,
    X.keyFormulaTameSymbol w hw hfin f g, rfl⟩

/-- `residueUnitCycle` is a Stacks 02RW generator of `ratEquivZero X n` when `height w = n + 1`. -/
theorem isRatEquivGen_residueUnitCycle (w : X) (a : (X.presheaf.stalk w)ˣ) (n : ℕ)
    (hn : Order.height w = ((n + 1 : ℕ) : ℕ∞)) :
    IsRatEquivGen X n w (X.residueUnitCycle w a) :=
  ⟨hn, isIntegral_pointClosure w, inferInstance, isLocallyNoetherian_pointClosure w,
    X.residueUnitOnPointClosure w a, rfl⟩

/-- **Unit twist of the tame symbol on `W_w` (Stacks 0AYC, second paragraph; 0EAS(4)(6) + 0EAN).**
For `a, b ∈ O_{X,w}^*` and `f, g ∈ K(X)^*`:
`∂_w(a f, b g) = ∂_w(f, g) · ā^{ord_w g} · b̄^{-ord_w f}` in `K(W_w)^*`.
This is `Ring.tameSymbol_unit_mul` (`TameSymbolUnitTwist.lean`) pushed through the field
homomorphism `κ(w) → K(W_w)`, with `ord_w = X.ord` (Mathlib `Scheme.ord`, which is `Ring.ordFrac` of
`O_{X,w}` since `coheight w = 1`). -/
theorem keyFormulaTameSymbol_unit_mul (w : X) (hw : Order.coheight w = 1)
    (hfin : Module.Finite (X.presheaf.stalk w) (integralClosure (X.presheaf.stalk w) X.functionField))
    (a b : (X.presheaf.stalk w)ˣ) (f g : X.functionFieldˣ) :
    X.keyFormulaTameSymbol w hw hfin
        (Units.map (algebraMap (X.presheaf.stalk w) X.functionField).toMonoidHom a * f)
        (Units.map (algebraMap (X.presheaf.stalk w) X.functionField).toMonoidHom b * g)
      = X.keyFormulaTameSymbol w hw hfin f g *
          X.residueUnitOnPointClosure w a ^ X.ord (g : X.functionField) w *
          (X.residueUnitOnPointClosure w b ^ X.ord (f : X.functionField) w)⁻¹ := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
  have hg := Scheme.ord_eq_unzero_ordHom hw g.ne_zero
  have hf := Scheme.ord_eq_unzero_ordHom hw f.ne_zero
  set φ := X.residueFieldToPointClosureFunctionField w with hφ
  have key : ∀ (x y z : X.residueField w) (m n : ℤ),
      φ (x * y ^ n * (z ^ m)⁻¹) = φ x * φ y ^ n * (φ z ^ m)⁻¹ := fun x y z m n => by
    rw [map_mul, map_mul, map_inv₀, map_zpow₀, map_zpow₀]
  apply Units.ext
  simp only [keyFormulaTameSymbol, residueUnitOnPointClosure, Units.val_mul, Units.coe_map,
    Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
  erw [Units.val_mk0, Units.val_mk0]
  rw [Ring.tameSymbol_unit_mul, hg, hf]
  exact key _ _ _ _ _

/-- **Tame symbol of two units is trivial (0EAN)**: `f, g ∈ O_{X,w}^*` ⇒ `∂_w(f, g) = 1`. -/
theorem keyFormulaTameSymbol_unit_unit (w : X) (hw : Order.coheight w = 1)
    (hfin : Module.Finite (X.presheaf.stalk w) (integralClosure (X.presheaf.stalk w) X.functionField))
    (a b : (X.presheaf.stalk w)ˣ) :
    X.keyFormulaTameSymbol w hw hfin
        (Units.map (algebraMap (X.presheaf.stalk w) X.functionField).toMonoidHom a)
        (Units.map (algebraMap (X.presheaf.stalk w) X.functionField).toMonoidHom b) = 1 := by
  have h := X.keyFormulaTameSymbol_unit_mul w hw hfin a b 1 1
  rw [mul_one, mul_one] at h
  rw [h]
  have h1 : X.ord ((1 : X.functionFieldˣ) : X.functionField) w = 0 := by
    rw [Units.val_one]
    have := Scheme.ord_mul (X := X) (x := w) one_ne_zero one_ne_zero
    rw [mul_one] at this
    linarith
  rw [h1, zpow_zero, zpow_zero, inv_one, mul_one, mul_one]
  -- ∂(1, 1) = 1
  apply Units.ext
  have : Ring.KrullDimLE 1 (X.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
  have h2 := Ring.tameSymbol_mul_left (X.presheaf.stalk w) (K := X.functionField) hfin 1 1 1
  rw [one_mul] at h2
  have h3 : Ring.tameSymbol (X.presheaf.stalk w) (K := X.functionField) hfin 1 1 = 1 :=
    mul_left_cancel₀ (Ring.tameSymbol_ne_zero _ hfin 1 1) (h2.symm.trans (mul_one _).symm)
  simp only [keyFormulaTameSymbol, Units.coe_map, h3, Units.val_one]
  erw [Units.val_mk0]
  exact map_one _


section KeyLemmaTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Transport to the ring-level Key Lemma (Stacks 0EAX, `Stacks0eax.lean`)

`A := O_{X,z}`, `φ : K(X) ≅ Frac A`. For `w ⤳ z` with `coheight w = 1`, `q_w := stalkPrimeOfSpecializes`
is a height-one prime of `A`, `O_{X,w} ≅ A_{q_w}` (`isLocalization_atPrime_stalkSpecializes`), and the
local ring of `W_w` at the point over `z` is `A / q_w` (`stalkQuotEquivOfIsClosedImmersion`). -/

/-- `K(X) ≅ Frac(O_{X,z})` as `O_{X,z}`-algebras. -/
def functionFieldEquivFractionRing (z : X) :
    X.functionField ≃ₐ[X.presheaf.stalk z] FractionRing (X.presheaf.stalk z) :=
  (FractionRing.algEquiv (X.presheaf.stalk z) X.functionField).symm

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- `dim O_{X,z} = 2` when `coheight z = 2`. -/
theorem ringKrullDim_stalk_eq_two {z : X} (hz : Order.coheight z = 2) :
    ringKrullDim (X.presheaf.stalk z) = 2 := by
  rw [ringKrullDim_stalk_eq_coheight, hz]; rfl

/-- Compatibility of `φ` with `O_{X,w} ≅ (O_{X,z})_{q_w}` and the maps to the fraction fields. -/
theorem functionFieldEquivFractionRing_algebraMap_algEquiv {w z : X} (h : w ⤳ z) :
    letI : Algebra (X.presheaf.stalk z) (X.presheaf.stalk w) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    haveI := isLocalization_atPrime_stalkSpecializes h
    ∀ x : Localization.AtPrime (stalkPrimeOfSpecializes h).asIdeal,
      functionFieldEquivFractionRing z (algebraMap (X.presheaf.stalk w) X.functionField
        (IsLocalization.algEquiv (stalkPrimeOfSpecializes h).asIdeal.primeCompl
          (Localization.AtPrime (stalkPrimeOfSpecializes h).asIdeal) (X.presheaf.stalk w) x)) =
      algebraMap (Localization.AtPrime (stalkPrimeOfSpecializes h).asIdeal)
        (FractionRing (X.presheaf.stalk z)) x := by
  letI : Algebra (X.presheaf.stalk z) (X.presheaf.stalk w) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  haveI := isLocalization_atPrime_stalkSpecializes h
  haveI := isScalarTower_stalkSpecializes_functionField h
  intro x
  set e := IsLocalization.algEquiv (stalkPrimeOfSpecializes h).asIdeal.primeCompl
    (Localization.AtPrime (stalkPrimeOfSpecializes h).asIdeal) (X.presheaf.stalk w) with he
  have key := IsLocalization.ringHom_ext (stalkPrimeOfSpecializes h).asIdeal.primeCompl
    (j := ((functionFieldEquivFractionRing z : X.functionField →+* FractionRing (X.presheaf.stalk z)).comp
      ((algebraMap (X.presheaf.stalk w) X.functionField).comp
        (e : Localization.AtPrime (stalkPrimeOfSpecializes h).asIdeal →+* X.presheaf.stalk w))))
    (k := algebraMap (Localization.AtPrime (stalkPrimeOfSpecializes h).asIdeal)
      (FractionRing (X.presheaf.stalk z))) (by
      ext a
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes,
        ← IsScalarTower.algebraMap_apply])
  exact RingHom.congr_fun key x

/-- The hypothesis `hfin` of Stacks 0EAX (`Ring.tameSymbol_milnorGersten_lowDegree`) from `hnorm`. -/
theorem keyFormula_hfin
    (hnorm : ∀ x : X, Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField)) (z : X) :
    ∀ q : PrimeSpectrum (X.presheaf.stalk z), q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing (X.presheaf.stalk z))) := by
  intro q _
  obtain ⟨hw, hq⟩ := stalkPrimeOfSpecializes_fromSpecStalk q
  rw [← hq]
  letI : Algebra (X.presheaf.stalk z) (X.presheaf.stalk (X.fromSpecStalk z q)) :=
    (X.presheaf.stalkSpecializes hw).hom.toAlgebra
  haveI := isLocalization_atPrime_stalkSpecializes hw
  have hc := functionFieldEquivFractionRing_algebraMap_algEquiv hw
  set e := IsLocalization.algEquiv (stalkPrimeOfSpecializes hw).asIdeal.primeCompl
    (Localization.AtPrime (stalkPrimeOfSpecializes hw).asIdeal)
    (X.presheaf.stalk (X.fromSpecStalk z q)) with he
  refine Ring.TameSymbol.moduleFinite_integralClosure_of_ringEquiv e.symm.toRingEquiv
    (functionFieldEquivFractionRing z).toRingEquiv (fun a => ?_) (hnorm _)
  have := hc (e.symm a)
  simpa using this

/-- The hypothesis `hB` of Stacks 0EAX from `hnorm z`. -/
theorem keyFormula_hB
    (hnorm : ∀ x : X, Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField)) (z : X) :
    Module.Finite (X.presheaf.stalk z)
      (integralClosure (X.presheaf.stalk z) (FractionRing (X.presheaf.stalk z))) :=
  Ring.TameSymbol.moduleFinite_integralClosure_of_ringEquiv (RingEquiv.refl _)
    (functionFieldEquivFractionRing z).toRingEquiv
    (fun a => by simp [AlgEquiv.commutes]) (hnorm z)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- `toAdd (unzero v) = log v`. -/
theorem toAdd_unzero_eq_log (v : WithZero (Multiplicative ℤ)) (hv : v ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero hv) = WithZero.log v := by
  conv_rhs => rw [← WithZero.coe_unzero hv]
  rfl

/-- **Per-point identity (Stacks 0AYC, last paragraph): the coefficient of `(ι_w)_* div(∂_w(f, g))` at
`z` is `ord_{A/q_w}(∂_{A_{q_w}}(φ f, φ g))`**, the `q_w`-term of Stacks 0EAX for `A = O_{X,z}`. -/
theorem keyFormulaTameCycle_apply_eq_log_tameOrd
    (hnorm : ∀ x : X, Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField))
    {z : X} (hz : Order.coheight z = 2) (f g : X.functionFieldˣ)
    {w : X} (hwz : w ⤳ z) (hw : Order.coheight w = 1) :
    X.keyFormulaTameCycle w hw (hnorm w) f g z =
      WithZero.log (Ring.tameOrd (X.presheaf.stalk z) (ringKrullDim_stalk_eq_two hz)
        (keyFormula_hfin hnorm z)
        ⟨stalkPrimeOfSpecializes hwz, (height_stalkPrimeOfSpecializes hwz).trans hw⟩
        (Units.map (functionFieldEquivFractionRing z : X.functionField →* FractionRing _) f)
        (Units.map (functionFieldEquivFractionRing z : X.functionField →* FractionRing _) g)) := by
  classical
  haveI hLN : IsLocallyNoetherian (X.pointClosure w) := isLocallyNoetherian_pointClosure w
  haveI hInt : IsIntegral (X.pointClosure w) := isIntegral_pointClosure w
  have hA := ringKrullDim_stalk_eq_two hz
  -- z = ι z'
  have hz_range : z ∈ Set.range (X.pointClosureι w).base := by
    rw [MiyaokaMori.PointClosureTransport.range_eq_closure_of_isClosedImmersion (X.pointClosureι w),
      pointClosureι_genericPoint]
    exact specializes_iff_mem_closure.mp hwz
  obtain ⟨z', hz'⟩ := hz_range
  subst hz'
  have hη : (X.pointClosureι w).base (genericPoint (X.pointClosure w)) = w :=
    pointClosureι_genericPoint w
  have hηz' : genericPoint (X.pointClosure w) ⤳ z' := genericPoint_specializes' z'
  -- the prime `q` of `A` at `w`; the closed-immersion kernel is computed at `ι η = w`
  set q := stalkPrimeOfSpecializes hwz with hqdef
  have hq : q.asIdeal.height = 1 := (height_stalkPrimeOfSpecializes hwz).trans hw
  have hqq : stalkPrimeOfSpecializes ((X.pointClosureι w).base.hom.map_specializes hηz') = q :=
    stalkPrimeOfSpecializes_congr hη _ _
  -- `O_{W,z'} ≅ A / q`
  set eQ : (X.pointClosure w).presheaf.stalk z' ≃+*
      X.presheaf.stalk ((X.pointClosureι w).base z') ⧸ q.asIdeal :=
    (stalkQuotEquivOfIsClosedImmersion (X.pointClosureι w) z').trans
      (Ideal.quotEquivOfEq (congrArg PrimeSpectrum.asIdeal hqq)) with heQ
  have heQ_symm : ∀ a, eQ.symm (Ideal.Quotient.mk _ a) = (X.pointClosureι w).stalkMap z' a := by
    intro a
    rw [RingEquiv.symm_apply_eq, heQ, RingEquiv.trans_apply,
      stalkQuotEquivOfIsClosedImmersion_stalkMap, Ideal.quotEquivOfEq_mk]
  -- coheight of z' in W is 1
  have hcoh : Order.coheight z' = 1 := by
    apply le_antisymm
    · have h1 : ringKrullDim ((X.pointClosure w).presheaf.stalk z') ≤ 1 := by
        rw [ringKrullDim_eq_of_ringEquiv eQ]
        exact Ring.krullDimLE_iff.mp (Ring.krullDimLE_one_quotient_of_height_eq_one hA q hq)
      rw [ringKrullDim_stalk_eq_coheight] at h1
      exact_mod_cast h1
    · rw [ENat.one_le_iff_ne_zero, Order.coheight_ne_zero]
      intro hmax
      have h1 : z' ⤳ genericPoint (X.pointClosure w) := hmax (show z' ≤ _ from hηz')
      have heq : z' = genericPoint (X.pointClosure w) := (h1.antisymm hηz').eq
      apply absurd hz
      rw [heq, hη, hw]
      decide
  -- unfold the cycle coefficient
  unfold keyFormulaTameCycle
  rw [MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply,
    Scheme.principalCycle_apply, Scheme.ord_eq_unzero_ordHom hcoh (Units.ne_zero _),
    toAdd_unzero_eq_log]
  unfold Ring.tameOrd
  congr 1
  -- set-up of the rings and isomorphisms
  letI : Algebra (X.presheaf.stalk ((X.pointClosureι w).base z')) (X.presheaf.stalk w) :=
    (X.presheaf.stalkSpecializes hwz).hom.toAlgebra
  haveI := isLocalization_atPrime_stalkSpecializes hwz
  haveI := isScalarTower_stalkSpecializes_functionField hwz
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
  haveI : Ring.KrullDimLE 1 ((X.pointClosure w).presheaf.stalk z') := krullDimLE_of_coheight_le hcoh.le
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) :=
    Ring.krullDimLE_one_localization_of_height_eq_one q hq
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk ((X.pointClosureι w).base z') ⧸ q.asIdeal) :=
    Ring.krullDimLE_one_quotient_of_height_eq_one hA q hq
  haveI := q.isPrime
  set eW := IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
    (X.presheaf.stalk w) with heW
  set φ := functionFieldEquivFractionRing ((X.pointClosureι w).base z') with hφ
  -- compatibility of `φ⁻¹` with `eW`
  have hcompat : ∀ x : Localization.AtPrime q.asIdeal,
      φ.symm.toRingEquiv (algebraMap (Localization.AtPrime q.asIdeal)
        (FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z'))) x) =
      algebraMap (X.presheaf.stalk w) X.functionField (eW.toRingEquiv x) := by
    intro x
    have key := IsLocalization.ringHom_ext q.asIdeal.primeCompl
      (j := φ.symm.toRingEquiv.toRingHom.comp
        (algebraMap (Localization.AtPrime q.asIdeal)
          (FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z')))))
      (k := (algebraMap (X.presheaf.stalk w) X.functionField).comp eW.toRingEquiv.toRingHom) (by
        ext a
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply])
    exact RingHom.congr_fun key x
  -- tame symbol transport (step 5)
  have htame := Ring.TameSymbol.tameSymbol_ringEquiv eW.toRingEquiv φ.symm.toRingEquiv hcompat
    (keyFormula_hfin hnorm _ q hq) (hnorm w)
    (Units.map (φ : X.functionField →* FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z'))) f)
    (Units.map (φ : X.functionField →* FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z'))) g)
  have hff : Units.map (φ.symm.toRingEquiv :
        FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z')) →* X.functionField)
      (Units.map (φ : X.functionField →* FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z'))) f)
        = f := by
    ext; simp
  have hgg : Units.map (φ.symm.toRingEquiv :
        FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z')) →* X.functionField)
      (Units.map (φ : X.functionField →* FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z'))) g)
        = g := by
    ext; simp
  rw [hff, hgg] at htame
  -- the value of the symbol in `K(W)`
  have hval : ((X.keyFormulaTameSymbol w hw (hnorm w) f g : (X.pointClosure w).functionFieldˣ) :
      (X.pointClosure w).functionField) =
      X.residueFieldToPointClosureFunctionField w
        (IsLocalRing.ResidueField.mapEquiv eW.toRingEquiv
          (Ring.tameSymbol (Localization.AtPrime q.asIdeal) (keyFormula_hfin hnorm _ q hq)
            (Units.map (φ : X.functionField →* FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z'))) f)
            (Units.map (φ : X.functionField →* FractionRing (X.presheaf.stalk ((X.pointClosureι w).base z'))) g))) := by
    rw [htame]
    simp only [keyFormulaTameSymbol, Units.coe_map]
    erw [Units.val_mk0]
    rfl
  -- transport of `ord` along `O_{W,z'} ≅ A / q'` (step 4)
  set ψ : q.asIdeal.ResidueField →+* (X.pointClosure w).functionField :=
    (X.residueFieldToPointClosureFunctionField w).comp
      (IsLocalRing.ResidueField.mapEquiv eW.toRingEquiv).toRingHom with hψ
  have hψcompat : ∀ r : X.presheaf.stalk ((X.pointClosureι w).base z') ⧸ q.asIdeal,
      ψ (algebraMap _ q.asIdeal.ResidueField r) =
        algebraMap ((X.pointClosure w).presheaf.stalk z') (X.pointClosure w).functionField (eQ.symm r) := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [heQ_symm, Ideal.algebraMap_quotient_residueField_mk]
    have h1 : algebraMap (X.presheaf.stalk ((X.pointClosureι w).base z')) q.asIdeal.ResidueField a =
        IsLocalRing.residue (Localization.AtPrime q.asIdeal)
          (algebraMap _ (Localization.AtPrime q.asIdeal) a) := by
      rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime q.asIdeal) q.asIdeal.ResidueField a,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hres : ∀ y : Localization.AtPrime q.asIdeal,
        X.residueFieldToPointClosureFunctionField w
          (IsLocalRing.ResidueField.mapEquiv eW.toRingEquiv (IsLocalRing.residue _ y)) =
        (X.pointClosureι w).stalkMap (genericPoint (X.pointClosure w))
          (X.presheaf.stalkSpecializes (specializes_of_eq hη) (eW y)) := by
      intro y
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      exact residueFieldToPointClosureFunctionField_residue w (eW y)
    rw [h1, hψ]
    change X.residueFieldToPointClosureFunctionField w
      (IsLocalRing.ResidueField.mapEquiv eW.toRingEquiv
        (IsLocalRing.residue _ (algebraMap _ (Localization.AtPrime q.asIdeal) a))) = _
    rw [hres, eW.commutes]
    change _ = (X.pointClosure w).presheaf.stalkSpecializes hηz' ((X.pointClosureι w).stalkMap z' a)
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
    congr 1
    show X.presheaf.stalkSpecializes _ (X.presheaf.stalkSpecializes hwz a) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  rw [hval]
  change Ring.ordFrac ((X.pointClosure w).presheaf.stalk z') (ψ _) = _
  exact Ring.ordFrac_ringEquiv eQ.symm ψ hψcompat _

/-- **Scheme-level Key Lemma (Stacks 0EAX at a codimension-2 point).**

Statement: `X` integral, locally Noetherian; every stalk has finite normalization inside `K(X)`
(`hnorm`); `z : X` with `coheight z = 2` (so `A := O_{X,z}` is a two-dimensional Noetherian local
domain); `f, g ∈ K(X)^*`. Let `T := {w | w ⤳ z, coheight w = 1}` (the codimension-1 points of `X`
specializing to `z`, i.e. the height-1 primes of `A`). Then only finitely many `w ∈ T` have
`((ι_w)_* div(∂_w(f, g))) z ≠ 0`, and `Σ_{w ∈ T} ((ι_w)_* div(∂_w(f, g))) z = 0`.

Source: Stacks 0EAX (chow-lemma-milnor-gersten-low-degree), in the form used in the proof of 0AYC
(chow-lemma-key-formula, last paragraph: "the coefficient of `z` in `Σ_i (Z_i → X)_* div(∂_{B_i}(f, g))`
is `Σ_q ord_{A/q}(∂_{A_q}(f, g))`, which is zero by Lemma 0EAX").

Natural-language proof (all steps are transport; the mathematics is `Ring.tameSymbol_milnorGersten_lowDegree`,
`Stacks0eax.lean`):
1. `A := O_{X,z}`: Noetherian (`IsLocallyNoetherian`), local domain, `ringKrullDim A = coheight z = 2`
   (Mathlib `ringKrullDim_stalk_eq_coheight`). `K(X)` is a fraction field of `A`; fix the
   field isomorphism `φ : K(X) ≃ FractionRing A` (`IsFractionRing.algEquiv`).
2. Height-1 primes `q` of `A` ↔ points `w ∈ T`: `w ↦ q_w := ker(A → O_{X,w})`; conversely `q ↦` the
   point of `Spec A → X` (`X.fromSpecStalk z`, Mathlib) at `q`. Both `A_{q_w}` and `O_{X,w}` are
   localizations of `Γ(U)` (`U` an affine open around `z`) at the prime of `w`
   (`IsAffineOpen.isLocalization_stalk`), so `O_{X,w} ≃ A_{q_w}` compatibly with the maps to `K(X)`
   and `FractionRing A`; height/coheight match (`IsLocalization.AtPrime.ringKrullDim_eq_height`).
3. Residue fields: `κ(w) = ResidueField O_{X,w} ≃ q_w.ResidueField` (induced by 2.), and
   `κ(w) → K(W_w)` (`residueFieldToPointClosureFunctionField`) is bijective (`ι_w` is a closed
   immersion, so its stalk maps are surjective; a ring map between fields is injective).
4. Local rings of `W_w` at `z`: `O_{W_w, z'} ≃ A / q_w` (`z'` the unique point of `W_w` over `z`;
   `W_w = closure {w}` with reduced structure, so on an affine open `U ∋ z`, `W_w ∩ U = Spec(Γ(U)/p_w)`,
   whose local ring at `z` is `(Γ(U)/p_w)_{p_z} = A / q_w`). Under 3. and 4. the fraction fields
   correspond, so `(W_w).ord h z' = ord_{A/q_w}(h̄)` (`Ring.ordFrac_ringEquiv`, `OrdOpenImmersion.lean:45`).
5. The tame symbol is invariant under compatible isomorphisms `(A, K) ≃ (A', K')` (its definition
   `Ring.tameSymbol` only uses the integral closure of the image of `A` in `K`, the height-one spectrum of
   that Dedekind ring, valuations, and norms of residue fields: each is transported by the
   induced isomorphism `integralClosure A K ≃ integralClosure A' K'`). Hence
   `∂_{O_{X,w}}(f, g) ↦ ∂_{A_{q_w}}(φ f, φ g)` under 3.
6. `((ι_w)_* div(∂_w(f,g))) z = (W_w).ord (∂_w(f,g)) z'` (`properPushforward_closedImmersion_apply`)
   `= ord_{A/q_w}(∂_{A_{q_w}}(φ f, φ g))` (4., 5.) `= toAdd (Ring.tameOrd A hA hfin q_w (φ f) (φ g))`.
   Summing over `T ≃ {q | height q = 1}` and applying `Ring.tameSymbol_milnorGersten_lowDegree`
   (finite support + `∏ᶠ = 1`, i.e. `Σ = 0` additively) gives both claims. The hypotheses `hB`, `hfin`
   of 0EAX are `hnorm z` and `hnorm w` (transported along 2.; `integralClosure` commutes with the
   isomorphisms of 2.).

Edge cases: `T = ∅` cannot happen for `coheight z = 2` (there is a chain `w ⤳ z`), but the statement is
true anyway (empty sum). `f = g`: `∂(f, f) = ∂(f, -1)` (0EAS), still summing to 0. -/
theorem keyFormula_finsum_tameCycle_eq_zero
    (hnorm : ∀ x : X, Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField))
    (z : X) (hz : Order.coheight z = 2) (f g : X.functionFieldˣ) :
    (Function.support fun w : {w : X // w ⤳ z ∧ Order.coheight w = 1} =>
      X.keyFormulaTameCycle w.1 w.2.2 (hnorm w.1) f g z).Finite ∧
    ∑ᶠ w : {w : X // w ⤳ z ∧ Order.coheight w = 1},
      X.keyFormulaTameCycle w.1 w.2.2 (hnorm w.1) f g z = 0 := by
  classical
  have hA := ringKrullDim_stalk_eq_two hz
  have hfin' := keyFormula_hfin hnorm z
  have hB := keyFormula_hB hnorm z
  set φ : X.functionField →* FractionRing (X.presheaf.stalk z) :=
    (functionFieldEquivFractionRing z : X.functionField →* FractionRing (X.presheaf.stalk z)) with hφ
  have hmain := Ring.tameSymbol_milnorGersten_lowDegree (X.presheaf.stalk z) hA hB hfin'
    (Units.map φ f) (Units.map φ g)
  set F : {q : PrimeSpectrum (X.presheaf.stalk z) // q.asIdeal.height = 1} → WithZero (Multiplicative ℤ) :=
    fun q => Ring.tameOrd (X.presheaf.stalk z) hA hfin' q (Units.map φ f) (Units.map φ g) with hFdef
  change (Function.mulSupport F).Finite ∧ ∏ᶠ q, F q = 1 at hmain
  obtain ⟨hFfin, hFprod⟩ := hmain
  have hF0 : ∀ q, F q ≠ 0 := fun q => by
    have h1 := Ring.krullDimLE_one_localization_of_height_eq_one q.1 q.2
    have h2 := Ring.krullDimLE_one_quotient_of_height_eq_one hA q.1 q.2
    show Ring.ordFrac _ (Ring.tameSymbol _ _ _ _) ≠ 0
    exact (map_ne_zero _).mpr (Ring.tameSymbol_ne_zero _ _ _ _)
  set G : {q : PrimeSpectrum (X.presheaf.stalk z) // q.asIdeal.height = 1} → ℤ :=
    fun q => WithZero.log (F q) with hGdef
  have hGsupp : (Function.support G).Finite := hFfin.subset fun q hq => by
    simp only [Function.mem_support, Function.mem_mulSupport, hGdef] at hq ⊢
    intro h1
    exact hq (by rw [h1, WithZero.log_one])
  have hc : ∀ w : {w : X // w ⤳ z ∧ Order.coheight w = 1},
      X.keyFormulaTameCycle w.1 w.2.2 (hnorm w.1) f g z = G (stalkPrimeEquiv z w) :=
    fun w => keyFormulaTameCycle_apply_eq_log_tameOrd hnorm hz f g w.2.1 w.2.2
  refine ⟨?_, ?_⟩
  · have : (Function.support fun w : {w : X // w ⤳ z ∧ Order.coheight w = 1} =>
        X.keyFormulaTameCycle w.1 w.2.2 (hnorm w.1) f g z) = (stalkPrimeEquiv z) ⁻¹' Function.support G := by
      ext w
      simp only [Function.mem_support, Set.mem_preimage, hc]
    rw [this]
    exact hGsupp.preimage (stalkPrimeEquiv z).injective.injOn
  · rw [finsum_congr hc, finsum_comp_equiv (stalkPrimeEquiv z)]
    apply WithZero.exp_injective
    rw [WithZero.exp_zero, KeyLemma.exp_finsum G hGsupp, ← hFprod]
    exact finprod_congr fun q => WithZero.exp_log (hF0 q)

end KeyLemmaTransport

/-- **Coefficient of `(ι_w)_* div_{ι_w^* N}(t_w|_{W_w})` at `z` via a local generator at `z`
(Stacks 0AYC, third paragraph: `s_i = a_i s`, `t_i = b_i t` with `a_i, b_i ∈ A_{q_i}^*`).**

Statement: `N` a line bundle on `X`; `w ⤳ z`, `coheight w = 1`; `τ` a generator of `N_z`;
`b ∈ O_{X,w}^*`. Let `t_w := b • (τ specialized to w) ∈ N_w` (a generator of `N_w`) and let
`t_w|` be its image in `(ι_w^* N)_η` under the pullback stalk unit (after moving it to the stalk at
`ι_w(η) = w`). Then
`((ι_w)_* div_{ι_w^*N}(t_w|)) z = ((ι_w)_* div(b̄)) z`, `b̄ ∈ K(W_w)^*` the residue class of `b`.

Source: Stacks 0AYC (proof, third paragraph) together with the local description of `div` of a
rational section (Stacks 02SE/02SH; here `rationalSectionOrd_eq_ord_of_generator`).

Natural-language proof:
1. `unit_η` is `O_{X,w}`-semilinear along `ι_w^♯ : O_{X,w} → O_{W_w,η} = K(W_w)`
   (`modulePullbackStalkUnit` is semilinear for `stalkMap`), so `unit_η(t_w) = ι^♯(b) • unit_η(τ_w)`,
   and `ι^♯(b) = b̄` as elements of `K(W_w)` (the residue field map composed with
   `functionFieldIsoResidueField` is `ι^♯` followed by `O_{W_w,η} = K(W_w)`).
2. Let `z'` be the point of `W_w` over `z`. `unit_{z'}(τ)` generates `(ι_w^*N)_{z'}`
   (`span_modulePullbackStalkUnit_eq_top`, since `τ` generates `N_z`), and its image in the generic
   stalk is `unit_η(τ_w)` (`modulePullbackStalkUnit_specializes`, `moduleStalkSpecializes_comp`).
3. Hence `div_{ι^*N}(unit_η t_w) z' = (W_w).ord (b̄) z'` by `rationalSectionOrd_eq_ord_of_generator`
   applied with the generator `unit_{z'}(τ)` and scalar `b̄`.
4. Both sides are coefficients of pushforwards along the closed immersion `ι_w` at `z = ι_w z'`:
   `properPushforward_closedImmersion_apply`.
Edge cases: `w = z` is excluded by `coheight w = 1` only if `coheight z ≠ 1`; if `w = z` the statement
still holds (`z' = η`, both sides `0`). `b` a non-unit is excluded (then `t_w` is not a generator).
The proof follows steps 1–4 above (`residueFieldToPointClosureFunctionField_residue` is step 1's
identification `b̄ = ι^♯(b)`). -/
theorem keyFormula_pullback_generator_coeff (N : X.Modules) [N.IsLineBundle] {w z : X}
    (hwz : w ⤳ z) (hw : Order.coheight w = 1) (τ : N.presheaf.stalk z)
    (hτ : Submodule.span (X.presheaf.stalk z) {τ} = ⊤) (b : (X.presheaf.stalk w)ˣ) :
    haveI : IsLocallyNoetherian (X.pointClosure w) := isLocallyNoetherian_pointClosure w
    AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
      (((Scheme.Modules.pullback (X.pointClosureι w)).obj N).rationalSectionDivisor
        (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N (genericPoint (X.pointClosure w))
          (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N (specializes_of_eq (pointClosureι_genericPoint w))
            ((b : X.presheaf.stalk w) • AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N hwz τ)))) z
      = X.residueUnitCycle w b z := by
  haveI : IsLocallyNoetherian (X.pointClosure w) := isLocallyNoetherian_pointClosure w
  -- z = ι_w z'
  have hz : z ∈ Set.range (X.pointClosureι w).base := by
    rw [MiyaokaMori.PointClosureTransport.range_eq_closure_of_isClosedImmersion (X.pointClosureι w),
      pointClosureι_genericPoint]
    exact specializes_iff_mem_closure.mp hwz
  obtain ⟨z', hz'⟩ := hz
  subst hz'
  have hηz : (genericPoint (X.pointClosure w)) ⤳ z' := (genericPoint_spec (X.pointClosure w)).specializes trivial
  set t' := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N z' τ with ht'
  have hspan : Submodule.span ((X.pointClosure w).presheaf.stalk z') {t'} = ⊤ :=
    Scheme.Modules.span_modulePullbackStalkUnit_eq_top (X.pointClosureι w) N z' τ hτ
  set g : (X.pointClosure w).functionField :=
    ((X.residueUnitOnPointClosure w b : (X.pointClosure w).functionFieldˣ) :
      (X.pointClosure w).functionField) with hg_def
  have hg_eq : g = ((X.pointClosureι w).stalkMap (genericPoint (X.pointClosure w))).hom (X.presheaf.stalkSpecializes
      (specializes_of_eq (pointClosureι_genericPoint w)) (b : X.presheaf.stalk w)) :=
    residueFieldToPointClosureFunctionField_residue w b
  have hj : AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber (X.pointClosure w)
      ((Scheme.Modules.pullback (X.pointClosureι w)).obj N) z' t' =
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N (genericPoint (X.pointClosure w))
        (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N ((X.pointClosureι w).base.hom.map_specializes hηz) τ) :=
    Scheme.Modules.modulePullbackStalkUnit_specializes (X.pointClosureι w) N hηz τ
  have hg : g • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber (X.pointClosure w)
      ((Scheme.Modules.pullback (X.pointClosureι w)).obj N) z' t' =
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N (genericPoint (X.pointClosure w))
        (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N (specializes_of_eq (pointClosureι_genericPoint w))
          ((b : X.presheaf.stalk w) • AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N hwz τ)) := by
    rw [hj, hg_eq, (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N
        (specializes_of_eq (pointClosureι_genericPoint w))).map_smulₛₗ,
      (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N (genericPoint (X.pointClosure w))).map_smulₛₗ,
      MiyaokaMori.RationalSectionOrdRestrict.moduleStalkSpecializes_comp]
  have hu : AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N (genericPoint (X.pointClosure w))
      (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N (specializes_of_eq (pointClosureι_genericPoint w))
        ((b : X.presheaf.stalk w) • AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N hwz τ)) ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := Scheme.Modules.exists_stalk_genericPoint_ne_zero
      ((Scheme.Modules.pullback (X.pointClosureι w)).obj N)
    obtain ⟨c, hc⟩ := Scheme.Modules.exists_smul_toGenericFiber_eq _ z' t' hspan v
    apply hv
    rw [← hc]
    have hg0 : g ≠ 0 := (X.residueUnitOnPointClosure w b).ne_zero
    have h1 := hg
    rw [h0] at h1
    rw [(smul_eq_zero.mp h1).resolve_left hg0, smul_zero]
    rfl
  rw [MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply]
  unfold residueUnitCycle
  rw [MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply]
  exact Scheme.Modules.rationalSectionOrd_eq_ord_of_generator _ z' t' hspan g _ hu hg

end AlgebraicGeometry.Scheme

end
