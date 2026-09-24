import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.FromSpecStalkPrimePoint
import MiyaokaMori.RingTheory.OrderOfVanishing.OrdZeroIffUnit
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierLocalDataPullbackDominant
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.StalkUnitOrder

/-! # Support of a fibre divisor

The support of the fibre divisor `π^*(y)` over a closed point `y` is exactly the set-theoretic
fibre: `π⁻¹(y)` is the union of the closures of the codimension-one points at which the Weil
coefficient of `π^*(y)` is nonzero (the fibre is purely one-dimensional, and every point lies on a
component with positive coefficient).

Proof sketch: take local equations `(U_i, g_i)` of `[y]` (`fiberDivisor_eq_ofLocalData`); then
`π^*[y] = ofLocalData (π⁻¹U_i, π^♮g_i)`, and at `η ∈ π⁻¹U_i` the Weil coefficient is
`ord_η (π^♮ g_i)`. `g_i` is regular on `U_i`: for `x ∈ U_i`, `g_i = a_x ∈ O_{C,x}`, and `a_x` is a
unit iff `x ≠ y` (`ord_x g_i` is the coefficient of `[y]` at `x`, `1_{x=y}`). At `q ∈ π⁻¹U_i`,
`π^♮ g_i` equals `π^♯_q (a_{π q})`.
`⊇`: a nonzero coefficient gives `coheight η = 1` and `π^♯_η(a)` not a unit, so (the stalk map is
local) `a` is not a unit, so `π(η) = y`; and `π⁻¹(y)` is closed.
`⊆`: for `q ∈ π⁻¹(y)`, `b := π^♯_q (a_y) ∈ m_q` is nonzero; take a minimal prime `𝔭` over `(b)`
(Krull's principal ideal theorem gives `ht 𝔭 = 1`); `η := fromSpecStalk q 𝔭` is a generization of
`q` with `coheight η = 1`, the image of `b` in `O_{S,η}` is `π^♯_η(a) ∈ m_η`, so
`ord_η (π^♮ g_i) ≠ 0` (`ord_algebraMap_ne_zero_of_not_isUnit`) and `q ∈ closure {η}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- On a smooth projective curve, a point of coheight `≠ 1` is the generic point:
`height + coheight = dim C = 1`, so `coheight ≠ 1` gives `coheight = 0`, i.e. the point is maximal. -/
theorem SmoothProjectiveCurve.eq_genericPoint_of_coheight_ne_one {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (x : C.toScheme) (hco : Order.coheight x ≠ 1) :
    x = genericPoint C.toScheme := by
  have hsum := Variety.height_add_coheight C.toVariety x
  have hdim : C.toVariety.toScheme.dimension = 1 := by
    have h1 := Variety.dim_spec C.toVariety
    have h2 : topologicalKrullDim C.toScheme = 1 := C.dim_one
    have h3 : ((C.toVariety.dim : ℕ) : WithBot ℕ∞) = 1 := h1.symm.trans h2
    exact_mod_cast h3
  rw [hdim] at hsum
  have hle : Order.coheight x ≤ 1 := by
    calc Order.coheight x ≤ Order.height x + Order.coheight x := le_add_self
      _ = 1 := by exact_mod_cast hsum
  have h0 : Order.coheight x = 0 := by
    rcases Order.le_one_iff.mp hle with h | h
    · exact h
    · exact absurd h hco
  have hmax : IsMax x := Order.coheight_eq_zero.mp h0
  have h1 : x ≤ genericPoint C.toScheme := genericPoint_specializes x
  exact ((AlgebraicGeometry.Scheme.le_iff_specializes.mp (hmax h1)).antisymm
    (AlgebraicGeometry.Scheme.le_iff_specializes.mp h1)).eq

/-- On a curve, a nonzero stalk element `a ∈ O_{C,x}` of vanishing order `0` is a unit: for
`coheight x = 1` by `ord_algebraMap_ne_zero_of_not_isUnit`; otherwise `x` is the generic point,
the stalk is the function field, and every nonzero element is a unit. -/
theorem SmoothProjectiveCurve.isUnit_of_ord_eq_zero {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (x : C.toScheme) {a : C.toScheme.presheaf.stalk x} (ha0 : a ≠ 0)
    (h : C.toScheme.ord (algebraMap (C.toScheme.presheaf.stalk x) C.toScheme.functionField a) x
      = 0) : IsUnit a := by
  by_cases hco : Order.coheight x = 1
  · by_contra hu
    exact AlgebraicGeometry.Scheme.ord_algebraMap_ne_zero_of_not_isUnit hco ha0 hu h
  · have hgen := SmoothProjectiveCurve.eq_genericPoint_of_coheight_ne_one C x hco
    subst hgen
    have hF : IsField (C.toScheme.presheaf.stalk (genericPoint C.toScheme)) :=
      Field.toIsField C.toScheme.functionField
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
    exact isUnit_iff_exists.mpr ⟨b, hb, (mul_comm b a).trans hb⟩

/-- The support of the fibre divisor over a closed point is the set-theoretic fibre. -/
theorem fiberDivisor_support {k : Type u} [Field k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    π.base ⁻¹' {y}
      = ⋃ η ∈ {η : S.toScheme | ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) η ≠ 0}, closure {η} := by
  classical
  have hdom : AlgebraicGeometry.IsDominant π := ⟨hπ.surj.denseRange⟩
  obtain ⟨ι, U, g, hUg, hDg, hfib⟩ := fiberDivisor_eq_ofLocalData π hπ y
  have hUg' := CartierDivisor.isLocalData_pullback_of_isDominant (X := S.toVariety)
    (Y := C.toVariety) π U g hUg
  -- the Weil coefficient is the vanishing order of the pulled-back local equation
  have hcoeff : ∀ i (η : S.toScheme), η ∈ π ⁻¹ᵁ U i →
      ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) η =
        S.toScheme.ord ((Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap π).hom.toMonoidHom (g i) :
          (S.toScheme.functionField)ˣ) : S.toScheme.functionField) η := by
    intro i η hη
    rw [hfib]
    exact CartierDivisor.weilCycle_ofLocalData S.toVariety _ _ hUg' i η hη
  -- `g_i` is regular on `U_i`
  have hreg : ∀ i (x : C.toScheme), x ∈ U i → ∃ a : C.toScheme.presheaf.stalk x,
      algebraMap (C.toScheme.presheaf.stalk x) C.toScheme.functionField a =
        (g i : C.toScheme.functionField) :=
    fun i x hx => SmoothProjectiveCurve.localData_mem_range_of_effective
      (Divisor.ofPoint_effective y) U g hUg hDg i x hx
  -- `ord_x g_i` is the coefficient of `[y]` at `x`
  have hordg : ∀ i (x : C.toScheme), x ∈ U i →
      C.toScheme.ord (g i : C.toScheme.functionField) x = if x = y then 1 else 0 := by
    intro i x hx
    rw [← CartierDivisor.weilCycle_ofLocalData C.toVariety U g hUg i x hx, ← hDg]
    exact Divisor.ofPoint_weilCycle y hy x
  -- `π^♮ g_i` at `q` equals `π^♯_q a`
  have hpull : ∀ i (q : S.toScheme) (a : C.toScheme.presheaf.stalk (π.base q)),
      algebraMap (C.toScheme.presheaf.stalk (π.base q)) C.toScheme.functionField a =
        (g i : C.toScheme.functionField) →
      ((Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap π).hom.toMonoidHom (g i) :
          (S.toScheme.functionField)ˣ) : S.toScheme.functionField) =
        algebraMap (S.toScheme.presheaf.stalk q) S.toScheme.functionField (π.stalkMap q a) := by
    intro i q a ha
    rw [Units.coe_map]
    change (AlgebraicGeometry.Scheme.dominantFunctionFieldMap π) (g i : C.toScheme.functionField) = _
    rw [← ha]
    exact AlgebraicGeometry.Scheme.dominantFunctionFieldMap_algebraMap π q a
  ext q
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
    exists_prop]
  constructor
  · -- ⊆: q ∈ π⁻¹(y)
    intro hq
    obtain ⟨i, hyi⟩ : ∃ i, y ∈ U i := by
      have : y ∈ (⨆ i, U i : C.toScheme.Opens) := by rw [hUg.1]; trivial
      exact TopologicalSpace.Opens.mem_iSup.mp this
    have hqi : π.base q ∈ U i := hq ▸ hyi
    obtain ⟨a, ha⟩ := hreg i (π.base q) hqi
    have ha_nonunit : ¬ IsUnit a := by
      intro hu
      have h0 := AlgebraicGeometry.Divisors.StalkUnitOrder.ord_algebraMap_unit (Y := C.toScheme) (π.base q)
        hu.unit
      rw [IsUnit.unit_spec, ha, hordg i (π.base q) hqi, if_pos hq] at h0
      exact one_ne_zero h0
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact (g i).ne_zero (by rw [← ha, map_zero])
    set b := π.stalkMap q a with hb
    have hb_nonunit : ¬ IsUnit b := fun h =>
      ha_nonunit ((isUnit_map_iff (π.stalkMap q).hom a).mp h)
    have hb0 : b ≠ 0 := by
      intro h0
      apply ha0
      apply AlgebraicGeometry.Scheme.dominant_stalkMap_injective π q
      rw [map_zero]
      exact h0
    have hbm : Ideal.span {b} ≤ IsLocalRing.maximalIdeal (S.toScheme.presheaf.stalk q) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalRing.mem_maximalIdeal b).mpr (mem_nonunits_iff.mpr hb_nonunit)
    obtain ⟨𝔭, h𝔭min, -⟩ := Ideal.exists_minimalPrimes_le hbm
    have h𝔭prime : 𝔭.IsPrime := h𝔭min.1.1
    have hb𝔭 : b ∈ 𝔭 := h𝔭min.1.2 (Ideal.mem_span_singleton_self b)
    have hht : 𝔭.height = 1 := by
      apply le_antisymm
      · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {b}) 𝔭 h𝔭min
      · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
        intro hbot
        rw [hbot] at hb𝔭
        exact hb0 ((Submodule.mem_bot _).mp hb𝔭)
    let P : AlgebraicGeometry.Spec (S.toScheme.presheaf.stalk q) := ⟨𝔭, h𝔭prime⟩
    have hηq : S.toScheme.fromSpecStalk q P ⤳ q :=
      AlgebraicGeometry.Scheme.fromSpecStalk_apply_specializes q P
    have hcoh : Order.coheight (S.toScheme.fromSpecStalk q P) = 1 := by
      rw [AlgebraicGeometry.Scheme.coheight_fromSpecStalk_apply q P]
      exact hht
    have hπη : π.base (S.toScheme.fromSpecStalk q P) ⤳ π.base q := hηq.map π.continuous
    have hηi : S.toScheme.fromSpecStalk q P ∈ π ⁻¹ᵁ U i := hπη.mem_open (U i).isOpen hqi
    refine ⟨S.toScheme.fromSpecStalk q P, ?_, hηq.mem_closure⟩
    rw [hcoeff i _ hηi]
    have ha' : algebraMap (C.toScheme.presheaf.stalk (π.base (S.toScheme.fromSpecStalk q P)))
        C.toScheme.functionField (C.toScheme.presheaf.stalkSpecializes hπη a) =
        (g i : C.toScheme.functionField) := by
      rw [← ha]
      simp only [RingHom.algebraMap_toAlgebra]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    have hpullη := hpull i _ (C.toScheme.presheaf.stalkSpecializes hπη a) ha'
    have hnat : π.stalkMap (S.toScheme.fromSpecStalk q P)
        (C.toScheme.presheaf.stalkSpecializes hπη a) =
        S.toScheme.presheaf.stalkSpecializes hηq b :=
      AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap_apply π _ q hηq a
    rw [hpullη, hnat]
    apply AlgebraicGeometry.Scheme.ord_algebraMap_ne_zero_of_not_isUnit hcoh
    · intro h0
      rw [hnat, h0, map_zero] at hpullη
      exact Units.ne_zero _ hpullη
    · have hmem := (AlgebraicGeometry.Scheme.stalkSpecializes_mem_maximalIdeal_iff q P b).mpr hb𝔭
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  · -- ⊇: `q ∈ closure {η}` with nonzero coefficient at `η`
    rintro ⟨η, hη, hqη⟩
    have hclosed : IsClosed (π.base ⁻¹' {y}) := hy.preimage π.continuous
    suffices hηy : π.base η = y by
      have hsub : closure ({η} : Set S.toScheme) ⊆ π.base ⁻¹' {y} :=
        hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηy)
      exact hsub hqη
    obtain ⟨i, hηi⟩ : ∃ i, η ∈ π ⁻¹ᵁ U i := by
      have : η ∈ (⨆ i, π ⁻¹ᵁ U i : S.toScheme.Opens) := by rw [hUg'.1]; trivial
      exact TopologicalSpace.Opens.mem_iSup.mp this
    rw [hcoeff i η hηi] at hη
    obtain ⟨a, ha⟩ := hreg i (π.base η) hηi
    rw [hpull i η a ha] at hη
    have hc_nonunit : ¬ IsUnit (π.stalkMap η a) := by
      intro hu
      apply hη
      have h0 := AlgebraicGeometry.Divisors.StalkUnitOrder.ord_algebraMap_unit (Y := S.toScheme) η hu.unit
      rwa [IsUnit.unit_spec] at h0
    have ha_nonunit : ¬ IsUnit a := fun hu => hc_nonunit (hu.map (π.stalkMap η).hom)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact (g i).ne_zero (by rw [← ha, map_zero])
    by_contra hne
    apply ha_nonunit
    have hord0 : C.toScheme.ord (algebraMap (C.toScheme.presheaf.stalk (π.base η))
        C.toScheme.functionField a) (π.base η) = 0 := by
      rw [ha, hordg i _ hηi, if_neg hne]
    exact SmoothProjectiveCurve.isUnit_of_ord_eq_zero C (π.base η) ha0 hord0

end
