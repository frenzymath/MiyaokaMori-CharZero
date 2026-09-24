import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.Paper.S4Completion.GeneralFiberDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleInterEqIntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassLemmas
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks0ha1
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackDegreeOnCurve

/-! # Degree of a line bundle on a fibre isomorphic to `P¹`

If a fibre of `π : S → C` is isomorphic to `P¹`, the fibre degree `fiberDegree π hπ A y = A · [π^*(y)]`
equals the degree of the pullback of the line bundle `A` to `P¹`. This is the step "the same
observation preserves the degree bound" in the proof of Corollary 4.3 of the
paper.

References: Fulton, *Intersection Theory*, Example 2.4.2 and Proposition 2.5(c) (the intersection
number of a divisor with a curve is the degree of the restricted line bundle).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The inclusion of the fibre over a closed point is a closed immersion: if `y` is closed then
`Y.fromSpecResidueField y` is a closed immersion (`isClosed_singleton_iff_isClosedImmersion`),
closed immersions are stable under base change, and `fiberι = pullback.fst`. -/
theorem AlgebraicGeometry.Scheme.Hom.isClosedImmersion_fiberι_of_isClosed
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (y : Y) (hy : IsClosed ({y} : Set Y)) :
    AlgebraicGeometry.IsClosedImmersion (f.fiberι y) := by
  have h1 : AlgebraicGeometry.IsClosedImmersion (Y.fromSpecResidueField y) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hy
  have h2 : AlgebraicGeometry.IsClosedImmersion
      (CategoryTheory.Limits.pullback.fst f (Y.fromSpecResidueField y)) := inferInstance
  exact h2

/-- The integral curve in `S` obtained from a fibre isomorphism `e : π.fiber y ≅ P¹`: the carrier
is `P¹` and the closed immersion is `e.inv ≫ π.fiberι y`. It is a closed immersion since `e.inv` is
an isomorphism and `fiberι` is a closed immersion (`y` closed); `P¹` is integral and
one-dimensional, and a closed immersion followed by a proper morphism is proper. -/
def fiberIsoIntegralCurve {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (e : π.fiber y ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) :
    IntegralCurve k S.toScheme :=
  haveI : AlgebraicGeometry.IsClosedImmersion (π.fiberι y) :=
    AlgebraicGeometry.Scheme.Hom.isClosedImmersion_fiberι_of_isClosed π y hy
  haveI : AlgebraicGeometry.IsClosedImmersion (e.inv ≫ π.fiberι y) := inferInstance
  haveI : AlgebraicGeometry.IsProper
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    SmoothProjectiveVariety.isProper_structureMorphism S.toSmoothProjectiveVariety
  haveI : AlgebraicGeometry.IsIntegral (ProjectiveLine.asSmoothProjectiveCurve k).toScheme :=
    SmoothProjectiveCurve.isIntegral _
  { carrier := (ProjectiveLine.asSmoothProjectiveCurve k).toScheme
    ι := e.inv ≫ π.fiberι y
    dim_eq_one := (ProjectiveLine.asSmoothProjectiveCurve k).dim_one }

/-- A non-generic point of a one-dimensional integral scheme is closed (the same proof as
`isClosed_singleton_of_ne_genericPoint_of_dim_one` in `DegreeZeroIffConstant.lean`). -/
theorem isClosed_singleton_of_ne_genericPoint_of_krullDim_one
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (hdim : topologicalKrullDim X = 1) {x : X} (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  apply AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one hdim.le x
  let _ : PartialOrder X := specializationOrder X
  have hk : Order.krullDim X = 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hle : Order.coheight x ≤ 1 := by
    have h := Order.coheight_le_krullDim x
    rw [hk] at h
    exact WithBot.coe_le_coe.mp h
  have hxη : x < genericPoint X := by
    refine lt_of_le_of_ne ?_ hx
    exact AlgebraicGeometry.Scheme.le_iff_specializes.mpr
      ((genericPoint_spec X).specializes (Set.mem_univ x))
  have hge : Order.coheight (genericPoint X) + 1 ≤ Order.coheight x :=
    Order.coheight_add_one_le hxη
  exact le_antisymm hle (le_trans le_add_self hge)

section FiberIsoCurve

variable {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (e : π.fiber y ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme)

/-- Every point of the fibre curve maps to `y`. -/
theorem fiberIsoIntegralCurve_π_apply (q : (fiberIsoIntegralCurve π y hy e).carrier) :
    π.base ((fiberIsoIntegralCurve π y hy e).ι.base q) = y := by
  have h : (π.fiberι y).base (e.inv.base q) ∈ Set.range (π.fiberι y).base := Set.mem_range_self _
  have hr : Set.range (π.fiberι y).base = π.base ⁻¹' {y} := π.range_fiberι y
  rw [hr] at h
  exact h

/-- The image of the fibre curve is exactly `π⁻¹{y}`. -/
theorem fiberIsoIntegralCurve_exists_of_π_eq (p : S.toScheme) (hp : π.base p = y) :
    ∃ q : (fiberIsoIntegralCurve π y hy e).carrier, (fiberIsoIntegralCurve π y hy e).ι.base q = p := by
  have hp' : p ∈ Set.range (π.fiberι y).base := by
    rw [π.range_fiberι y]
    exact hp
  obtain ⟨z, hz⟩ := hp'
  refine ⟨e.hom.base z, ?_⟩
  change (π.fiberι y).base (e.inv.base (e.hom.base z)) = p
  rw [← hz]
  congr 1
  change (e.hom ≫ e.inv).base z = z
  rw [e.hom_inv_id]
  rfl

/-- A non-generic point of the fibre curve is a closed point of `S`. -/
theorem fiberIsoIntegralCurve_isClosed_of_ne (q : (fiberIsoIntegralCurve π y hy e).carrier)
    (hq : q ≠ genericPoint (fiberIsoIntegralCurve π y hy e).carrier) :
    IsClosed ({(fiberIsoIntegralCurve π y hy e).ι.base q} : Set S.toScheme) := by
  have hcl : IsClosed ({q} : Set (fiberIsoIntegralCurve π y hy e).carrier) :=
    isClosed_singleton_of_ne_genericPoint_of_krullDim_one
      (fiberIsoIntegralCurve π y hy e).dim_eq_one hq
  have := (fiberIsoIntegralCurve π y hy e).ι.isClosedEmbedding.isClosedMap _ hcl
  rwa [Set.image_singleton] at this

end FiberIsoCurve

/-- A closed point of a scheme is minimal for the specialisation order (`x ≤ y ↔ y ⤳ x`), so it
has height `0`. -/
theorem AlgebraicGeometry.Scheme.height_eq_zero_of_isClosed_singleton {X : AlgebraicGeometry.Scheme.{u}}
    {p : X} (hp : IsClosed ({p} : Set X)) : Order.height p = 0 := by
  apply Order.height_eq_zero.mpr
  intro x hx
  have hsp : p ⤳ x := AlgebraicGeometry.Scheme.le_iff_specializes.mp hx
  have hxp : x ∈ closure ({p} : Set X) := specializes_iff_mem_closure.mp hsp
  rw [hp.closure_eq] at hxp
  rw [Set.mem_singleton_iff.mp hxp]

/-- A cycle in `Z_1` vanishes at a closed point: a closed point `p` has height `0 ≠ 1`. -/
theorem OneCycle.apply_eq_zero_of_isClosed {k : Type u} [Field k] {X : Variety k}
    (Z : OneCycle X) (p : X.toScheme) (hp : IsClosed ({p} : Set X.toScheme)) :
    (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) p = 0 := by
  by_contra hne
  have hht : Order.height p = ((1 : ℕ) : ℕ∞) := Z.2 p hne
  rw [AlgebraicGeometry.Scheme.height_eq_zero_of_isClosed_singleton hp] at hht
  exact absurd hht (by norm_num)

/-- Comparison of the order of vanishing of an element of the stalk with `Ring.ord`: for `a ≠ 0`
and `coheight x = 1`, `ord_x(algebraMap a) = n ↔ Ring.ord (O_{X,x}) a = n` (`Scheme.ord_eq_iff`,
`Ring.ordFrac_eq_ord`, `Ring.ordMonoidWithZeroHom_eq_ord`). -/
theorem AlgebraicGeometry.Scheme.ord_algebraMap_eq_natCast_iff {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1) {a : X.presheaf.stalk x} (ha : a ≠ 0) (n : ℕ) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = (n : ℤ) ↔
      Ring.ord (X.presheaf.stalk x) a = (n : ℕ∞) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have ha' : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).mpr ha
  rw [AlgebraicGeometry.Scheme.ord_eq_iff hx ha']
  change Ring.ordFrac (X.presheaf.stalk x) (algebraMap (X.presheaf.stalk x) X.functionField a) = _ ↔ _
  rw [Ring.ordFrac_eq_ord _ ha, Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha)]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))
  rw [← hm]
  simp only [ENat.recTopCoe_natCast]
  constructor
  · intro h
    have h1 := Multiplicative.ofAdd.injective (WithZero.coe_inj.mp h)
    exact_mod_cast h1
  · intro h
    have : m = n := by exact_mod_cast h
    subst this
    rfl

/-- `Ring.ord R a = 1` iff `R/(a)` is a simple module iff `(a)` is maximal
(`Module.length_eq_one_iff`, `isSimpleModule_iff_isCoatom`, `Ideal.isMaximal_def`). -/
theorem Ring.ord_eq_one_iff_isMaximal {R : Type*} [CommRing R] (a : R) :
    Ring.ord R a = 1 ↔ (Ideal.span {a}).IsMaximal := by
  rw [Ideal.isMaximal_def]
  exact Module.length_eq_one_iff.trans isSimpleModule_iff_isCoatom

/-- Pulling back a family of local equations along a dominant morphism gives a family of local
equations (alias of `CartierDivisor.IsLocalData.pullback`; the surjectivity hypothesis `_hf` is not
needed and is kept only for the call sites). -/
theorem CartierDivisor.isLocalData_pullback {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsDominant f] (_hf : Function.Surjective f.base)
    {ι : Type u} (U : ι → Y.toScheme.Opens) (g : ι → (Y.toScheme.functionField)ˣ)
    (hUg : CartierDivisor.IsLocalData U g) :
    CartierDivisor.IsLocalData (fun i => f ⁻¹ᵁ U i)
      (fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i)) :=
  CartierDivisor.IsLocalData.pullback f hUg

open Classical in
/-- The Weil coefficient of the fibre divisor at `p` is given by a local equation `g` of `y`:
there is `g ∈ K(C)ˣ` with `ord_{π p} g = [π p = y]` (by `Divisor.ofPoint_weilCycle`) such that the
coefficient of `[π^*(y)]` at `p` is `ord_p(π^♮ g)` (`weilCycle_ofLocalData` and
`isLocalData_pullback`). -/
theorem fiberDivisor_weilCycle_exists_localEquation {k : Type u} [Field k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) (p : S.toScheme) :
    ∃ g : (C.toScheme.functionField)ˣ,
      C.toScheme.ord (g : C.toScheme.functionField) (π.base p) = (if π.base p = y then 1 else 0) ∧
      ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) p =
        S.toScheme.ord ((Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap π).hom.toMonoidHom g :
          (S.toScheme.functionField)ˣ) : S.toScheme.functionField) p := by
  have : AlgebraicGeometry.IsDominant π := ⟨hπ.surj.denseRange⟩
  obtain ⟨d, key, hfd⟩ : ∃ d : (Σ ι : Type u, (ι → C.toScheme.Opens) × (ι → (C.toScheme.functionField)ˣ)),
      (CartierDivisor.IsLocalData (X := C.toVariety) d.2.1 d.2.2 ∧
        Divisor.ofPoint y = CartierDivisor.ofLocalData (X := C.toVariety) d.2.1 d.2.2) ∧
      fiberDivisor π hπ y = CartierDivisor.ofLocalData (fun i : d.1 => π ⁻¹ᵁ d.2.1 i)
        (fun i : d.1 => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap π).hom.toMonoidHom (d.2.2 i)) := by
    obtain ⟨ι, U, g, h1, h2⟩ := cartierDivisor_exists_localData C.toVariety (Divisor.ofPoint y)
    refine ⟨⟨ι, U, g⟩, ⟨h1, h2⟩, ?_⟩
    show CartierDivisor.pullback π hπ.surj (Divisor.ofPoint y) = _
    rw [h2]
    exact CartierDivisor.pullback_ofLocalData (X := S.toVariety) (Y := C.toVariety) π hπ.surj h1
  have hcov : π.base p ∈ (⨆ i, d.2.1 i : C.toScheme.Opens) := by rw [key.1.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  refine ⟨d.2.2 i, ?_, ?_⟩
  · rw [← CartierDivisor.weilCycle_ofLocalData C.toVariety _ _ key.1 i (π.base p) hi, ← key.2]
    exact Divisor.ofPoint_weilCycle y hy (π.base p)
  · have h2 := CartierDivisor.weilCycle_ofLocalData S.toVariety (fun i : d.1 => π ⁻¹ᵁ d.2.1 i)
      (fun i : d.1 => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap π).hom.toMonoidHom (d.2.2 i))
      (CartierDivisor.isLocalData_pullback (X := S.toVariety) (Y := C.toVariety) π hπ.surj d.2.1 d.2.2 key.1) i p
      (show p ∈ π ⁻¹ᵁ d.2.1 i from hi)
    rw [hfd]
    exact h2

/-- On a smooth projective curve, a rational function `g` with `ord_x g = 0` is a unit of the stalk
at `x`: if `coheight x = 1` the stalk is a DVR, `g` and `g⁻¹` both have valuation `0`, hence lie in
the stalk (`valuation_nonneg_iff`), and their product is `1` (the `algebraMap` is injective); if
`coheight x ≠ 1` then `x` is the generic point and the stalk is the function field. (The same case
distinction as in `SmoothProjectiveCurve.localData_mem_range_of_effective`.) -/
theorem SmoothProjectiveCurve.exists_unit_of_ord_eq_zero {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (x : C.toScheme) (g : (C.toScheme.functionField)ˣ)
    (hg : C.toScheme.ord (g : C.toScheme.functionField) x = 0) :
    ∃ v : (C.toScheme.presheaf.stalk x)ˣ,
      algebraMap (C.toScheme.presheaf.stalk x) C.toScheme.functionField
        (v : C.toScheme.presheaf.stalk x) = (g : C.toScheme.functionField) := by
  by_cases hco : Order.coheight x = 1
  · have : IsDiscreteValuationRing (C.toScheme.presheaf.stalk x) :=
      SmoothProjectiveCurve.isDiscreteValuationRing_stalk C x hco
    have hval : AlgebraicGeometry.Divisors.CurveStalkValuation.valuation C.toScheme x hco
        (g : C.toScheme.functionField) = 0 := by
      rw [AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_of_ne_zero C.toScheme x hco g.ne_zero, hg]
      rfl
    have hval' : AlgebraicGeometry.Divisors.CurveStalkValuation.valuation C.toScheme x hco
        ((g : C.toScheme.functionField)⁻¹) = 0 := by
      rw [AddValuation.map_inv, hval, neg_zero]
    obtain ⟨a, ha⟩ := (AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_nonneg_iff C.toScheme x hco _).mp hval.ge
    obtain ⟨b, hb⟩ := (AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_nonneg_iff C.toScheme x hco _).mp hval'.ge
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (C.toScheme.presheaf.stalk x) C.toScheme.functionField
      rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ g.ne_zero]
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩
  · have hgen : x = genericPoint C.toScheme := by
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
    subst hgen
    refine ⟨g, ?_⟩
    change (C.toScheme.presheaf.stalkSpecializes _).hom (g : C.toScheme.functionField) = _
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl

/-- (a) The Weil coefficient of the fibre divisor vanishes outside the fibre: if `π p ≠ y`, a
local equation `g` of `y` is a unit of the stalk at `π p` (`exists_unit_of_ord_eq_zero`), so
`π^♮ g = algebraMap (π^♯ v)` is a unit of the stalk at `p` and `ord_p = 0`
(`ord_algebraMap_unit`). -/
theorem fiberDivisor_weilCycle_eq_zero_of_ne {k : Type u} [Field k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) (p : S.toScheme) (hp : π.base p ≠ y) :
    ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) p = 0 := by
  have : AlgebraicGeometry.IsDominant π := ⟨hπ.surj.denseRange⟩
  obtain ⟨g, hg, hw⟩ := fiberDivisor_weilCycle_exists_localEquation π hπ y hy p
  rw [if_neg hp] at hg
  obtain ⟨v, hv⟩ := SmoothProjectiveCurve.exists_unit_of_ord_eq_zero C (π.base p) g hg
  rw [hw, Units.coe_map, ← hv]
  exact (congrArg (fun z => S.toScheme.ord z p)
    (AlgebraicGeometry.Scheme.dominantFunctionFieldMap_algebraMap π p v)).trans
    (AlgebraicGeometry.Divisors.StalkUnitOrder.ord_algebraMap_unit p
      (Units.map (π.stalkMap p).hom.toMonoidHom v))

/-- **The key computation**: the pullback of a uniformiser has order of vanishing `1` at the
generic point `ξ` of the fibre. If `g ∈ K(C)ˣ` satisfies `ord_y g = 1`, then `ord_ξ(π^♮ g) = 1`,
where `ξ = ι(η_{P¹})` is the generic point of the fibre curve.

Proof (Fulton §1.5; [Stacks, 0HA1]; Lemma 5.1 of the paper):
1. `coheight ξ = 1`: `[F] ∈ Z_1` gives `height ξ = 1` (`fundamentalClass_coe_eq_single` and the
   membership condition of `Z_1`), and `height + coheight = dim S = 2`
   (`Variety.height_add_coheight`).
2. `y` closed gives `coheight y = 1` (`coheight_eq_one_of_isClosed`), so `O_{C,y}` is a DVR;
   `ord_y g = 1 ≥ 0` gives `g = algebraMap t` with `t ∈ O_{C,y}` (`valuation_nonneg_iff`), and
   `Ring.ord t = length(O_{C,y}/(t)) = 1` (`ord_algebraMap_eq_natCast_iff`), hence `(t)` is maximal,
   `(t) = m_y` (`Ring.ord_eq_one_iff_isMaximal`, `IsLocalRing.eq_maximalIdeal`).
3. `π^♮ g = algebraMap (π^♯_ξ t)` (`dominantFunctionFieldMap_algebraMap`), `s := π^♯_ξ t ≠ 0`
   (`dominant_stalkMap_injective`), and `ord_ξ(algebraMap s) = 1 ⇔ Ring.ord s = 1 ⇔ (s)` maximal.
4. `O_{S,ξ}/(s) = O_{S,ξ}/m_y·O_{S,ξ} ≃+* O_{F,ξ'}` ([Stacks, 0HA1], `Scheme.Hom.fiber_stalk_iso`,
   `ξ' = π.asFiber ξ`); `ξ'` is the generic point of the fibre (`fiberι` injective,
   `genericPoint_eq_of_isOpenImmersion e.inv`), the fibre is integral (via `e`), and the stalk at its
   generic point is its function field, a field; hence `O_{S,ξ}/(s)` is a field and `(s)` is maximal
   (`Ideal.Quotient.maximal_of_isField`). -/
theorem fiberIsoIntegralCurve_ord_pullback_eq_one {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (e : π.fiber y ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme)
    (g : (C.toScheme.functionField)ˣ) (hg : C.toScheme.ord (g : C.toScheme.functionField) y = 1) :
    haveI : AlgebraicGeometry.IsDominant π := ⟨hπ.surj.denseRange⟩
    S.toScheme.ord (AlgebraicGeometry.Scheme.dominantFunctionFieldMap π (g : C.toScheme.functionField))
      ((fiberIsoIntegralCurve π y hy e).ι.base
        (genericPoint (fiberIsoIntegralCurve π y hy e).carrier)) = 1 := by
  classical
  have hdom : AlgebraicGeometry.IsDominant π := ⟨hπ.surj.denseRange⟩
  have hP : AlgebraicGeometry.IsIntegral (ProjectiveLine.asSmoothProjectiveCurve k).toScheme :=
    SmoothProjectiveCurve.isIntegral _
  have hne : Nonempty (π.fiber y) := ⟨e.inv.base (genericPoint _)⟩
  have hFint : AlgebraicGeometry.IsIntegral (π.fiber y) :=
    AlgebraicGeometry.isIntegral_of_isOpenImmersion e.hom
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : S.toScheme, ξ = (fiberIsoIntegralCurve π y hy e).ι.base
      (genericPoint (fiberIsoIntegralCurve π y hy e).carrier) := ⟨_, rfl⟩
  rw [← hξdef]
  have hξy : π.base ξ = y := by rw [hξdef]; exact fiberIsoIntegralCurve_π_apply π y hy e _
  -- step 1: coheight ξ = 1
  have hht : Order.height ξ = ((1 : ℕ) : ℕ∞) := by
    have hmem := (fiberIsoIntegralCurve π y hy e).fundamentalClass.2
    refine hmem ξ ?_
    rw [IntegralCurve.fundamentalClass_coe_eq_single, ← hξdef,
      Function.locallyFinsuppWithin.single_apply, if_pos rfl]
    exact one_ne_zero
  have hco : Order.coheight ξ = 1 := by
    have h := Variety.height_add_coheight S.toVariety ξ
    have hdimS : S.toVariety.toScheme.dimension = 2 := by
      rw [← Variety.dim_eq_scheme_dimension, S.dim_eq_two]
    rw [hdimS, hht] at h
    have h2 : ((1 : ℕ) : ℕ∞) + Order.coheight ξ = ((1 : ℕ) : ℕ∞) + 1 := by
      rw [h]
      norm_num
    exact (WithTop.add_left_inj (ENat.natCast_ne_top 1)).mp h2
  -- step 2: the local equation g comes from a uniformizer t of O_{C,y}
  have hcoy : Order.coheight y = 1 := SmoothProjectiveCurve.coheight_eq_one_of_isClosed C y hy
  have hDVR : IsDiscreteValuationRing (C.toScheme.presheaf.stalk y) :=
    SmoothProjectiveCurve.isDiscreteValuationRing_stalk C y hcoy
  have hval : 0 ≤ AlgebraicGeometry.Divisors.CurveStalkValuation.valuation C.toScheme y hcoy
      (g : C.toScheme.functionField) := by
    rw [AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_of_ne_zero C.toScheme y hcoy g.ne_zero, hg]
    exact zero_le_one
  obtain ⟨t, ht⟩ := (AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_nonneg_iff C.toScheme y hcoy _).mp hval
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact g.ne_zero (by rw [← ht, map_zero])
  have hordt : Ring.ord (C.toScheme.presheaf.stalk y) t = 1 := by
    have h1 := (AlgebraicGeometry.Scheme.ord_algebraMap_eq_natCast_iff hcoy ht0 1).mp
      (by rw [ht]; exact hg)
    exact_mod_cast h1
  have hmax : Ideal.span {t} = IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y) :=
    IsLocalRing.eq_maximalIdeal ((Ring.ord_eq_one_iff_isMaximal t).mp hordt)
  -- step 3: pull back to ξ
  subst hξy
  have hs0 : π.stalkMap ξ t ≠ 0 := by
    intro h
    exact ht0 (AlgebraicGeometry.Scheme.dominant_stalkMap_injective π ξ (by rw [h, map_zero]))
  rw [← ht]
  refine (congrArg (fun z => S.toScheme.ord z ξ)
    (AlgebraicGeometry.Scheme.dominantFunctionFieldMap_algebraMap π ξ t)).trans ?_
  change _ = ((1 : ℕ) : ℤ)
  rw [AlgebraicGeometry.Scheme.ord_algebraMap_eq_natCast_iff hco hs0 1, Nat.cast_one,
    Ring.ord_eq_one_iff_isMaximal]
  -- step 4: O_{S,ξ}/(s) is the stalk of the fibre at its generic point, a field
  have hI : Ideal.map (π.stalkMap ξ).hom
      (IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk (π.base ξ))) =
      Ideal.span {π.stalkMap ξ t} := by
    rw [← hmax, Ideal.map_span, Set.image_singleton]
  obtain ⟨e0⟩ := AlgebraicGeometry.Scheme.Hom.fiber_stalk_iso π ξ
  have hgen : π.asFiber ξ = genericPoint (π.fiber (π.base ξ)) := by
    apply (π.fiberι (π.base ξ)).isEmbedding.injective
    rw [AlgebraicGeometry.Scheme.Hom.fiberι_asFiber]
    have h1 : (π.fiberι (π.base ξ)).base (e.inv.base (genericPoint _)) = ξ := hξdef.symm
    rw [← AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion e.inv]
    exact h1.symm
  have hfield : IsField ((π.fiber (π.base ξ)).presheaf.stalk (π.asFiber ξ)) := by
    rw [hgen]
    exact Field.toIsField (π.fiber (π.base ξ)).functionField
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField hfield ((Ideal.quotEquivOfEq hI).symm.trans e0.symm).toMulEquiv

/-- The Weil coefficient of the fibre divisor at the generic point `ξ = ι(η_{P¹})` of the fibre is
`1`: take a local equation `g` of `y` (`fiberDivisor_weilCycle_exists_localEquation`: `ord_y g = 1`
and the coefficient is `ord_ξ(π^♮ g)`) and apply `fiberIsoIntegralCurve_ord_pullback_eq_one`. -/
theorem fiberIsoIntegralCurve_weilCycle_generic {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (e : π.fiber y ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) :
    ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ)
      ((fiberIsoIntegralCurve π y hy e).ι.base
        (genericPoint (fiberIsoIntegralCurve π y hy e).carrier)) = 1 := by
  have : AlgebraicGeometry.IsDominant π := ⟨hπ.surj.denseRange⟩
  obtain ⟨g, hg, hw⟩ := fiberDivisor_weilCycle_exists_localEquation π hπ y hy
    ((fiberIsoIntegralCurve π y hy e).ι.base (genericPoint (fiberIsoIntegralCurve π y hy e).carrier))
  rw [fiberIsoIntegralCurve_π_apply π y hy e, if_pos rfl] at hg
  rw [hw, Units.coe_map]
  exact fiberIsoIntegralCurve_ord_pullback_eq_one π hπ y hy e g hg

/-- The fibre cycle is the fundamental class of the fibre curve: `fiberCycle π hπ y = [F]` with
`F = fiberIsoIntegralCurve π y hy e`.

Proof (Fulton §1.5, §2.1; Lemma 5.1 of the paper): `fiberCycle` is the Weil cycle
of the Cartier divisor `fiberDivisor π hπ y = π^*(Divisor.ofPoint y)`, and `[F]` is the cycle with
value `1` at `ξ := ι(generic point of P¹)` and `0` elsewhere
(`ClosedSubvariety.fundamentalClass_eq_single`). Compare pointwise:
(a) `π p ≠ y`: the local equation `π^♮ g` of `π^*(y)` (`g` a local equation of `y`) is a unit of
the stalk at `p` (`g` is a unit at `π p ≠ y`, by `Divisor.ofPoint_weilCycle` and the DVR property),
so `ord_p = 0`; and `p ≠ ξ` since `π ξ = y`.
(b) `π p = y`, `p ≠ ξ`: `p` is a closed point of `S` (a non-generic point of the fibre `≅ P¹` is
closed, and `fiberι` is a closed embedding), so `height p = 0 ≠ 1` and a cycle in `Z_1` vanishes at
`p`; so does `single ξ 1`.
(c) `p = ξ`: `ord_ξ(π^♮ t) = length(O_{S,ξ}/(π^♯ t)) = 1`, because
`O_{S,ξ}/(π^♯ t) ≅ O_{F,ξ}` ([Stacks, 0HA1], `fiber_stalk_iso`; `t` a uniformiser of `O_{C,y}`,
`(t) = m_y`) is the stalk of the fibre at its generic point, i.e. the function field of the fibre,
a field, hence a simple module; and `coheight ξ = 1` (`height ξ + coheight ξ = 2`, `height ξ = 1`). -/
theorem fiberCycle_eq_fundamentalClass_of_fiber_iso {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (e : π.fiber y ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) :
    fiberCycle π hπ y = (fiberIsoIntegralCurve π y hy e).fundamentalClass := by
  classical
  apply Subtype.ext
  rw [IntegralCurve.fundamentalClass_coe_eq_single]
  change ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) = _
  apply DFunLike.ext
  intro p
  rw [Function.locallyFinsuppWithin.single_apply]
  by_cases hp : π.base p = y
  · obtain ⟨q, rfl⟩ := fiberIsoIntegralCurve_exists_of_π_eq π y hy e p hp
    by_cases hq : q = genericPoint (fiberIsoIntegralCurve π y hy e).carrier
    · subst hq
      rw [if_pos rfl]
      exact fiberIsoIntegralCurve_weilCycle_generic π hπ y hy e
    · rw [if_neg]
      · exact OneCycle.apply_eq_zero_of_isClosed (fiberCycle π hπ y) _
          (fiberIsoIntegralCurve_isClosed_of_ne π y hy e q hq)
      · intro h
        exact hq ((fiberIsoIntegralCurve π y hy e).ι.isClosedEmbedding.injective h)
  · rw [if_neg, fiberDivisor_weilCycle_eq_zero_of_ne π hπ y hy p hp]
    intro h
    apply hp
    rw [h]
    exact fiberIsoIntegralCurve_π_apply π y hy e _

/-- The curve-degree relation `HasCurveModuleDegree` does not depend on the `k`-structure (the
structure morphism to `Spec k`) when `k` is algebraically closed: `LineCartierPresentation` depends
only on the underlying scheme, and `rawZeroCycleDegree` over an algebraically closed field is the
sum of the coefficients (`rawZeroCycleDegree_eq_sum_of_isAlgClosed`), independent of residue field
degrees.

This is the transport needed in the next theorem, where the two `topSelfIntersection`s are taken
with respect to *different* `k`-structures on `C` (`ι ≫ (X ↘ Spec k)` and `C ↘ Spec k`; `ι` is not
assumed to be a `k`-morphism): both sides satisfy the relation for their own `k`-structure, the
relation is independent of the `k`-structure (this lemma), and the value is read off with
`hasCurveModuleDegree_iff_eq_topSelfIntersection`. -/
private theorem AlgebraicGeometry.Intersection.HasCurveModuleDegree.of_base {k : Type u} [Field k] [IsAlgClosed k]
    {W : AlgebraicGeometry.Scheme.{u}}
    (f f' : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper f']
    (M : W.Modules) {d : ℤ}
    (h : AlgebraicGeometry.Intersection.HasCurveModuleDegree (⟨W, f⟩ : AlgebraicGeometry.Proj.SchemeOver k) M d) :
    AlgebraicGeometry.Intersection.HasCurveModuleDegree (⟨W, f'⟩ : AlgebraicGeometry.Proj.SchemeOver k) M d := by
  obtain ⟨hInt, hNoeth, hProp, hdim, s, P, hd⟩ := h
  have : AlgebraicGeometry.IsIntegral W := hInt
  have : AlgebraicGeometry.IsNoetherian W := hNoeth
  have : AlgebraicGeometry.IsProper f := hProp
  refine ⟨hInt, hNoeth, inferInstance, hdim, s,
    ⟨P.section_ne_zero, P.cartier, P.frame, P.equation_eq⟩, ?_⟩
  rw [← hd]
  let α := P.cartier.zeroCycle hdim
  let sf := (AlgebraicGeometry.Intersection.properCycle_finiteSupport f α.1).toFinset
  have hs : ∀ x, x ∉ sf → α.1 x = 0 := by
    intro x hx
    by_contra hne
    exact hx ((AlgebraicGeometry.Intersection.properCycle_finiteSupport f α.1).mem_toFinset.mpr hne)
  rw [AlgebraicGeometry.Intersection.rawZeroCycleDegree_eq_sum_of_isAlgClosed f' α sf hs,
    AlgebraicGeometry.Intersection.rawZeroCycleDegree_eq_sum_of_isAlgClosed f α sf hs]

/-- The degree of an integral curve equals the degree of the line bundle pulled back to the curve
(as a smooth projective curve): if the carrier of `Γ` is a smooth projective curve `C` (closed
immersion `ι : C → X`), then `Γ.degree L = deg(ι^* L)`. Both sides are the top self-intersection
`topSelfIntersection` of `ι^*L` on `C`, only with respect to different `k`-structures on `C`
(`ι ≫ (X ↘ Spec k)` and `C ↘ Spec k`); for `k` algebraically closed this does not matter
(`HasCurveModuleDegree.of_base`). -/
theorem IntegralCurve.degree_eq_lineBundle_degree_pullback {k : Type u} [Field k] [IsAlgClosed k]
    {X : Variety k} {C : SmoothProjectiveCurve k} (ι : C.toScheme ⟶ X.toScheme)
    [AlgebraicGeometry.IsClosedImmersion ι]
    [hp : AlgebraicGeometry.IsProper (ι ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))]
    (L : LineBundle X) :
    letI Γ : IntegralCurve k X.toScheme := { carrier := C.toScheme, ι := ι, dim_eq_one := C.dim_one }
    Γ.degree L.toModules = (LineBundle.pullback ι L).degree := by
  let Γ : IntegralCurve k X.toScheme := { carrier := C.toScheme, ι := ι, dim_eq_one := C.dim_one }
  have : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  have : AlgebraicGeometry.IsProper
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper C.projective
  have hdim1 : C.toScheme.dimension = 1 :=
    MiyaokaMori.TopSelfIntersectionCurve.dimension_eq_one_of_schemeIsOneDimensional C.dim_one
  -- the degree relation holds for `Γ.degree L` w.r.t. the k-structure `ι ≫ (X ↘ Spec k)` (`degree_spec`),
  -- hence — k algebraically closed — also w.r.t. `C ↘ Spec k`; then read off the value on the right-hand side
  have hspec' : AlgebraicGeometry.Intersection.HasCurveModuleDegree
      (⟨C.toScheme, ι ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ :
        AlgebraicGeometry.Proj.SchemeOver k)
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L.toModules) (Γ.degree L.toModules) :=
    IntegralCurve.degree_spec Γ L.toModules
  have h2 := AlgebraicGeometry.Intersection.HasCurveModuleDegree.of_base
    (ι ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) _ hspec'
  rw [LineBundle.degree_eq_topSelfIntersection C C.isProper]
  exact (MiyaokaMori.TopSelfIntersectionCurve.hasCurveModuleDegree_iff_eq_topSelfIntersection
    C.isProper hdim1 ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L.toModules) _).mp h2

/-- **Main result.** Let `π : S → C` be a surjection from a smooth projective surface to a smooth
projective curve and `y ∈ C` a closed point. If the scheme-theoretic fibre `π.fiber y` is isomorphic
to `P¹` (via `e`), then for every line bundle `A`:
`fiberDegree π hπ A y = deg ((e.inv ≫ π.fiberι y)^* A)`, the right-hand side being the degree of
a line bundle on `P¹`.

References: Corollary 4.3 of the paper; Fulton, Example 2.4.2 and
Proposition 2.5(c).

Proof in three steps, with `F := fiberIsoIntegralCurve π y hy e` (carrier `P¹`,
`ι = e.inv ≫ π.fiberι y`):
1. `fiberCycle π hπ y = [F]` (`fiberCycle_eq_fundamentalClass_of_fiber_iso`);
2. `A ⬝ [F] = F.degree A.toModules` (`LineBundle.inter_fundamentalClass_eq_degree`);
3. `F.degree A.toModules = deg(ι^* A)` (`IntegralCurve.degree_eq_lineBundle_degree_pullback`).

Edge cases: `π⁻¹{y}` is nonempty (`hπ` is surjective); `y` is a closed point (`hy`); `e` is only an
isomorphism of schemes, not required to be a `k`-isomorphism (for `k` algebraically closed the
degree is independent of the `k`-structure, see step 3). -/
theorem fiberDegree_eq_degree_of_fiber_iso {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (A : LineBundle S.toVariety) (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (e : π.fiber y ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) :
    fiberDegree π hπ A y =
      (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
        (e.inv ≫ π.fiberι y) A).degree := by
  have : AlgebraicGeometry.IsClosedImmersion (π.fiberι y) :=
    AlgebraicGeometry.Scheme.Hom.isClosedImmersion_fiberι_of_isClosed π y hy
  have : AlgebraicGeometry.IsClosedImmersion (e.inv ≫ π.fiberι y) := inferInstance
  have : AlgebraicGeometry.IsProper
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    SmoothProjectiveVariety.isProper_structureMorphism S.toSmoothProjectiveVariety
  have : AlgebraicGeometry.IsIntegral (ProjectiveLine.asSmoothProjectiveCurve k).toScheme :=
    SmoothProjectiveCurve.isIntegral _
  unfold fiberDegree
  rw [fiberCycle_eq_fundamentalClass_of_fiber_iso π hπ y hy e,
    LineBundle.inter_fundamentalClass_eq_degree]
  have h := IntegralCurve.degree_eq_lineBundle_degree_pullback (X := S.toVariety)
    (C := ProjectiveLine.asSmoothProjectiveCurve k) (e.inv ≫ π.fiberι y) A
  exact h

end
