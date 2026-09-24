import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.CurveStalkFunctionField
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.CurveStalkValuation
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.StalkRegularOrder

/-! # The fibre divisor of a ruled surface

`π_S^*(y)`: the effective divisor on `S` obtained by pulling back the point divisor `[y]` along
`π_S` (the fibre with multiplicities), as in the proof of Lemma 5.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The Weil cycle of the zero Cartier divisor is zero (`weilCycle_add` with `D = E = 0`). -/
theorem CartierDivisor.weilCycle_zero {k : Type u} [Field k] (V : Variety k) :
    CartierDivisor.weilCycle V (0 : CartierDivisor V) = 0 := by
  have h := CartierDivisor.weilCycle_add V (0 : CartierDivisor V) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- Pull back local equations `(U_i, g_i) ↦ (f⁻¹U_i, f^♮ g_i)` along a dominant morphism `f : X → Y`:
if every `g_i` is regular at every point of `U_i` (lies in the image of the local ring), then the
glued Cartier divisor is effective.
Proof: the Weil coefficient at `p ∈ f⁻¹U_i` is `ord_p(f^♮ g_i)` (`weilCycle_ofLocalData`; if the
pulled-back data are not compatible, `ofLocalData` is `0`, still effective). If `g_i = a` with
`a ∈ O_{Y,f(p)}` then `f^♮ g_i = f^♯_p a ∈ O_{X,p}` (`dominantFunctionFieldMap_algebraMap`), and a
nonzero regular element has `ord ≥ 0` (`ord_algebraMap_nonneg`). -/
theorem CartierDivisor.effective_ofLocalData_pullback {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsDominant f]
    {ι : Type u} (U : ι → Y.toScheme.Opens) (g : ι → (Y.toScheme.functionField)ˣ)
    (hreg : ∀ i, ∀ x ∈ U i, ((g i : Y.toScheme.functionField)) ∈
      Set.range (algebraMap (Y.toScheme.presheaf.stalk x) Y.toScheme.functionField)) :
    CartierDivisor.Effective (CartierDivisor.ofLocalData (fun i => f ⁻¹ᵁ U i)
      (fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i))) := by
  intro p
  by_cases hLD : CartierDivisor.IsLocalData (fun i => f ⁻¹ᵁ U i)
      (fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i))
  · have hp : p ∈ (⨆ i, f ⁻¹ᵁ U i : X.toScheme.Opens) := by rw [hLD.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    rw [CartierDivisor.weilCycle_ofLocalData X _ _ hLD i p hi]
    obtain ⟨a, ha⟩ := hreg i (f.base p) hi
    have hga : ((Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i) :
        (X.toScheme.functionField)ˣ) : X.toScheme.functionField) =
        algebraMap (X.toScheme.presheaf.stalk p) X.toScheme.functionField (f.stalkMap p a) := by
      rw [← AlgebraicGeometry.Scheme.dominantFunctionFieldMap_algebraMap f p a, ha]
      rfl
    rw [hga]
    apply AlgebraicGeometry.Divisors.StalkRegularOrder.ord_algebraMap_nonneg
    intro h0
    apply Units.ne_zero (Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i))
    rw [hga, h0, map_zero]
  · have h0 : CartierDivisor.ofLocalData (fun i => f ⁻¹ᵁ U i)
        (fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i)) = 0 := by
      unfold CartierDivisor.ofLocalData
      exact if_neg hLD
    rw [h0, CartierDivisor.weilCycle_zero]
    exact le_rfl

/-- Any local equations `(U_i, g_i)` of an effective Cartier divisor `D` on a smooth projective curve
are regular at every point `x ∈ U_i`.
If `x` has coheight `1` (a closed point), the stalk is a DVR (`isDiscreteValuationRing_stalk`),
`ord_x(g_i)` is the coefficient of `[D]` at `x`, which is `≥ 0` (`weilCycle_ofLocalData`), and in a
DVR valuation `≥ 0` means lying in the stalk (`valuation_nonneg_iff`). If the coheight is not `1`,
then `height + coheight = dim C = 1` forces `coheight x = 0`, so `x` is maximal, i.e. the generic
point, whose stalk is the function field. -/
theorem SmoothProjectiveCurve.localData_mem_range_of_effective {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {D : CartierDivisor C.toVariety}
    (hD : CartierDivisor.Effective D)
    {ι : Type u} (U : ι → C.toScheme.Opens) (g : ι → (C.toScheme.functionField)ˣ)
    (hUg : CartierDivisor.IsLocalData (X := C.toVariety) U g)
    (hDg : D = CartierDivisor.ofLocalData (X := C.toVariety) U g)
    (i : ι) (x : C.toScheme) (hx : x ∈ U i) :
    ((g i : C.toScheme.functionField)) ∈
      Set.range (algebraMap (C.toScheme.presheaf.stalk x) C.toScheme.functionField) := by
  by_cases hco : Order.coheight x = 1
  · have : IsDiscreteValuationRing (C.toScheme.presheaf.stalk x) :=
      SmoothProjectiveCurve.isDiscreteValuationRing_stalk C x hco
    have hord : 0 ≤ C.toScheme.ord (g i : C.toScheme.functionField) x := by
      have h := hD x
      rw [hDg, CartierDivisor.weilCycle_ofLocalData C.toVariety U g hUg i x hx] at h
      exact h
    have hval : 0 ≤ AlgebraicGeometry.Divisors.CurveStalkValuation.valuation C.toScheme x hco
        (g i : C.toScheme.functionField) := by
      rw [AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_of_ne_zero C.toScheme x hco (g i).ne_zero]
      exact_mod_cast hord
    exact (AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_nonneg_iff C.toScheme x hco _).mp hval
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
    refine ⟨(g i : C.toScheme.functionField), ?_⟩
    change (C.toScheme.presheaf.stalkSpecializes _).hom (g i : C.toScheme.functionField) = _
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl

/-- The point divisor `[y]` is effective: for closed `y` its Weil coefficient is `1_{x = y} ≥ 0`
(`ofPoint_weilCycle`); for non-closed `y`, `[y] = 0`. -/
theorem Divisor.ofPoint_effective {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (y : C.toScheme) : CartierDivisor.Effective (Divisor.ofPoint y) := by
  by_cases hy : IsClosed ({y} : Set C.toScheme)
  · intro x
    rw [Divisor.ofPoint_weilCycle y hy x]
    split_ifs <;> norm_num
  · rw [Divisor.ofPoint_of_not_isClosed y hy]
    intro x
    rw [CartierDivisor.weilCycle_zero]
    exact le_rfl

/-- The fibre divisor `π^*[y]` of a surjective morphism `π : S → C` from a smooth projective surface
to a smooth projective curve over the point `y`. -/
noncomputable def fiberDivisor {k : Type u} [Field k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) : CartierDivisor S.toVariety :=
  CartierDivisor.pullback π hπ.surj (Divisor.ofPoint y)

/-- The fibre divisor `π^*[y]` is effective: its local equations `π^♮ g_i` are regular functions
(`[y]` is effective, so its local equations `g_i` are regular on `C`,
`localData_mem_range_of_effective`), hence the order at every codimension-one point is `≥ 0`
(`effective_ofLocalData_pullback`). -/
theorem fiberDivisor_effective {k : Type u} [Field k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) : CartierDivisor.Effective (fiberDivisor π hπ y) := by
  have : AlgebraicGeometry.IsDominant π := ⟨hπ.surj.denseRange⟩
  obtain ⟨ι, U, g, hUg, hD⟩ := cartierDivisor_exists_localData C.toVariety (Divisor.ofPoint y)
  unfold fiberDivisor
  rw [hD, CartierDivisor.pullback_ofLocalData (X := S.toVariety) (Y := C.toVariety) π hπ.surj hUg]
  exact CartierDivisor.effective_ofLocalData_pullback (X := S.toVariety) (Y := C.toVariety) π _ _
    (fun i x hx => SmoothProjectiveCurve.localData_mem_range_of_effective
      (Divisor.ofPoint_effective y) _ _ hUg hD i x hx)

end
