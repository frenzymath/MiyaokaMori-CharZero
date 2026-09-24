import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdFiniteOnNoetherianOpen
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs

/-! # The principal cycle of a rational function

The principal divisor `div(r) ∈ Z_{dim X - 1}(X)` of `r ∈ K(X)^×`: the cycle of the orders of vanishing of
`r` at the codimension-one points (with locally finite support). Fulton §1.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The principal cycle on an integral **locally Noetherian** scheme `W`: for `r ∈ K(W)^×`, `z ↦ ord_z(r)`
(Mathlib's `Scheme.ord`, which is `0` at points of coheight `≠ 1`). No quasi-compactness is needed:
`AlgebraicCycle` only requires locally finite support, and the support of `Scheme.ord` is locally finite on
any integral locally Noetherian scheme (`exists_isOpen_finite_ord_ne_zero`), so this agrees with `div(f)` of
Stacks 02RV, 02SE. On a Noetherian scheme it is the cycle of the principal Cartier datum
(`principalCycle_eq_algebraicCycle_principalCartierData`). -/

noncomputable def AlgebraicGeometry.Scheme.principalCycle (W : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (r : W.functionFieldˣ) : AlgebraicGeometry.AlgebraicCycle W ℤ where
  toFun z := W.ord (r : W.functionField) z
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' z _ := by
    obtain ⟨V, hzV, -, hfin⟩ :=
      AlgebraicGeometry.Scheme.exists_isOpen_finite_ord_ne_zero (r : W.functionField) z ⊤ trivial
    refine ⟨(V : Set W), V.isOpen.mem_nhds hzV, hfin.subset ?_⟩
    rintro x ⟨hxV, hx⟩
    exact ⟨hxV, hx⟩

theorem AlgebraicGeometry.Scheme.principalCycle_apply (W : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (r : W.functionFieldˣ) (z : W) :
    W.principalCycle r z = W.ord (r : W.functionField) z := rfl

theorem AlgebraicGeometry.Scheme.principalCycle_mul (W : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (r s : W.functionFieldˣ) :
    W.principalCycle (r * s) = W.principalCycle r + W.principalCycle s := by
  refine Function.locallyFinsuppWithin.ext fun z => ?_
  rw [Function.locallyFinsuppWithin.coe_add]
  show W.ord ((r * s : W.functionFieldˣ) : W.functionField) z = _
  rw [Units.val_mul, AlgebraicGeometry.Scheme.ord_mul r.ne_zero s.ne_zero]
  rfl

/-- `div(1) = 0`. -/
theorem AlgebraicGeometry.Scheme.principalCycle_one (W : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W] :
    W.principalCycle 1 = 0 := by
  have h := W.principalCycle_mul 1 1
  rw [mul_one] at h
  have h2 : W.principalCycle 1 + W.principalCycle 1 = 0 + W.principalCycle 1 := by
    rw [zero_add]; exact h.symm
  exact add_right_cancel h2

theorem AlgebraicGeometry.Scheme.principalCycle_inv (W : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (r : W.functionFieldˣ) : W.principalCycle r⁻¹ = -W.principalCycle r := by
  have h := W.principalCycle_mul r r⁻¹
  rw [mul_inv_cancel, W.principalCycle_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- `div : K(W)^× → Z_{dim W − 1}(W)` as a homomorphism of additive groups (the multiplicative group written as
`Additive`). -/
noncomputable def AlgebraicGeometry.Scheme.principalCycleHom (W : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W] :
    Additive W.functionFieldˣ →+ AlgebraicGeometry.AlgebraicCycle W ℤ :=
  AddMonoidHom.mk' (fun r => W.principalCycle (Additive.toMul r))
    (fun _ _ => W.principalCycle_mul _ _)

theorem AlgebraicGeometry.Scheme.principalCycle_zpow (W : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (r : W.functionFieldˣ) (n : ℤ) : W.principalCycle (r ^ n) = n • W.principalCycle r :=
  map_zsmul W.principalCycleHom n (Additive.ofMul r)

/- `simp`/`rw` rewriting in the argument of `principalCycle` auto-generates the congruence lemma
   `AlgebraicGeometry.Scheme.principalCycle.congr_simp`. If two downstream modules that do not import each
   other both generate it, a third module importing both fails with `environment already contains`; so it is
   generated once here, in the module of the definition. -/
private theorem AlgebraicGeometry.Scheme.principalCycle_congr_aux
    {W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    {r s : W.functionFieldˣ} (h : r = s) : W.principalCycle r = W.principalCycle s := by
  simp only [h]

/-- On a Noetherian `W`, `div(r)` is the cycle of the principal Cartier datum `principalCartierData r` (both
have coefficients `Scheme.ord`). -/
theorem AlgebraicGeometry.Scheme.principalCycle_eq_algebraicCycle_principalCartierData
    (W : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsNoetherian W]
    (r : W.functionFieldˣ) :
    W.principalCycle r = (AlgebraicGeometry.Intersection.principalCartierData r).algebraicCycle :=
  Function.locallyFinsuppWithin.ext fun z =>
    (AlgebraicGeometry.Intersection.principalCartierData_coefficient r z).symm

/-- On a Noetherian `W`, `div(r)` has finite support (`CartierLocalData.algebraicCycle_support_finite`). -/
theorem AlgebraicGeometry.Scheme.principalCycle_support_finite
    (W : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsNoetherian W]
    (r : W.functionFieldˣ) : (Function.support (W.principalCycle r)).Finite := by
  rw [W.principalCycle_eq_algebraicCycle_principalCartierData r]
  exact AlgebraicGeometry.Intersection.CartierLocalData.algebraicCycle_support_finite _

/-- On a Noetherian `W` of dimension `≤ 1`, `div(r)` is the underlying cycle of the zero cycle
`CartierLocalData.zeroCycle` of the principal Cartier datum. -/
theorem AlgebraicGeometry.Scheme.principalCycle_eq_zeroCycle
    (W : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsNoetherian W]
    (r : W.functionFieldˣ) (hdim : topologicalKrullDim W ≤ 1) :
    W.principalCycle r = ((AlgebraicGeometry.Intersection.principalCartierData r).zeroCycle hdim).1 :=
  W.principalCycle_eq_algebraicCycle_principalCartierData r

theorem principalCycle_mem_cycleGroup {k : Type u} [Field k] (X : Variety k)
    (r : X.toScheme.functionFieldˣ) :
    X.toScheme.principalCycle r ∈ CycleGroup X (X.toScheme.dimension - 1) := by
  intro x hx
  rw [AlgebraicGeometry.Scheme.principalCycle_apply] at hx
  have hco : Order.coheight x = 1 := by
    by_contra h
    exact hx (AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one h _)
  have h1 := Variety.height_add_coheight X x
  rw [hco] at h1
  have hne : Order.height x ≠ ⊤ := by
    intro h; rw [h] at h1; simp at h1
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at h1 ⊢
  have : n + 1 = X.toScheme.dimension := by exact_mod_cast h1
  have : n = X.toScheme.dimension - 1 := by omega
  rw [this]

noncomputable def principalDivisor {k : Type u} [Field k] (X : Variety k)
    (r : X.toScheme.functionFieldˣ) : CycleGroup X (X.toScheme.dimension - 1) :=
  ⟨X.toScheme.principalCycle r, principalCycle_mem_cycleGroup X r⟩

end
