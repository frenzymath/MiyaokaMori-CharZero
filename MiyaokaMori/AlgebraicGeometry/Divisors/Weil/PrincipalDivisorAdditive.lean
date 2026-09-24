import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.Divisor
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.PrincipalDivisorFiniteness
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.SchemePrincipalWeilDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor

/-! # Additivity of principal divisors

`div(fg) = div(f) + div(g)`: the principal divisor gives a group homomorphism `K(X)^× → Div(X)` whose image
is the subgroup of principal divisors.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open Classical in
private lemma coeff_restricted_sum {X : AlgebraicGeometry.Scheme.{u}}
    (c : X → ℤ) (hc : (Function.support c).Finite)
    (Z : {x : X // X.IsPrimeDivisor x}) :
    (FreeAbelianGroup.toFinsupp
        (∑ x ∈ hc.toFinset,
          if hx : X.IsPrimeDivisor x then c x • FreeAbelianGroup.of ⟨x, hx⟩ else 0)) Z =
      c Z := by
  classical
  have hterm (x : X) :
      (FreeAbelianGroup.toFinsupp
          (if hx : X.IsPrimeDivisor x then
            c x • FreeAbelianGroup.of ⟨x, hx⟩ else 0)) Z =
        if x = Z then c x else 0 := by
    by_cases hx : X.IsPrimeDivisor x
    · by_cases heq : x = (Z : X)
      · subst x
        simp [hx, FreeAbelianGroup.toFinsupp_of]
      · have hsub : ¬ (⟨x, hx⟩ : {y : X // X.IsPrimeDivisor y}) = Z := by
          intro h
          exact heq (congrArg Subtype.val h)
        rw [dif_pos hx, map_zsmul, FreeAbelianGroup.toFinsupp_of, if_neg heq]
        change (c x • Finsupp.single (⟨x, hx⟩ : {y : X // X.IsPrimeDivisor y}) 1) Z = 0
        simp [hsub]
    · by_cases heq : x = (Z : X)
      · subst x
        exact (hx Z.property).elim
      · rw [dif_neg hx, if_neg heq]
        change (FreeAbelianGroup.toFinsupp (0 : FreeAbelianGroup _)) Z = 0
        rw [map_zero]
        rfl
  by_cases h : c Z = 0 <;> simp [hterm, h]

/-- `div(fg) = div(f) + div(g)`. -/
theorem AlgebraicGeometry.Scheme.principalDivisor_mul {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X] {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    X.principalDivisor (f * g) = X.principalDivisor f + X.principalDivisor g := by
  classical
  letI : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  change (show FreeAbelianGroup _ from X.principalDivisor (f * g)) =
    (show FreeAbelianGroup _ from X.principalDivisor f) +
      (show FreeAbelianGroup _ from X.principalDivisor g)
  unfold AlgebraicGeometry.Scheme.principalDivisor
  simp only [dif_neg (mul_ne_zero hf hg), dif_neg hf, dif_neg hg]
  apply (FreeAbelianGroup.equivFinsupp _).injective
  apply Finsupp.ext
  intro Z
  set_option backward.isDefEq.respectTransparency false in
    simp only [FreeAbelianGroup.equivFinsupp_apply]
  set_option backward.isDefEq.respectTransparency false in
    rw [map_add]
  rw [Finsupp.add_apply]
  set_option backward.isDefEq.respectTransparency false in
    rw [coeff_restricted_sum, coeff_restricted_sum, coeff_restricted_sum]
  simp only [AlgebraicGeometry.Scheme.principalCycle_apply, Units.val_mk0]
  exact AlgebraicGeometry.Scheme.ord_mul hf hg

/-- `div(1) = 0`. -/
theorem AlgebraicGeometry.Scheme.principalDivisor_one (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X] :
    X.principalDivisor (1 : X.functionField) = 0 := by
  simp [AlgebraicGeometry.Scheme.principalDivisor, AlgebraicGeometry.Scheme.principalCycle_one]

/-- The group homomorphism `K(X)^× → Div(X)`, `u ↦ div(u)`; the data is `principalDivisor`, the two axioms are
the two theorems above. -/

noncomputable def AlgebraicGeometry.Scheme.principalDivisorHom (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X] :
    (X.functionField)ˣ →* Multiplicative X.WeilDivisor where
  toFun u := Multiplicative.ofAdd (X.principalDivisor (u : X.functionField))
  map_one' := by
    rw [Units.val_one, AlgebraicGeometry.Scheme.principalDivisor_one]; rfl
  map_mul' u v := by
    rw [Units.val_mul, AlgebraicGeometry.Scheme.principalDivisor_mul u.ne_zero v.ne_zero]; rfl

end
