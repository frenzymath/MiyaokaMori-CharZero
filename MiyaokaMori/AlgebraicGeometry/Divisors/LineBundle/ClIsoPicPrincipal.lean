import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPrincipal
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierWeilIso
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisorAdditive
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeilUniqueHelpers

/-! # Principal Cartier divisors: trivial line bundle and principal Weil divisor

Two basic properties of the principal Cartier divisor `div(a)`, used for `Cl(X) ≅ Pic(X)` (`ClIsoPic`):

* **`O_X(div a) ≅ O_X`** (Hartshorne II.6.13(c), direction `⇒`): `div(a)` is given by the single chart
  `(X, a)`, the global section `t ∈ 𝒦^*(X)` with value `a` is its local equation, so `t⁻¹` is a global
  frame of `O_X(div a)`, and a global frame gives `O_X(div a) ≅ O_X` (`IsLocalEquation.isFrame`,
  `IsFrame.topTrivialization`).
* **The Cartier `div(a)` corresponds to the Weil `div(a)`** (Hartshorne II.6.11, "principal ↔
  principal"): both have coefficient `ord_Z(a)` at every prime divisor `Z` — on the left by
  `weilCycle_ofLocalData` (on a single chart the coefficient is the `ord` of the equation), on the right
  by the definition of `X.principalDivisor` (the coefficients of `X.principalCycle` are `Scheme.ord`).

Sources: Hartshorne II.6.11, II.6.13(c).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CartierDivisor

variable {k : Type u} [Field k] {X : Variety k}

/-- The principal local datum `principalCartierData a` (single chart `⊤`, equation `a`) satisfies the
gluing condition `IsLocalData`. -/
theorem principal_isLocalData (a : X.toScheme.functionFieldˣ) :
    CartierDivisor.IsLocalData (AlgebraicGeometry.Intersection.principalCartierData a).opens
      (fun i => Units.mk0 ((AlgebraicGeometry.Intersection.principalCartierData a).equation i)
        ((AlgebraicGeometry.Intersection.principalCartierData a).equation_ne_zero i)) := by
  dsimp [CartierDivisor.IsLocalData]
  constructor
  · ext y
    simp only [AlgebraicGeometry.Intersection.principalCartierData]
    simp
  · intro i j y hy
    constructor
    · refine ⟨1, ?_⟩
      simp [AlgebraicGeometry.Intersection.principalCartierData]
    · refine ⟨1, ?_⟩
      simp [AlgebraicGeometry.Intersection.principalCartierData]

/-- `CartierDivisor.principal a` is the divisor glued by `ofLocalData` from the single-chart datum (by
definition). -/
theorem principal_eq_ofLocalData (a : X.toScheme.functionFieldˣ) :
    CartierDivisor.principal a =
      CartierDivisor.ofLocalData (AlgebraicGeometry.Intersection.principalCartierData a).opens
        (fun i => Units.mk0 ((AlgebraicGeometry.Intersection.principalCartierData a).equation i)
          ((AlgebraicGeometry.Intersection.principalCartierData a).equation_ne_zero i)) := rfl

/-- `div(a)` has a global local equation (the section of `𝒦^*(X)` with value `a`). -/
theorem exists_isLocalEquation_principal_top (a : X.toScheme.functionFieldˣ) :
    ∃ t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op ⊤),
      CartierDivisor.IsLocalEquation (CartierDivisor.principal a) ⊤ t := by
  let x₀ : X.toScheme := Classical.arbitrary _
  obtain ⟨t, -, ht⟩ := CartierToWeilLocalSection.local_section_ofLocalData
    (AlgebraicGeometry.Intersection.principalCartierData a).opens
    (fun i => Units.mk0 ((AlgebraicGeometry.Intersection.principalCartierData a).equation i)
      ((AlgebraicGeometry.Intersection.principalCartierData a).equation_ne_zero i))
    (principal_isLocalData a) x₀ ⟨0⟩ trivial
  exact ⟨t, ht⟩

/-- Hartshorne II.6.13(c), direction `⇒`: `O_X(div a) ≅ O_X` (global frame `t⁻¹`). -/
theorem lineBundle_principal (a : X.toScheme.functionFieldˣ) :
    Nonempty ((CartierDivisor.lineBundle (CartierDivisor.principal a)).toModules
      ≅ SheafOfModules.unit X.toScheme.ringCatSheaf) := by
  obtain ⟨t, ht⟩ := exists_isLocalEquation_principal_top a
  exact ⟨ht.isFrame.topTrivialization.symm⟩

end CartierDivisor

open Classical in
private lemma coeff_restricted_sum' {X : AlgebraicGeometry.Scheme.{u}}
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
        rw [map_zero]
        rfl
  by_cases h : c Z = 0 <;> simp [hterm, h]

/-- The coefficient of the principal Weil divisor `div(a)` at a prime divisor `Z` is `ord_Z(a)` (the
definition of principal divisors in Hartshorne II.6.11). -/
theorem AlgebraicGeometry.Scheme.principalDivisor_coeff (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X]
    (a : X.functionFieldˣ) (Z : {Z : X // X.IsPrimeDivisor Z}) :
    FreeAbelianGroup.coeff Z (X.principalDivisor (a : X.functionField)) =
      X.ord (a : X.functionField) Z := by
  classical
  let _ : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hne : (a : X.functionField) ≠ 0 := a.ne_zero
  show FreeAbelianGroup.toFinsupp (X.principalDivisor (a : X.functionField)) Z = _
  unfold AlgebraicGeometry.Scheme.principalDivisor
  rw [dif_neg hne]
  refine (coeff_restricted_sum' _ _ Z).trans ?_
  rw [AlgebraicGeometry.Scheme.principalCycle_apply, Units.val_mk0]

/-- Hartshorne II.6.11 ("principal Cartier divisors ↔ principal Weil divisors"): `cartierToWeilHom` sends
the Cartier `div(a)` to the Weil `div(a)`; both have coefficient `ord_Z(a)` at every prime divisor. -/
theorem cartierToWeilHom_principal {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (a : X.toScheme.functionFieldˣ) :
    cartierToWeilHom X (CartierDivisor.principal a) =
      X.toScheme.principalDivisor (a : X.toScheme.functionField) := by
  apply (FreeAbelianGroup.equivFinsupp _).injective
  ext Z
  have hL := cartierToWeilFun_coeff X (CartierDivisor.principal a) Z.1 Z.2
  have hR := AlgebraicGeometry.Scheme.principalDivisor_coeff X.toScheme a Z
  change FreeAbelianGroup.coeff Z (cartierToWeilFun X (CartierDivisor.principal a)) =
    FreeAbelianGroup.coeff Z (X.toScheme.principalDivisor (a : X.toScheme.functionField))
  rw [hR, hL, CartierDivisor.principal_eq_ofLocalData]
  exact CartierDivisor.weilCycle_ofLocalData X.toVariety _ _
    (CartierDivisor.principal_isLocalData a) ⟨0⟩ Z.1 trivial

/-- The same statement for `cartierWeilEquiv`. -/
theorem cartierWeilEquiv_principal {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (a : X.toScheme.functionFieldˣ) :
    cartierWeilEquiv X (CartierDivisor.principal a) =
      X.toScheme.principalDivisor (a : X.toScheme.functionField) :=
  cartierToWeilHom_principal X a

end
