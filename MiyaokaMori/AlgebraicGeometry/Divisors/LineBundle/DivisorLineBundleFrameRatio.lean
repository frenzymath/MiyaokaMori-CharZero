import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleFrame

/-! # Transition units of `O_X(D)` in terms of generic values

**Transition units of `O_X(D)` in terms of generic values** (Hartshorne II.6.13(a)): let `t_i ∈ 𝒦^*(U_i)`,
`t_j ∈ 𝒦^*(U_j)` be local equations of the Cartier divisor `D`, `W ⊆ U_i ∩ U_j` nonempty and
`w ∈ O_X(W)`. Then, for the frames `t_i^{-1}`, `t_j^{-1}` of `O_X(D)` (`IsLocalEquation.frame`),

  `w • t_j^{-1}|_W = t_i^{-1}|_W  ⟺  germ(w) · val(t_j)^{-1} = val(t_i)^{-1}` in `K(X)`,

where `val : 𝒦^*(W) → K(X)^*` is the (injective) value at the generic point
(`rationalUnitsSectionToFunctionField`) and `germ(w) = X.germToFunctionField W w`.

Proof: `t^{-1}|_W` is `lineBundleSectionEquiv` of `invSection` (`res_frame`); the equiv is linear and
injective, so the left side is an equality in the submodule `lineBundleSections D W ⊆ 𝒦_X(W)`, i.e.
`ι(w) · t_j^{-1}|_W = t_i^{-1}|_W` in `𝒦_X(W)`; `𝒦_X(W) → K(X)` is an injective ring homomorphism
(Stacks 01X5, `rationalSectionToFunctionField_injective`) with `val ∘ ι = germ`
(`toRationalFunctionsSheaf_rationalSectionToFunctionField`).

Used in `CartierPullbackLineBundle`: it turns the comparison of transition units of `O_X(f^*D)` and
`f^*O_Y(D)` into the identity `f^♯(germ w) = germ(f^♯ w)` in `K(X)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CartierDivisor

variable {k : Type u} [Field k] {X : Variety k}

/-- The value of a unit section, as an element of `K(X)`, is the value of its underlying section. -/
theorem coe_rationalUnitsSectionToFunctionField {U : X.toScheme.Opens} [Nonempty U]
    (t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    ((X.toScheme.rationalUnitsSectionToFunctionField U t : (X.toScheme.functionField)ˣ) :
      X.toScheme.functionField) = X.toScheme.rationalSectionToFunctionField U (unitVal t) := rfl

/-- The value of `ι(w)` is the germ of `w`. -/
theorem rationalSectionToFunctionField_toRationalFunctionsSheaf {W : X.toScheme.Opens} [Nonempty W]
    (w : Γ(X.toScheme, W)) :
    X.toScheme.rationalSectionToFunctionField W
        ((X.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom w) =
      X.toScheme.germToFunctionField W w := by
  have h := X.toScheme.toRationalFunctionsSheaf_rationalSectionToFunctionField W
  exact ConcreteCategory.congr_hom h w

/-- The value of the restriction of `t^{-1}` is the inverse of the value of the restriction of `t`. -/
theorem rationalSectionToFunctionField_res_inv {U W : X.toScheme.Opens} [Nonempty W] (h : W ≤ U)
    (t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    X.toScheme.rationalSectionToFunctionField W
        ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE h).op).hom (unitVal t⁻¹)) =
      ((X.toScheme.rationalUnitsSectionToFunctionField W
          (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE h).op t))⁻¹ :
        (X.toScheme.functionField)ˣ) := by
  rw [← map_inv, coe_rationalUnitsSectionToFunctionField, ← unitVal_restrict, map_inv]

/-- **Frame ratio criterion**: `w • t_j^{-1}|_W = t_i^{-1}|_W` iff `germ(w) · val(t_j)^{-1} = val(t_i)^{-1}`. -/
theorem IsLocalEquation.smul_res_frame_iff {D : CartierDivisor X} {Ui Uj W : X.toScheme.Opens}
    [Nonempty W] {ti : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op Ui)}
    {tj : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op Uj)}
    (hti : IsLocalEquation D Ui ti) (htj : IsLocalEquation D Uj tj)
    (hi : W ≤ Ui) (hj : W ≤ Uj) (w : Γ(X.toScheme, W)) :
    w • (CartierDivisor.lineBundleModules D).res hj htj.frame =
        (CartierDivisor.lineBundleModules D).res hi hti.frame ↔
      X.toScheme.germToFunctionField W w *
          ((X.toScheme.rationalUnitsSectionToFunctionField W
              (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op tj))⁻¹ :
            (X.toScheme.functionField)ˣ) =
        ((X.toScheme.rationalUnitsSectionToFunctionField W
            (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hi).op ti))⁻¹ :
          (X.toScheme.functionField)ˣ) := by
  rw [hti.res_frame hi, htj.res_frame hj, ← (lineBundleSectionEquiv D W).map_smul,
    (lineBundleSectionEquiv D W).injective.eq_iff, Subtype.ext_iff]
  change (X.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom w *
      (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hj).op).hom (unitVal tj⁻¹) =
    (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hi).op).hom (unitVal ti⁻¹) ↔ _
  rw [← (X.toScheme.rationalSectionToFunctionField_injective W).eq_iff, map_mul,
    rationalSectionToFunctionField_toRationalFunctionsSheaf,
    rationalSectionToFunctionField_res_inv hj tj, rationalSectionToFunctionField_res_inv hi ti]

end CartierDivisor

end
