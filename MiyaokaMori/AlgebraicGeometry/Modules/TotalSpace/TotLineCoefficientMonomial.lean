import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap

/-! # The ξ-coefficients of a monomial

**The ξ-coefficients of a monomial**: `coefficient L M q (monomial L M q c) = c` (`totalSpace.coefficient_monomial_eq`)
and `coefficient L M q' (monomial L M q c) = 0` for `q' ≠ q` (`totalSpace.coefficient_monomial_eq_zero_of_ne`), for a line
bundle `L` and a line bundle `M` on any scheme `X` (coefficients and monomials are inverse to each other).

This module is an alias layer: each statement is a one-line reference to its counterpart in
`TotLineCoefficientMap` (`tensorPowerToSymPart_comp_symPartToTensorPower`, `coefficient_monomial`,
`coefficient_monomial_of_ne`); names and statements are kept for the users `TotSectionsPolynomial`
(`xiCoefficient_xiMonomial`) and `TotLineMonomialMul`. For the proof see the docstring of
`totalSpace.coefficient_monomial` in `TotLineCoefficientMap`.
-/

set_option autoImplicit false
universe u
open CategoryTheory
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `Θ_q ≫ Θ'_q = 𝟙`: `tensorPowerToSymPart ≫ symPartToTensorPower = 𝟙`.
Alias of `totalSpace.tensorPowerToSymPart_comp_symPartToTensorPower` (`TotLineCoefficientMap`). -/
theorem totalSpace.tensorPowerToSymPart_symPartToTensorPower (L : X.Modules) [L.IsLineBundle] (q : ℕ) :
    totalSpace.tensorPowerToSymPart L q ≫ totalSpace.symPartToTensorPower L q = 𝟙 _ :=
  totalSpace.tensorPowerToSymPart_comp_symPartToTensorPower L q

/-- `coefficient q (monomial q c) = c`. Alias of `totalSpace.coefficient_monomial` (`TotLineCoefficientMap`). -/
theorem totalSpace.coefficient_monomial_eq (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle] (q : ℕ)
    (c : ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q).val.obj (Opposite.op ⊤) : Type u)) :
    totalSpace.coefficient L M q (totalSpace.monomial L M q c) = c :=
  totalSpace.coefficient_monomial L M q c

/-- `coefficient q' (monomial q c) = 0` for `q' ≠ q`. Alias of `totalSpace.coefficient_monomial_of_ne`
(`TotLineCoefficientMap`). -/
theorem totalSpace.coefficient_monomial_eq_zero_of_ne (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle] {q q' : ℕ}
    (h : q' ≠ q) (c : ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q).val.obj (Opposite.op ⊤) : Type u)) :
    totalSpace.coefficient L M q' (totalSpace.monomial L M q c) = 0 :=
  totalSpace.coefficient_monomial_of_ne L M h c

end AlgebraicGeometry.Scheme
end
