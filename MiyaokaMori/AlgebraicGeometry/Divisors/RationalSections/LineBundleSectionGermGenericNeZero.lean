import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionGenericGermZero

/-! # Nonzero sections of a line bundle have nonzero generic germ

On an integral scheme, a nonzero global section of a line bundle has nonzero germ at the generic point
(the discussion before Stacks 02OQ: invertible sheaves on an integral scheme are torsion-free). It is
the contrapositive of `lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- On an integral scheme, a nonzero global section of a line bundle has nonzero germ at the generic point.

Source: the discussion before Stacks 02OQ (invertible sheaves on an integral scheme are torsion-free);
Hartshorne II.6. Proof: the contrapositive is `lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero`
(a global section of a line bundle on an integral scheme whose germ at the generic point is zero is zero:
take a trivializing open `V` at each point, the generic point lies in `V`, `σ|_V` corresponds to
`a ∈ Γ(X, V)`, `germ_injective_of_isIntegral` gives `a = 0`, and the sheaf axiom
`TopCat.Presheaf.section_ext` gives `σ = 0`). Edge cases: if `X` is a point, `Γ(L) = L_η`; if `L` is
trivial, this is the injectivity of the embedding of a domain into its fraction field. -/
theorem AlgebraicGeometry.Scheme.Modules.germ_genericPoint_ne_zero
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (L : X.Modules) [L.IsLineBundle] (σ : (L.val.obj (Opposite.op ⊤) : Type u)) (hσ : σ ≠ 0) :
    L.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(L, ⊤) from σ) ≠ 0 :=
  fun h => hσ (lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero L σ h)

end
