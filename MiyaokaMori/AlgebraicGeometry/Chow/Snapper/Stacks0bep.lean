import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bem

/-! # The Snapper intersection number (Stacks 0BEP)

The numerical intersection number (Stacks 0BEP): for invertible sheaves `L_1, …, L_d` on a proper
scheme `X` of dimension `d`, the intersection number `(L_1⋯L_d·X)` is the coefficient of the monomial
`n_1⋯n_d` in the numerical polynomial `χ(X, L_1^{n_1} ⊗ ⋯ ⊗ L_d^{n_d})` (the case `Z = X` of 0BEP). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The Snapper intersection number `(L_1⋯L_d·X) := Σ_{S ⊆ {1..d}} (-1)^{d-|S|} χ(X, ⊗_{i∈S} L_i)`, i.e.
the mixed difference `Δ_1⋯Δ_d` at the origin of `n ↦ χ(X, L_1^{n_1} ⊗ ⋯ ⊗ L_d^{n_d})`. The numerical
polynomial of 0BEM has total degree `≤ d`, and its mixed difference is exactly the coefficient of the
monomial `n_1⋯n_d`, so this agrees with the definition of Stacks 0BEP; the finite sum is written
directly, without choosing a polynomial from an existence theorem. The tensor product is spelled
exactly as in Stacks 0BEM (with `n_i = 1_{i∈S}`). -/
noncomputable def AlgebraicGeometry.snapperIntersection {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    {d : ℕ} (hd : X.dimension = d) (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle] : ℚ :=
  ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
    (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
      ((List.finRange d).foldl
        (fun (G : X.Modules) (i : Fin d) => G.tensor (L i ^ (if i ∈ S then (1 : ℤ) else 0)))
        (SheafOfModules.unit X.ringCatSheaf)) : ℚ)

end