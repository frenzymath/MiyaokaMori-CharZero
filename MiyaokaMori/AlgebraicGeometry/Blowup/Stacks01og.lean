import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC

/-! # Stacks 01OG: the blowup of a scheme along a quasi-coherent ideal sheaf

The blowup of a scheme `X` along a quasi-coherent ideal sheaf `I` is the relative Proj of the Rees
algebra, `b : X' = Proj_X(⊕_{n ≥ 0} Iⁿ) → X`, together with its exceptional ideal `b⁻¹I`.

This is the general definition of the point blowups used in the proof of Corollary 4.3 of the paper (§4); see also Stacks 0805, 0807 and 080E.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The blowup of `X` along `I`: the relative Proj of the Rees algebra `⊕_{n ≥ 0} Iⁿ`
(with `I⁰ = O_X`), as a scheme over `X`. -/
noncomputable def AlgebraicGeometry.Scheme.blowup {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) : CategoryTheory.Over X :=
  AlgebraicGeometry.Scheme.relativeProj I.reesAlgebra

/-- The exceptional ideal of the blowup `b : X' → X` along `I`: the inverse image ideal
`b⁻¹I · O_{X'}`, whose support is the exceptional divisor `E = b⁻¹(Z)`. -/
noncomputable def AlgebraicGeometry.Scheme.blowup.exceptionalIdeal {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) : (AlgebraicGeometry.Scheme.blowup I).left.IdealSheafData :=
  I.comap (AlgebraicGeometry.Scheme.blowup I).hom

end
