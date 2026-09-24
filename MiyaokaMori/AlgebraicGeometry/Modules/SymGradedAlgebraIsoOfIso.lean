import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraCongr

/-! # Functoriality of the symmetric algebra along isomorphisms

Functoriality of the symmetric algebra along isomorphisms: an isomorphism `e : M ≅ N` of
quasi-coherent modules induces an isomorphism `Sym M ≅ Sym N` of graded quasi-coherent
algebras (`symGradedAlgebra`).

References: Stacks 01CH (`Sym` is a functor on `O_X`-modules; Sym of quasi-coherent is quasi-coherent),
Bourbaki, Algebra III §6 no. 2 (functoriality of the symmetric algebra). Used for the fibres of
`P(O ⊕ L)`: `Sym(g^*V^∨) ≅ Sym(O^2)` from `g^*V^∨ ≅ O^2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Sym is functorial along isomorphisms.**

Proof: the graded-algebra isomorphism
`Modules.symGradedAlgebra_congr e : symGradedAlgebra V ≅ symGradedAlgebra W` is built
from the degreewise isomorphisms `symPowMapIso e m` (descended from the tensor-power maps
`monoidalPowMap e.hom m` along the coequaliser projection `symPowπ`), compatibility with
multiplication `symPowMul_symPowMap` and with the unit (`symPowπ_symPowMap` at `m = 0`), and
`GradedQCAlgebra.isoMk`; the `dite` in `symGradedAlgebra` lands in the same branch on both sides
because quasi-coherence is invariant under isomorphism (`isQuasicoherent_of_iso`). The
quasi-coherence hypotheses of this statement are therefore not used by the proof; they are kept
for the users of the statement.

References: Stacks 01CH (`Sym` is a functor on `O_X`-modules), Bourbaki, Algebra III §6 no. 2. -/
theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_iso_of_iso
    {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (e : M ≅ N) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra M ≅
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebra N) :=
  ⟨AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_congr e⟩

end
