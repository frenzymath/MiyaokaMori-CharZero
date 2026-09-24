import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.GradedQCAlgebraIsoMk
import MiyaokaMori.AlgebraicGeometry.Modules.SymPowMap

/-! # Functoriality of the symmetric algebra sheaf in isomorphisms

An isomorphism of sheaves of modules `e : V ≅ W` induces an isomorphism of graded quasi-coherent
algebras `symGradedAlgebra V ≅ symGradedAlgebra W`.

Proof: `symGradedAlgebra` is a `dite` on "`V` is quasi-coherent". Quasi-coherence is invariant under
isomorphism (Mathlib: `isQuasicoherent` is an object property closed under isomorphisms), so `V` and
`W` fall into the same branch. In the true branch, `symGradedAlgebraOfQC V _ ≅ symGradedAlgebraOfQC W _`
is assembled by `GradedQCAlgebra.isoMk` from the piecewise isomorphisms `symPowMapIso e m`;
compatibility with multiplication is `symPowMul_symPowMap`, and with the unit (`= symPowπ V 0`) is
`symPowπ_symPowMap` at `m = 0` (`monoidalPowMap e.hom 0 = 𝟙`). In the false branch both sides are the
trivial graded algebra `GradedQCAlgebra.trivial X`. The two `dite` reductions are written as `eqToIso`
via `dif_pos` / `dif_neg`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Quasi-coherence is transported along isomorphisms (Mathlib: `SheafOfModules.isQuasicoherent` is closed
under isomorphisms). -/
theorem isQuasicoherent_of_iso {V W : X.Modules} (e : V ≅ W) (h : V.IsQuasicoherent) :
    W.IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf) e h

/-- For quasi-coherent `V`, `symGradedAlgebra V` is `symGradedAlgebraOfQC V h`. -/
theorem symGradedAlgebra_eq_ofQC (V : X.Modules) (h : V.IsQuasicoherent) :
    symGradedAlgebra V = symGradedAlgebraOfQC V h := dif_pos h

/-- For non-quasi-coherent `V`, `symGradedAlgebra V` is the trivial graded algebra. -/
theorem symGradedAlgebra_eq_trivial (V : X.Modules) (h : ¬ V.IsQuasicoherent) :
    symGradedAlgebra V = GradedQCAlgebra.trivial X := dif_neg h

/-- Quasi-coherent case: `Sym(V) ≅ Sym(W)` as graded algebras. -/
def symGradedAlgebraOfQC_congr {V W : X.Modules} (e : V ≅ W) (hV : V.IsQuasicoherent)
    (hW : W.IsQuasicoherent) : symGradedAlgebraOfQC V hV ≅ symGradedAlgebraOfQC W hW :=
  GradedQCAlgebra.isoMk (fun m => symPowMapIso e m) (fun m n => symPowMul_symPowMap e.hom m n)
    (by
      show symPowπ V 0 ≫ symPowMap e.hom 0 = symPowπ W 0
      rw [symPowπ_symPowMap]
      exact Category.id_comp _)

/-- General case: `Sym(V) ≅ Sym(W)` as graded algebras (both sides fall into the same branch of the `dite`). -/
def symGradedAlgebra_congr {V W : X.Modules} (e : V ≅ W) :
    symGradedAlgebra V ≅ symGradedAlgebra W :=
  @dite _ V.IsQuasicoherent (Classical.propDecidable _)
    (fun h =>
      eqToIso (symGradedAlgebra_eq_ofQC V h) ≪≫
        symGradedAlgebraOfQC_congr e h (isQuasicoherent_of_iso e h) ≪≫
        eqToIso (symGradedAlgebra_eq_ofQC W (isQuasicoherent_of_iso e h)).symm)
    (fun h =>
      eqToIso (symGradedAlgebra_eq_trivial V h) ≪≫
        eqToIso (symGradedAlgebra_eq_trivial W (fun h' => h (isQuasicoherent_of_iso e.symm h'))).symm)

end AlgebraicGeometry.Scheme.Modules

end
