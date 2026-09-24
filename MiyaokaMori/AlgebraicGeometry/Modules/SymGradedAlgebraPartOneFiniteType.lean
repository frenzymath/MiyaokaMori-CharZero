import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra

/-! # The degree-one part of the symmetric algebra is of finite type

Statement: for a quasi-coherent `O_X`-module `V` of finite type, the degree-one part `Sym^1 V` of
`symGradedAlgebra V` is of finite type.

Proof:
1. `V` quasi-coherent ⇒ `symGradedAlgebra V = symGradedAlgebraOfQC V _` (`dif_pos`), so part 1 is
   `symPow V 1`.
2. `symPowπ V 1 : monoidalPow V 1 → symPow V 1` is an epimorphism (`symPowπ_epi`), and
   `monoidalPow V 1 = 𝟙_ ⊗ V ≅ V` (`λ_ V`), so there is an epimorphism `V → Sym^1 V`.
3. Finite type is preserved by epimorphic images: given `x`, `exists_epi_free_pullback_of_isFiniteType V x`
   gives an open `U ∋ x`, a finite `I` and an epi `O_U^{⊕I} → V|_U`; compose with the pullback of the epi
   `V → Sym^1 V` (pullback along `U.ι` preserves epis, being a left adjoint / `Scheme.Modules.pullback`
   preserves colimits) to get an epi `O_U^{⊕I} → (Sym^1 V)|_U`; conclude with
   `isFiniteType_of_epi_free_pullback`.

Reference: Stacks 01B4 (finite type, local criterion). Used to show that `P(V) → X` is a projective
morphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_part_one_isFiniteType
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [hV : V.IsQuasicoherent] [V.IsFiniteType] :
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).part 1).IsFiniteType := by
  have hE : AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V =
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC V hV := by
    delta AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    exact dif_pos hV
  rw [hE]
  change (AlgebraicGeometry.Scheme.Modules.symPow V 1).IsFiniteType
  let q : V ⟶ AlgebraicGeometry.Scheme.Modules.symPow V 1 :=
    (λ_ V).inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ V 1
  have hq : Epi q :=
    @epi_comp _ _ _ _ _ (λ_ V).inv (IsIso.epi_of_iso _)
      (AlgebraicGeometry.Scheme.Modules.symPowπ V 1)
      (AlgebraicGeometry.Scheme.Modules.symPowπ_epi V 1)
  refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback _ fun x => ?_
  obtain ⟨U, J, hJ, π, hxU, hπ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType V x
  let F : X.Modules ⥤ U.toScheme.Modules := AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι
  let P : X.Modules ⥤ U.toScheme.Modules := AlgebraicGeometry.Scheme.Modules.pullback U.ι
  have hpres : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (AlgebraicGeometry.Scheme.Modules.restrictAdjunction U.ι)
  have hFq : Epi (F.map q) := @Functor.map_epi _ _ _ _ F hpres _ _ q hq
  let α := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hnat : F.map q ≫ α.hom.app (AlgebraicGeometry.Scheme.Modules.symPow V 1) =
      α.hom.app V ≫ P.map q := α.hom.naturality q
  have hcomp : Epi (α.hom.app V ≫ P.map q) := by
    rw [← hnat]
    exact @epi_comp _ _ _ _ _ (F.map q) hFq
      (α.hom.app (AlgebraicGeometry.Scheme.Modules.symPow V 1)) (IsIso.epi_of_iso _)
  have hpull : Epi (P.map q) := @epi_of_epi _ _ _ _ _ (α.hom.app V) (P.map q) hcomp
  exact ⟨U, J, hJ, π ≫ P.map q, hxU, @epi_comp _ _ _ _ _ π hπ (P.map q) hpull⟩

end
