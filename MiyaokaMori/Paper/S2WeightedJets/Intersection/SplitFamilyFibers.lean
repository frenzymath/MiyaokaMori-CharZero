import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.AdaptedFrameUpperTriangular
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOverPolynomialSections
import MiyaokaMori.Algebra.LambdaConjugateMatrix
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambda
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.TrivializationCocycleBiproduct
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.TrivializationCocycleIsMatrixCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.VectorBundleFamilyFromCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.VectorBundleFamilyFromCocycleSpec

/-! # Fibers of the splitting family

The conjugated family of vector bundles is `E` at `λ = 1` and `⊕_i Q_i` at `λ = 0` (Lemma 2.3
of the paper, "splitting the vector bundle").

Outline:
1. `exists_upperTriangular_cocycle`: a trivialization cocycle `g_{αα'}` adapted to the filtration is upper
   triangular, with diagonal entries the cocycles of the `Q_i`;
2. the conjugate by `Λ(λ)` has the explicit form `Matrix.lambdaConjugate` (entry `(i,j)` is `g_{ij} λ^{j-i}`),
   sent into `𝔸¹_C` by `polyHom`;
3. it is a matrix cocycle on `𝔸¹_C` (`isMatrixCocycle_lambdaConjugate_polyHom`; this needs the matrix cocycle
   condition `IsTrivializationCocycle.isMatrixCocycle` for `g` itself);
4. `bundleFamilyOfCocycle` glues the family `𝒱`, and `bundleFamilyOfCocycle_spec` gives local freeness and the two
   fibers: at `λ = 1`, `G(1) = g` (`lambdaConjugate_eval_one`) is a cocycle of `E`; at `λ = 0`,
   `G(0) = diag(g_ii)` (`lambdaConjugate_eval_zero`) is a cocycle of `⊕ Q_i` (`IsTrivializationCocycle.biproduct`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem bundleFamily_fibers {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {r : ℕ} (E : AlgebraicGeometry.VectorBundle C.toVariety) (hr : E.rank = r)
    (F : SubbundleFiltration E r) :
    ∃ 𝒱 : (AlgebraicGeometry.Scheme.affineLineOver C.toScheme).Modules,
      𝒱.IsLocallyFree ∧
      Nonempty (SheafOfModules.restrictToLambda 𝒱 (1 : k) ≅ E.toModules) ∧
      Nonempty (SheafOfModules.restrictToLambda 𝒱 (0 : k) ≅
        CategoryTheory.Limits.biproduct (fun i : Fin r => (F.lineQuotient i).toModules)) := by
  obtain ⟨ι, U, hU, g, hE, htri, hQ⟩ := exists_upperTriangular_cocycle E hr F
  have hg : IsMatrixCocycle U g := hE.isMatrixCocycle
  have hG := AlgebraicGeometry.Scheme.affineLineOver.isMatrixCocycle_lambdaConjugate_polyHom
    C.toScheme U g hg htri
  obtain ⟨hlf, hfib⟩ := bundleFamilyOfCocycle_spec U hU _ hG
  refine ⟨bundleFamilyOfCocycle U hU _ hG, hlf, ?_, ?_⟩
  · refine hfib 1 E.toModules g hE fun α α' => ?_
    show ((g α α').lambdaConjugate.map
        (AlgebraicGeometry.Scheme.affineLineOver.polyHom C.toScheme (U α ⊓ U α'))).map
      (AlgebraicGeometry.Scheme.affineLineOver.evalAt C.toScheme 1 (U α ⊓ U α')) = g α α'
    rw [AlgebraicGeometry.Scheme.affineLineOver.matrix_map_polyHom_evalAt,
      AlgebraicGeometry.Scheme.affineLineOver.constAt_one, Matrix.lambdaConjugate_eval_one]
  · refine hfib 0 _ (fun α α' => Matrix.diagonal fun a => g α α' a a)
      (IsTrivializationCocycle.biproduct (fun i => (F.lineQuotient i).toModules) U
        (fun α α' i => g α α' i i) hQ) fun α α' => ?_
    show ((g α α').lambdaConjugate.map
        (AlgebraicGeometry.Scheme.affineLineOver.polyHom C.toScheme (U α ⊓ U α'))).map
      (AlgebraicGeometry.Scheme.affineLineOver.evalAt C.toScheme 0 (U α ⊓ U α')) =
      Matrix.diagonal fun a => g α α' a a
    rw [AlgebraicGeometry.Scheme.affineLineOver.matrix_map_polyHom_evalAt,
      AlgebraicGeometry.Scheme.affineLineOver.constAt_zero,
      Matrix.lambdaConjugate_eval_zero _ (htri α α')]

end
