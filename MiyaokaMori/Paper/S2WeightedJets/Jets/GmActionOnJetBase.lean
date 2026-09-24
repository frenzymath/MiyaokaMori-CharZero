import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Morphisms.GroupSchemeAction
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.MultiplicativeGroupScheme
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty

/-! # The `𝔾_m`-action on the jet base

The action `t ↦ λt` of `𝔾_m` on `Spec k[t]/(t^{k+1})` (parameter rescaling, §2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `(λ ⊗ t)^{r+1} = 0`: well-definedness of the coaction `jetBaseRescaling.coaction` (the `(r+1)`-st power of
`t` vanishes in `k[t]/(t^{r+1})`; take powers factorwise in the tensor product with
`Algebra.TensorProduct.tmul_pow`, then `TensorProduct.tmul_zero`). -/

theorem jetBaseRescaling.coaction_wellDefined (k : Type u) [Field k] (r : ℕ) :
    Polynomial.eval₂ (algebraMap k (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))
      (TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k)
        (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))
      ((Polynomial.X : Polynomial k) ^ (r + 1)) = 0 := by
  have h : (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))) ^ (r + 1) = 0 := by
    have := AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial k) ^ (r + 1))
    rwa [Polynomial.eval₂_pow, Polynomial.eval₂_X] at this
  rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, Algebra.TensorProduct.tmul_pow, h,
    TensorProduct.tmul_zero]

/-- The coaction `k[t]/(t^{r+1}) → k[λ^{±1}] ⊗_k k[t]/(t^{r+1})`, `t ↦ λ ⊗ t` (via `AdjoinRoot.lift`, using
`(λ ⊗ t)^{r+1} = 0`). -/

noncomputable def jetBaseRescaling.coaction (k : Type u) [Field k] (r : ℕ) :
    MiyaokaMori.Jet.TruncatedJetRing k r →+* TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r) :=
  AdjoinRoot.lift (algebraMap k (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))
    (TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k)
      (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))
    (jetBaseRescaling.coaction_wellDefined k r)

noncomputable def jetBaseRescaling (k : Type u) [Field k] (r : ℕ) :
    CategoryTheory.Limits.pullback (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ⟶ jetBase k r :=
  (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescaling.coaction k r))

end
