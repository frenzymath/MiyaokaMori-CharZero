import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperInduction
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowSucc

/-! # Snapper's theorem (Stacks 0BEM)

The Snapper polynomial in its general form (Stacks 0BEM): for a proper scheme `X` over a field, a
coherent sheaf `F` and invertible sheaves `L_1, …, L_r`, the function
`(n_1, …, n_r) ↦ χ(X, F ⊗ L_1^{n_1} ⊗ ⋯ ⊗ L_r^{n_r})` is a numerical polynomial of total degree
`≤ dim Supp F`.

The theorem is assembled from:
* `exists_snapper_mvPolynomial_aux` (`SnapperInduction.lean`): the induction on `dim Supp F` for an
  abstract family of exponent line bundles `𝓜 i : ℤ → X.Modules` with `𝓜 i (n+1) ≅ 𝓜 i n ⊗ L i`;
* `zpow_succ_iso`: `L^{n+1} ≅ L^n ⊗ L`, so `𝓜 i n := L i ^ n` qualifies.
The statement's `foldl` is `twistList (fun i => L i ^ n i) (List.finRange r) F` by definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.exists_snapper_mvPolynomial {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules) [∀ i, (L i).IsLineBundle]
    (e : ℕ) (he : topologicalKrullDim (F.support) ≤ e) :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ e ∧
      ∀ n : Fin r → ℤ,
        (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            ((List.finRange r).foldl (fun (G : X.Modules) (i : Fin r) => G.tensor (L i ^ n i)) F) : ℚ)
          = MvPolynomial.eval (fun i => (n i : ℚ)) P :=
  AlgebraicGeometry.exists_snapper_mvPolynomial_aux (k := k) e X hX F he L (fun i n => L i ^ n)
    (fun i n => AlgebraicGeometry.Scheme.Modules.zpow_succ_iso (L i) n)

end
