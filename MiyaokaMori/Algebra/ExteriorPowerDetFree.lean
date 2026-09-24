import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Exact.Basic
import MiyaokaMori.Algebra.TopExteriorBasis

/-! # Multiplicativity of the determinant for split short exact sequences of free modules

Multiplicativity of the determinant (top exterior power) for **split** short exact sequences of
**free** modules: the free special case of Stacks 0FJB.

The sheaf-level statement `det G ≅ det F ⊗ det H` for a short exact sequence of locally free sheaves
is checked locally on open sets where `F`, `H` are free and the sequence splits; the algebraic facts
needed there are the ones in this file. The general form (finite projective modules of constant rank,
`Module.exteriorPower_det_shortExact`, via the graded decomposition of the exterior algebra of a
direct sum) is not needed for that.

Reference: Stacks 0FJB (statement of the general form). The proof in the free case uses only that
the top exterior power of a free module of rank `n` is free of rank 1 with basis `e_1 ∧ … ∧ e_n`, a
direct consequence of Mathlib's `Module.Basis.exteriorPower` (the top-degree index set
`Set.powersetCard (Fin n) n` has the single element `Finset.univ`), packaged as the explicit linear
isomorphism `MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv`.

Proof sketch:
* Higher exterior powers of a free module of rank `a` vanish: `⋀^n M` has a basis indexed by
  `Set.powersetCard (Fin a) n` (the `n`-element subsets of the index set); for `n > a` there are
  none, so `⋀^n M = 0`.
* Multiplicativity for free modules: `⋀^a M′ ≅ R` (basis `e_1∧…∧e_a`), `⋀^b M″ ≅ R` (basis
  `h_1∧…∧h_b`), `⋀^{a+b} M ≅ R` (basis the top wedge of the given basis of `M`). Hence
  `⋀^a M′ ⊗ ⋀^b M″ ≅ R ⊗ R ≅ R ≅ ⋀^{a+b} M`. When the basis of `M` is the concatenation of the bases
  of `M′` and `M″` (`Basis.prod` reindexed along `finSumFinEquiv`), this composite sends
  `(e_1∧…∧e_a) ⊗ (h_1∧…∧h_b)` to `e_1∧…∧e_a∧h_1∧…∧h_b`, i.e. it is the wedge map. The graded
  decomposition `Λ(M′ ⊕ M″) ≅ Λ M′ ⊗ Λ M″` (not in Mathlib) is **not** needed.
-/

universe u v

open scoped TensorProduct

noncomputable section

/-- The exterior power of degree `n > a` of a free module of rank `a` vanishes (the algebraic core of
`Λ^{a+1} F = 0` for a locally free sheaf `F` of rank `a`).

Proof: `b.exteriorPower n : Basis (Set.powersetCard (Fin a) n) R (⋀[R]^n M)`; any
`s : Set.powersetCard (Fin a) n` would satisfy `s.card = n` and `s.card ≤ Fintype.card (Fin a) = a < n`,
a contradiction, so the index type is empty; `Finsupp` on an empty index type is a subsingleton,
transported back along `Basis.repr`. -/
theorem Module.exteriorPower_subsingleton_of_basis_of_lt {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] {a n : ℕ} (b : Module.Basis (Fin a) R M) (h : a < n) :
    Subsingleton (⋀[R]^n M) := by
  have : IsEmpty (Set.powersetCard (Fin a) n) := by
    constructor
    intro s
    have h2 := Finset.card_le_univ s.val
    have h1 : s.val.card = n := s.prop
    simp only [Fintype.card_fin, h1] at h2
    omega
  have : Subsingleton ((Set.powersetCard (Fin a) n) →₀ R) :=
    ⟨fun x y => Finsupp.ext (fun i => isEmptyElim i)⟩
  exact (b.exteriorPower n).repr.toEquiv.subsingleton

/-- Multiplicativity of the determinant, **given bases**: if `M′` is free of rank `a`, `M″` free of
rank `b` and `M` free of rank `a + b`, then `⋀^a M′ ⊗ ⋀^b M″ ≅ ⋀^{a+b} M`.

No relation between the three bases is required: all three top exterior powers are free of rank 1,
so an isomorphism always exists. To obtain the "wedge" isomorphism `(e_I) ⊗ (h_J) ↦ e_I ∧ h_J`, take
`eM := ((e'.prod e'').reindex finSumFinEquiv).map …`; see the two corollaries below.

Reference: the free case of Stacks 0FJB; the only fact used is that the top exterior power is `≅ R`
(`MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv`). -/
def Module.exteriorPowerDetEquivOfBasis {R : Type u} [CommRing R] {M' M'' M : Type v}
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    [AddCommGroup M] [Module R M] {a b : ℕ}
    (e' : Module.Basis (Fin a) R M') (e'' : Module.Basis (Fin b) R M'')
    (eM : Module.Basis (Fin (a + b)) R M) :
    (↥(⋀[R]^a M') ⊗[R] ↥(⋀[R]^b M'')) ≃ₗ[R] ↥(⋀[R]^(a + b) M) :=
  (TensorProduct.congr (MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv e')
      (MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv e'')).trans
    ((TensorProduct.lid R R).trans
      (MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv eM).symm)

/-- The isomorphism above is the "wedge" map: it sends `(e_1∧…∧e_a) ⊗ (h_1∧…∧h_b)` to the top wedge
of `eM`. When `eM` is the concatenation of `e'` and `e''`, the right side is `e_1∧…∧e_a∧h_1∧…∧h_b`. -/
@[simp]
theorem Module.exteriorPowerDetEquivOfBasis_wedge {R : Type u} [CommRing R] {M' M'' M : Type v}
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    [AddCommGroup M] [Module R M] {a b : ℕ}
    (e' : Module.Basis (Fin a) R M') (e'' : Module.Basis (Fin b) R M'')
    (eM : Module.Basis (Fin (a + b)) R M) :
    Module.exteriorPowerDetEquivOfBasis e' e'' eM
        (exteriorPower.ιMulti R a e' ⊗ₜ[R] exteriorPower.ιMulti R b e'') =
      exteriorPower.ιMulti R (a + b) eM := by
  simp only [Module.exteriorPowerDetEquivOfBasis, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv_basis_wedge,
    TensorProduct.lid_tmul, smul_eq_mul, mul_one,
    MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv_symm_apply, one_smul]

theorem Module.exteriorPower_det_of_basis {R : Type u} [CommRing R] {M' M'' M : Type v}
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    [AddCommGroup M] [Module R M] {a b : ℕ}
    (e' : Module.Basis (Fin a) R M') (e'' : Module.Basis (Fin b) R M'')
    (eM : Module.Basis (Fin (a + b)) R M) :
    Nonempty ((↥(⋀[R]^a M') ⊗[R] ↥(⋀[R]^b M'')) ≃ₗ[R] ↥(⋀[R]^(a + b) M)) :=
  ⟨Module.exteriorPowerDetEquivOfBasis e' e'' eM⟩

/-- Multiplicativity of the determinant, **direct sum / split** form: if `M ≅ M′ × M″` with `M′`, `M″`
free of ranks `a`, `b`, then `⋀^a M′ ⊗ ⋀^b M″ ≅ ⋀^{a+b} M`.

Proof: `M′ × M″` has the basis `e' ⊕ e''` (`Basis.prod`, reindexed to `Fin (a+b)` along
`finSumFinEquiv`); transport it to `M` along `eq.symm` and apply `Module.exteriorPower_det_of_basis`. -/
theorem Module.exteriorPower_det_of_linearEquivProd {R : Type u} [CommRing R] {M' M'' M : Type v}
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    [AddCommGroup M] [Module R M] {a b : ℕ}
    (e' : Module.Basis (Fin a) R M') (e'' : Module.Basis (Fin b) R M'')
    (eq : M ≃ₗ[R] M' × M'') :
    Nonempty ((↥(⋀[R]^a M') ⊗[R] ↥(⋀[R]^b M'')) ≃ₗ[R] ↥(⋀[R]^(a + b) M)) :=
  Module.exteriorPower_det_of_basis e' e'' (((e'.prod e'').reindex finSumFinEquiv).map eq.symm)

/-- Multiplicativity of the determinant, **split short exact sequence** form: if
`0 → M′ →f M →g M″ → 0` is exact with `f` injective and `σ` a section of `g`, and `M′`, `M″` are free
of ranks `a`, `b`, then `⋀^a M′ ⊗ ⋀^b M″ ≅ ⋀^{a+b} M`.

This is the exact shape needed for the local check of `det G ≅ det F ⊗ det H` on open sets where
`F`, `H` are free and the sequence splits.

Proof: `Function.Exact.splitSurjectiveEquiv` turns the section `σ` into `M ≃ₗ M′ × M″`; then apply
`Module.exteriorPower_det_of_linearEquivProd`. (`Function.Exact f g` means
`LinearMap.range f = LinearMap.ker g`, see `LinearMap.exact_iff`.) -/
theorem Module.exteriorPower_det_of_splitExact {R : Type u} [CommRing R] {M' M'' M : Type v}
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    [AddCommGroup M] [Module R M] {a b : ℕ}
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''} (hexact : Function.Exact f g)
    (hf : Function.Injective f) (σ : M'' →ₗ[R] M) (hσ : g ∘ₗ σ = LinearMap.id)
    (e' : Module.Basis (Fin a) R M') (e'' : Module.Basis (Fin b) R M'') :
    Nonempty ((↥(⋀[R]^a M') ⊗[R] ↥(⋀[R]^b M'')) ≃ₗ[R] ↥(⋀[R]^(a + b) M)) :=
  Module.exteriorPower_det_of_linearEquivProd e' e'' (hexact.splitSurjectiveEquiv hf ⟨σ, hσ⟩).1

end
