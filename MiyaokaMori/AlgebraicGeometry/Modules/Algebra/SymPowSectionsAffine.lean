import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentAffineLocal
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesQuasicoherentClosure
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.BiproductSections

/-! # Sections of symmetric powers over an affine open are the coequalizer of the sections

**Stacks 01CG on an affine open**: for quasi-coherent `F` and affine `U`, the sections of the symmetric power
`symPow F e` (the wide coequaliser of the adjacent transpositions on `F^{⊗e}`, `SheafSymmetricAlgebra.lean`) are
the coequaliser of the sections: `(symPowπ F e).app U : Γ(U, F^{⊗e}) → Γ(U, Sym^e F)` is surjective, with kernel
the `Γ(U)`-span of the elements `transp_i x - x`.

Together with the bijectivity of `tensorSectionsHom` on affine opens (`Γ(U, F^{⊗e}) = Γ(U, F)^{⊗e}`) this says
`Γ(U, Sym^e F) = Sym^e_{Γ(U)} Γ(U, F)` (the `e`-th graded piece of `SymmetricAlgebra Γ(U) Γ(U, F)`, i.e. the quotient
of `Γ(U,F)^{⊗e}` by the transpositions).

Source: Stacks 01CG; exactness of `Γ(U, -)` on quasi-coherent modules over an affine `U` (Stacks 01XB / 01IB,
in the library as `Modules.gammaAffine_exact_iff`).

The kernel proof presents
`symPow F e` as the cokernel of `symPowRelations F e : ⨁_{i : Fin e} F^{⊗e} ⟶ F^{⊗e}` (`symPowπ_isCokernel`)
and applies `gammaAffine_exact_iff` to the resulting exact short complex.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry ZeroObject

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **Surjectivity of the symmetric-power quotient on sections over an affine open.**

Natural-language proof. `symPowπ F e : F^{⊗e} → Sym^e F` is a wide coequaliser projection, hence an epimorphism
(`symPowπ_epi`). Both `F^{⊗e} = monoidalPow F e` and `Sym^e F = symPow F e` are quasi-coherent
(`monoidalPow_isQuasicoherent`, `symPow_isQuasicoherent`). In the abelian category `X.Modules` the short complex
`F^{⊗e} → Sym^e F → 0` is exact (its `g` is `0` with `f` an epi, i.e. `Sym^e F → 0` has kernel `Sym^e F = im f`).
`Modules.gammaAffine_exact_iff` (exactness of `Γ(U, -)` on quasi-coherent modules over an affine `U`, proved in
`QuasicoherentAffineLocal.lean`) gives `Function.Exact ((symPowπ F e).app U) 0`, i.e. every section of `Sym^e F` on `U`
is in the image of `(symPowπ F e).app U`.

Edge cases: `e = 0`
(`symPow F 0 ≅ 𝟙_`, `π` an iso); `U = ⊥` (zero modules). -/
theorem symPowπ_app_surjective_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent] (e : ℕ)
    {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    Function.Surjective ((AlgebraicGeometry.Scheme.Modules.symPowπ F e).app U) := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.monoidalPow F e).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.monoidalPow_isQuasicoherent F ‹_› e
  have h2 : (AlgebraicGeometry.Scheme.Modules.symPow F e).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.symPow_isQuasicoherent F ‹_› e
  have h3 : (0 : X.Modules).IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.isQuasicoherent_zero X
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (AlgebraicGeometry.Scheme.Modules.symPowπ F e)
      (0 : AlgebraicGeometry.Scheme.Modules.symPow F e ⟶ 0) (comp_zero)
  have hS : S.Exact := (ShortComplex.exact_iff_epi S rfl).mpr
    (AlgebraicGeometry.Scheme.Modules.symPowπ_epi F e)
  have hex := (AlgebraicGeometry.Scheme.Modules.gammaAffine_exact_iff S).mp hS ⟨U, hU⟩
  intro y
  have h0 : (S.g.app U).hom y = 0 := by
    show ((0 : AlgebraicGeometry.Scheme.Modules.symPow F e ⟶ 0).app U).hom y = 0
    rw [AlgebraicGeometry.Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
  obtain ⟨x, hx⟩ := (hex y).mp h0
  exact ⟨x, hx⟩

/-- Composition acts on sections by composition of the actions (by definition). -/
private theorem comp_app_apply_aux {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (f ≫ g).app U x = g.app U (f.app U x) := rfl

/-- The relation morphism `δ : ⨁_{i : Fin e} F^{⊗e} ⟶ F^{⊗e}` with `i`-th component
`monoidalPowTransp F e i - 𝟙` (biproduct over the finite type `Fin e`; `X.Modules` is preadditive).
`symPow F e` is its cokernel (`symPowπ_isCokernel`). -/
def symPowRelations (F : X.Modules) (e : ℕ) :
    (⨁ fun _ : Fin e => AlgebraicGeometry.Scheme.Modules.monoidalPow F e) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow F e :=
  CategoryTheory.Limits.biproduct.desc fun i =>
    AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F e i - 𝟙 _

/-- `ι_i ≫ δ = transp_i - 𝟙`. -/
theorem ι_symPowRelations (F : X.Modules) (e : ℕ) (i : Fin e) :
    CategoryTheory.Limits.biproduct.ι (fun _ : Fin e => AlgebraicGeometry.Scheme.Modules.monoidalPow F e) i ≫
        symPowRelations F e =
      AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F e i - 𝟙 _ :=
  CategoryTheory.Limits.biproduct.ι_desc _ _

/-- `δ ≫ π = 0`: each `transp_i ≫ π = π` (`monoidalPowTransp_symPowπ`). -/
theorem symPowRelations_symPowπ (F : X.Modules) (e : ℕ) :
    symPowRelations F e ≫ AlgebraicGeometry.Scheme.Modules.symPowπ F e = 0 := by
  refine CategoryTheory.Limits.biproduct.hom_ext' _ _ fun i => ?_
  rw [← Category.assoc, ι_symPowRelations, Preadditive.sub_comp, Category.id_comp,
    AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_symPowπ F e i i.2, sub_self, comp_zero]

/-- **`symPowπ F e` is the cokernel of `δ`.** A morphism `k : F^{⊗e} ⟶ W` with `δ ≫ k = 0` satisfies
`transp_i ≫ k = k` for all `i` (compose with `ι_i`), hence descends along the wide coequaliser (`symPowDesc`,
`symPowπ_desc`); uniqueness because `π` is an epimorphism (`symPowπ_epi`). -/
def symPowπ_isCokernel (F : X.Modules) (e : ℕ) :
    CategoryTheory.Limits.IsColimit
      (CategoryTheory.Limits.CokernelCofork.ofπ (AlgebraicGeometry.Scheme.Modules.symPowπ F e)
        (symPowRelations_symPowπ F e)) :=
  CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ' _ _ fun k hk =>
    ⟨AlgebraicGeometry.Scheme.Modules.symPowDesc F e k fun i => by
        have h : CategoryTheory.Limits.biproduct.ι
            (fun _ : Fin e => AlgebraicGeometry.Scheme.Modules.monoidalPow F e) i ≫
              (symPowRelations F e ≫ k) =
            CategoryTheory.Limits.biproduct.ι
              (fun _ : Fin e => AlgebraicGeometry.Scheme.Modules.monoidalPow F e) i ≫ 0 := by
          rw [hk]
        rw [← Category.assoc, ι_symPowRelations, Preadditive.sub_comp, Category.id_comp, comp_zero,
          sub_eq_zero] at h
        exact h,
      AlgebraicGeometry.Scheme.Modules.symPowπ_desc F e k _⟩

/-- The short complex `⨁_i F^{⊗e} --δ--> F^{⊗e} --π--> Sym^e F` is exact. -/
theorem symPowRelations_shortComplex_exact (F : X.Modules) (e : ℕ) :
    (ShortComplex.mk (symPowRelations F e) (AlgebraicGeometry.Scheme.Modules.symPowπ F e)
      (symPowRelations_symPowπ F e)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (symPowπ_isCokernel F e)

/-- Sections of `π` kill every `transp_i x - x`. -/
theorem symPowπ_app_transp_sub (F : X.Modules) (e : ℕ) (U : X.Opens) (i : Fin e)
    (x : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow F e, U)) :
    (AlgebraicGeometry.Scheme.Modules.symPowπ F e).app U
      ((AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F e i).app U x - x) = 0 := by
  have h := congrArg (fun φ : (AlgebraicGeometry.Scheme.Modules.monoidalPow F e ⟶
      AlgebraicGeometry.Scheme.Modules.symPow F e) => φ.app U x)
    (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_symPowπ F e i i.2)
  simp only at h
  rw [map_sub, ← h]
  exact sub_self _

/-- **Kernel of the symmetric-power quotient on sections over an affine open**: `π_U y = 0` iff `y` is a
`Γ(U)`-linear combination of elements `transp_i x - x` (`i : Fin e`, `x ∈ Γ(U, F^{⊗e})`).

Natural-language proof. Let `δ : ⨁_{i : Fin e} F^{⊗e} → F^{⊗e}` be the morphism with `i`-th component
`monoidalPowTransp F e i - 𝟙` (biproduct over the finite type `Fin e`; `X.Modules` is preadditive).
1. **`symPowπ F e` is the cokernel of `δ`.** For any `k : F^{⊗e} → W`, `k ∘ transp_i = k` for all `i`
   iff `δ ≫ k = 0` (compare components: `ι_i ≫ δ ≫ k = (transp_i - 𝟙) ≫ k`). Hence the wide coequaliser of
   `{𝟙, transp_i}` (`symPow F e`, `symPowDesc`, `symPowπ_desc`) has the universal property of `coker δ`:
   the short complex `⨁_i F^{⊗e} --δ--> F^{⊗e} --π--> Sym^e F` is exact with `π` epi
   (`ShortComplex.exact_of_g_is_cokernel` / `Abelian.exact_iff_...` in Mathlib; or directly: the image of `δ` is the
   kernel of `π` because `π` is the coequaliser of the `transp_i` with `𝟙`).
2. **Quasi-coherence.** `⨁_i F^{⊗e}` is quasi-coherent (`isQuasicoherent_biproduct_of_fintype` with
   `monoidalPow_isQuasicoherent`), as are `F^{⊗e}` and `Sym^e F`.
3. **Exactness of sections.** `Modules.gammaAffine_exact_iff` gives `Function.Exact (δ.app U) ((symPowπ F e).app U)`:
   `π_U y = 0 ↔ ∃ z ∈ Γ(U, ⨁_i F^{⊗e}), δ_U z = y`.
4. **Identify the image of `δ_U`.** `Γ(U, ⨁_i F^{⊗e}) ≅ ∏_i Γ(U, F^{⊗e})` via
   the `π_i`, and `δ_U z = Σ_i ((transp_i)_U z_i - z_i)` (`δ = Σ_i π_i ≫ (transp_i - 𝟙)` by `biproduct.total`;
   `Hom.app` is additive). So the image of `δ_U` is the additive subgroup generated by the `transp_i x - x`, which is
   already a `Γ(U)`-submodule (each `(transp_i)_U` is `Γ(U)`-linear: `Hom.app_smul`), i.e. the span in the statement.

Edge cases: `e = 0` (no transpositions, span `∅ = ⊥`, and `π` is an isomorphism, kernel `0`); `e = 1`
(`transp 1 0 = 𝟙`, differences `0`, `π` iso).

Formalized along these lines: `symPowRelations` (= `δ`), `symPowπ_isCokernel` (step 1, via
`CokernelCofork.IsColimit.ofπ'` + `symPowDesc`), `symPowRelations_shortComplex_exact`
(`ShortComplex.exact_of_g_is_cokernel`), `isQuasicoherent_biproduct_of_fintype` (step 2), `gammaAffine_exact_iff`
(step 3), `biproduct_sections_total` + `ι_symPowRelations` (step 4); the converse by `Submodule.span_induction`
and `symPowπ_app_transp_sub`. -/
theorem symPowπ_app_eq_zero_iff_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent] (e : ℕ)
    {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow F e, U)) :
    (AlgebraicGeometry.Scheme.Modules.symPowπ F e).app U y = 0 ↔
      y ∈ Submodule.span Γ(X, U) (Set.range fun p : Fin e × Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow F e, U) =>
        (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp F e p.1).app U p.2 - p.2) := by
  constructor
  · intro hy
    let S : ShortComplex X.Modules :=
      ShortComplex.mk (symPowRelations F e) (AlgebraicGeometry.Scheme.Modules.symPowπ F e)
        (symPowRelations_symPowπ F e)
    have h1 : (⨁ fun _ : Fin e => AlgebraicGeometry.Scheme.Modules.monoidalPow F e).IsQuasicoherent :=
      AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct_of_fintype _ fun _ =>
        AlgebraicGeometry.Scheme.Modules.monoidalPow_isQuasicoherent F ‹_› e
    have h2 : (AlgebraicGeometry.Scheme.Modules.monoidalPow F e).IsQuasicoherent :=
      AlgebraicGeometry.Scheme.Modules.monoidalPow_isQuasicoherent F ‹_› e
    have h3 : (AlgebraicGeometry.Scheme.Modules.symPow F e).IsQuasicoherent :=
      AlgebraicGeometry.Scheme.Modules.symPow_isQuasicoherent F ‹_› e
    have hex := (AlgebraicGeometry.Scheme.Modules.gammaAffine_exact_iff S).mp
      (symPowRelations_shortComplex_exact F e) ⟨U, hU⟩
    obtain ⟨z, hz⟩ := (hex y).mp hy
    rw [← hz]
    show (symPowRelations F e).app U z ∈ _
    rw [biproduct_sections_total _ U z, map_sum]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span
      ⟨(j, (CategoryTheory.Limits.biproduct.π
        (fun _ : Fin e => AlgebraicGeometry.Scheme.Modules.monoidalPow F e) j).app U z), ?_⟩
    show _ = (symPowRelations F e).app U ((CategoryTheory.Limits.biproduct.ι
      (fun _ : Fin e => AlgebraicGeometry.Scheme.Modules.monoidalPow F e) j).app U _)
    rw [← comp_app_apply_aux, ι_symPowRelations, Hom.sub_app, Hom.id_app]
    rfl
  · intro hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨i, x⟩, rfl⟩ := hw
      exact symPowπ_app_transp_sub F e U i x
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul r a _ ha => rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul, ha, smul_zero]

end AlgebraicGeometry.Scheme.Modules

end
