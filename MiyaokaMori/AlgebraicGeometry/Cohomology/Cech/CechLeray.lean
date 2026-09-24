import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAltH0
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHPrimeSections
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyShift
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.SchemeModulesEnoughInjectives
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.Stacks01eu

/-! # Leray's theorem for the alternating Čech complex

Leray's theorem (Stacks 01ET, Hartshorne Ex. III.4.11): let `U : Fin n → X.Opens` cover `X` and `M`
be an `O_X`-module with `H^p(U_σ, M) = 0` for every strictly increasing index tuple `σ` and every
`p > 0` (`U_σ = ⋂_k U_{σ_k}`). Then `H^i(X, M) ≃ Ȟ^i_alt(U, M)` (`Γ(X, O_X)`-linearly) for all `i`.
Only the alternating (ordered) Čech complex is used; neither the full Čech complex nor a spectral
sequence.

Proof (the proof of Hartshorne III.4.5, p. 222, with the flasque quasi-coherent sheaf `G` replaced by
an injective `O_X`-module `I` and "`F` quasi-coherent" replaced by "`F` acyclic on each `U_σ`", so no
Noetherian hypothesis is needed): induction on `i`, for all `M` at once.
1. `i = 0`: `Ȟ^0 = Γ(X, M)` (III.4.1, `cechAlt_homologyZero_equiv_sections`) `= H^0(X, M)`
   (`sheafCohomologyZeroEquiv`).
2. Choose `0 → M → I → R → 0` with `I` injective. `H^1(U_σ, M) = 0` ⇒ `I(U_σ) → R(U_σ)` surjective
   (`surjective_sections_of_hPrime_one`), so `0 → C(M) → C(I) → C(R) → 0` is a short exact sequence of
   complexes (`cechShortComplex_shortExact`); `I` injective ⇒ flasque ⇒ `Ȟ^p(I) = 0` for `p > 0`
   (`cechComplexAlt_homology_subsingleton_of_injective`, III.4.3) and `H^p(X, I) = 0`.
3. `i = 1`: both sides are `coker(Γ(I) → Γ(R))` (Čech side: long exact homology sequence + naturality
   of step 1; derived side: `sheafCohomology.one_equiv_quotient`).
4. `i ≥ 2`: `Ȟ^i(M) ≅ Ȟ^{i-1}(R)` (Mathlib `ShortExact.δIso`) and `H^i(X, M) ≅ H^{i-1}(X, R)`
   (`sheafCohomology.δ_bijective`); `R` still satisfies the hypothesis
   (`hPrime_subsingleton_quotient`), so the induction hypothesis applies to `R`.

Source: Hartshorne III.4.5 (p. 222); the statement is Stacks 01ET = Hartshorne Ex. III.4.11.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens)

/-- Čech side, `i = 1`: `Ȟ^1(F) ≃ Γ(R)/im Γ(I)`, provided the sequence of Čech complexes is short
exact and `Ȟ^1(I) = 0`. -/
theorem cechAlt_homologyOne_equiv_quotient (hcov : ⨆ i, U i = ⊤) (S : ShortComplex X.Modules)
    (hT : (cechShortComplex U S).ShortExact)
    (h2 : Subsingleton (((cechComplexAlt U S.X₂).homology (1 : ℤ)) : Type u)) :
    Nonempty (((cechComplexAlt U S.X₁).homology (1 : ℤ)) ≃ₗ[Γ(X, ⊤)]
      (Γ(S.X₃, ⊤) ⧸ LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g))) := by
  have hz : IsZero ((cechShortComplex U S).X₂.homology 1) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ h2
  have hepi : Epi (hT.δ 0 1 rfl) := hT.epi_δ 0 1 rfl hz
  have hex := (hT.homology_exact₃ 0 1 rfl).moduleCat_range_eq_ker
  obtain ⟨e₂, e₃, he⟩ := cechAlt_homologyZero_equiv_sections U hcov S.g
  exact LinearMap.nonempty_equiv_quotient_of_exact
    (HomologicalComplex.homologyMap (cechComplexAltMap U S.g) 0).hom (hT.δ 0 1 rfl).hom
    ((ModuleCat.epi_iff_surjective _).1 hepi) hex e₂ e₃ (Scheme.Modules.Hom.appTopLinear S.g) he

/-- Čech side, `i ≥ 2`: `Ȟ^p(R) ≃ Ȟ^{p+1}(F)`, provided the sequence of Čech complexes is short exact
and `Ȟ^p(I) = Ȟ^{p+1}(I) = 0`. -/
theorem cechAlt_homology_shift (S : ShortComplex X.Modules)
    (hT : (cechShortComplex U S).ShortExact) (p : ℕ)
    (h2 : Subsingleton (((cechComplexAlt U S.X₂).homology ((p : ℕ) : ℤ)) : Type u))
    (h2' : Subsingleton (((cechComplexAlt U S.X₂).homology (((p + 1 : ℕ)) : ℤ)) : Type u)) :
    Nonempty (((cechComplexAlt U S.X₃).homology ((p : ℕ) : ℤ)) ≃ₗ[Γ(X, ⊤)]
      ((cechComplexAlt U S.X₁).homology (((p + 1 : ℕ)) : ℤ))) :=
  ⟨(hT.δIso ((p : ℕ) : ℤ) (((p + 1 : ℕ)) : ℤ) (by simp)
    (@ModuleCat.isZero_of_subsingleton _ _ _ h2)
    (@ModuleCat.isZero_of_subsingleton _ _ _ h2')).toLinearEquiv⟩

/-- **Leray's theorem (alternating Čech complex version)**: if `M` is acyclic on all finite
intersections of the cover, then `H^i(X, M) ≃ Ȟ^i_alt(U, M)`, `Γ(X, O_X)`-linearly. -/
theorem sheafCohomology_equiv_cechAlt_homology (hcov : ⨆ i, U i = ⊤) (i : ℕ) :
    ∀ (M : X.Modules),
      (∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n) (p : ℕ), 0 < p →
        Subsingleton (M.toAddCommGrpSheaf.H' p (⨅ k, U (σ k)))) →
      Nonempty (AlgebraicGeometry.sheafCohomology X M i ≃ₗ[Γ(X, ⊤)]
        ((cechComplexAlt U M).homology ((i : ℕ) : ℤ))) := by
  induction i with
  | zero =>
    intro M _
    obtain ⟨e, -, -⟩ := cechAlt_homologyZero_equiv_sections U hcov (𝟙 M)
    exact ⟨(sheafCohomologyZeroEquiv M).trans e.symm⟩
  | succ i ih =>
    intro M hM
    -- `0 → M → I → R → 0` with `I` injective
    let S : ShortComplex X.Modules :=
      ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel (Injective.ι M)
        mono_f := inferInstanceAs (Mono (Injective.ι M))
        epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι M))) }
    have hinj : Injective S.X₂ := inferInstanceAs (Injective (Injective.under M))
    have hsurj : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n),
        Function.Surjective (S.g.app (⨅ k, U (σ k))) := fun q σ =>
      surjective_sections_of_hPrime_one S hS _ (hM q σ 1 one_pos)
    have hT := cechShortComplex_shortExact U S hS hsurj
    have hR : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n) (p : ℕ), 0 < p →
        Subsingleton (S.X₃.toAddCommGrpSheaf.H' p (⨅ k, U (σ k))) := fun q σ p hp =>
      hPrime_subsingleton_quotient S hS _ p (hPrime_subsingleton_of_injective S.X₂ _ p hp)
        (hM q σ (p + 1) (Nat.succ_pos p))
    have hCI : ∀ p : ℕ, 0 < p →
        Subsingleton (((cechComplexAlt U S.X₂).homology ((p : ℕ) : ℤ)) : Type u) := fun p hp =>
      cechComplexAlt_homology_subsingleton_of_injective S.X₂ U p hp
    have hDI : ∀ p : ℕ, Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ (p + 1)) := fun p =>
      AlgebraicGeometry.sheafCohomology.subsingleton_of_injective S.X₂ p
    cases i with
    | zero =>
      have := hDI 0
      obtain ⟨d⟩ := AlgebraicGeometry.sheafCohomology.one_equiv_quotient hS
      obtain ⟨c⟩ := cechAlt_homologyOne_equiv_quotient U hcov S hT (hCI 1 one_pos)
      exact ⟨d.trans c.symm⟩
    | succ j =>
      have := hDI j
      have := hDI (j + 1)
      obtain ⟨r⟩ := ih S.X₃ hR
      obtain ⟨c⟩ := cechAlt_homology_shift U S hT (j + 1) (hCI (j + 1) (Nat.succ_pos j))
        (hCI (j + 1 + 1) (Nat.succ_pos _))
      let d := LinearEquiv.ofBijective _
        (AlgebraicGeometry.sheafCohomology.δ_bijective hS (j + 1) (j + 1 + 1) rfl)
      exact ⟨d.symm.trans (r.trans c)⟩

end AlgebraicGeometry.Scheme.Modules

end
