import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.SchemeModulesEnoughInjectives
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLes
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.Stacks01eu
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAlternatingQuotientAcyclic
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.SheafHPrimeInjectiveModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHPrimeOneOfSurjective

/-! # Cartan's criterion (Stacks 01EW)

Cartan's criterion: let `B` be a basis of the topology and `Cov` a family of open covers such that
(1) the covers and all their finite intersections lie in `B`, (2) for every `U ∈ B` the covers of `U`
in `Cov` are cofinal among all open covers of `U`, (3) the Čech cohomology of `F` on every cover in
`Cov` vanishes in positive degrees. Then `H^p(U, F) = 0` for every `U ∈ B` and `p > 0`.

Source: Stacks 01EW.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks01ewAux

theorem iInf_eq_biInf {α : Type*} [CompleteLattice α] {n q : ℕ} (U : Fin n → α)
    (σ : Fin (q + 1) ↪o Fin n) :
    ⨅ k, U (σ k) = ⨅ i ∈ Finset.univ.map σ.toEmbedding, U i := by
  apply le_antisymm
  · refine le_iInf₂ fun i hi => ?_
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hi
    exact iInf_le _ k
  · exact le_iInf fun k => iInf₂_le (σ k) (Finset.mem_map_of_mem _ (Finset.mem_univ k))

end Stacks01ewAux

theorem sheafCohomology'_vanishing_of_cech_basis {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    (B : Set X.Opens) (hB : TopologicalSpace.Opens.IsBasis B)
    (Cov : X.Opens → Set (Σ n : ℕ, Fin n → X.Opens))
    (h₁ : ∀ U ∈ B, ∀ c ∈ Cov U, ⨆ i, c.2 i = U ∧ ∀ s : Finset (Fin c.1), s.Nonempty → (⨅ i ∈ s, c.2 i) ∈ B)
    /- (2) `Cov U` is cofinal among the open covers of `U`: every open cover of `U` is refined by
       some cover in `Cov U` -/
    (h₂ : ∀ U ∈ B, ∀ (ι : Type u) (V : ι → X.Opens), ⨆ j, V j = U →
      ∃ c ∈ Cov U, ∀ i, ∃ j, c.2 i ≤ V j)
    (h₃ : ∀ U ∈ B, ∀ c ∈ Cov U, ∀ p : ℕ, 0 < p →
      Subsingleton (((AlgebraicGeometry.Scheme.Modules.cechComplexAlt c.2 M).homology (p : ℤ)) : Type u))
    (U : X.Opens) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    Subsingleton (M.toAddCommGrpSheaf.H' p U) := by
  -- take an injective hull `M ↪ I` with quotient `Q`: `I(W) → Q(W)` is surjective for `W ∈ B`, and
  -- `Q` inherits hypothesis (3)
  have setup : ∀ (M : X.Modules),
      (∀ U ∈ B, ∀ c ∈ Cov U, ∀ p : ℕ, 0 < p → Subsingleton
        (((AlgebraicGeometry.Scheme.Modules.cechComplexAlt c.2 M).homology (p : ℤ)) : Type u)) →
      ∃ (S : ShortComplex X.Modules) (_ : S.ShortExact), S.X₁ = M ∧ Injective S.X₂ ∧
        (∀ W ∈ B, Function.Surjective (S.g.app W)) ∧
        (∀ U ∈ B, ∀ c ∈ Cov U, ∀ p : ℕ, 0 < p → Subsingleton
          (((AlgebraicGeometry.Scheme.Modules.cechComplexAlt c.2 S.X₃).homology (p : ℤ)) : Type u)) := by
    intro M h₃
    let S : ShortComplex X.Modules :=
      ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel (Injective.ι M)
        mono_f := inferInstanceAs (Mono (Injective.ι M))
        epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι M))) }
    have hinj : Injective S.X₂ := inferInstanceAs (Injective (Injective.under M))
    have hsurjB : ∀ W ∈ B, Function.Surjective (S.g.app W) := by
      intro W hW
      exact AlgebraicGeometry.Scheme.Modules.surjective_sections_of_cech_h1 S hS W (Cov W)
        (fun c hc => (h₁ W hW c hc).1) (h₂ W hW)
        (fun c hc => by simpa using h₃ W hW c hc 1 one_pos)
    refine ⟨S, hS, rfl, hinj, hsurjB, ?_⟩
    intro W hW c hc p hp
    refine AlgebraicGeometry.Scheme.Modules.cechComplexAlt_homology_subsingleton_of_shortExact
      c.2 S hS ?_ (h₃ W hW c hc) ?_ p hp
    · intro q σ
      apply hsurjB
      rw [Stacks01ewAux.iInf_eq_biInf]
      exact (h₁ W hW c hc).2 _ ⟨σ 0, Finset.mem_map_of_mem _ (Finset.mem_univ 0)⟩
    · intro p hp
      exact AlgebraicGeometry.Scheme.Modules.cechComplexAlt_homology_subsingleton_of_injective
        S.X₂ c.2 p hp
  have key : ∀ (p : ℕ) (M : X.Modules),
      (∀ U ∈ B, ∀ c ∈ Cov U, ∀ p : ℕ, 0 < p → Subsingleton
        (((AlgebraicGeometry.Scheme.Modules.cechComplexAlt c.2 M).homology (p : ℤ)) : Type u)) →
      ∀ U ∈ B, Subsingleton (M.toAddCommGrpSheaf.H' (p + 1) U) := by
    intro p
    induction p with
    | zero =>
      intro M h₃ U hU
      obtain ⟨S, hS, hX₁, hinj, hsurjB, -⟩ := setup M h₃
      subst hX₁
      exact AlgebraicGeometry.Scheme.Modules.hPrime_one_subsingleton_of_surjective S hS U
        (hsurjB U hU) (AlgebraicGeometry.Scheme.Modules.hPrime_subsingleton_of_injective S.X₂ U 1 one_pos)
    | succ p ih =>
      intro M h₃ U hU
      obtain ⟨S, hS, hX₁, hinj, hsurjB, hQ⟩ := setup M h₃
      subst hX₁
      have hT := bridge_shortExact_toSheaf
        (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) S.f S.g S.zero) hS
      exact SheafHPrimeAux.ext_succ hT _ (p + 1)
        (AlgebraicGeometry.Scheme.Modules.hPrime_subsingleton_of_injective S.X₂ U (p + 2) (by omega))
        (ih S.X₃ hQ U hU)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact key q M h₃ U hU

end
