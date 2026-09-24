import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.Stacks00op
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Krull dimension of a standard smooth algebra equals its relative dimension

A nonzero standard smooth algebra `S` of relative dimension `n` over a field `K`: **every maximal
ideal has height `n`**, hence `ringKrullDim S = n` (the algebraic core of Stacks 00T7(7); the same
holds for every nonzero localization of `S`, since it is again standard smooth of relative
dimension `n`).

Proof (not via the "relative global complete intersection" route of Stacks 00SP, and without
`dim = trdeg`):
1. `S` is étale over `P = K[X_1..X_n]` (Mathlib `exists_etale_mvPolynomial`);
2. every maximal ideal of `P` has height `n` (`MvPolynomial.height_eq_of_isMaximal`, module
   `Stacks00op`);
3. flat ⇒ going-down ⇒ `ht Q = ht 𝔭 + ht (image of Q in the fibre S/𝔭S)` (Mathlib height formula
   00ON); étale ⇒ quasi-finite ⇒ primes over the same `𝔭` are pairwise incomparable ⇒ the fibre term
   is `0`, so `ht Q = ht 𝔭`;
4. a maximal ideal `Q` of `S` pulls back to a maximal ideal of `P` (Jacobson + finite type), so
   `ht Q = n`.

References: Stacks 00T7(7), 00ON, 00OP.
-/

set_option autoImplicit false

universe u v

open Polynomial

/-- Going-down + quasi-finite: a prime above has the same height as the prime below (the fibre term
in the height formula 00ON is `0`). -/
theorem Ideal.height_eq_of_liesOver_of_hasGoingDown_of_quasiFinite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.HasGoingDown R S] [Algebra.QuasiFinite R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    P.height = p.height := by
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P]
  set I : Ideal S := p.map (algebraMap R S) with hI
  have hIP : I ≤ P := by
    rw [hI, Ideal.map_le_iff_le_comap]
    exact (P.over_def p).le
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hcm : (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hIP
  have hP' : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hIP)
  have h0 : (P.map (Ideal.Quotient.mk I)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨hP', bot_le⟩, fun J hJ hJP => ?_⟩
    have : J.IsPrime := hJ.1
    have hle : J.comap (Ideal.Quotient.mk I) ≤ P := by
      rw [← hcm]
      exact Ideal.comap_mono hJP
    have hunder : (J.comap (Ideal.Quotient.mk I)).under R = P.under R := by
      refine le_antisymm (Ideal.comap_mono hle) fun x hx => ?_
      have hxp : x ∈ p := by rw [P.over_def p]; exact hx
      have : algebraMap R S x ∈ I := Ideal.mem_map_of_mem _ hxp
      change Ideal.Quotient.mk I (algebraMap R S x) ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr this]
      exact J.zero_mem
    have heq := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) _ P hle hunder
    rw [← heq, Ideal.map_comap_of_surjective _ hsurj]
  rw [h0, add_zero]

/-- A nonzero étale algebra over the polynomial ring in `n` variables over a field: every maximal
ideal has height `n`. -/
theorem Algebra.Etale.height_eq_of_isMaximal_of_mvPolynomial
    {K : Type u} {S : Type v} [Field K] [CommRing S] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) K) S] [Algebra.Etale (MvPolynomial (Fin n) K) S]
    (Q : Ideal S) [Q.IsMaximal] : Q.height = n := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing (MvPolynomial (Fin n) K) S
  have : Module.Flat (MvPolynomial (Fin n) K) S := Algebra.Smooth.flat _ S
  have : Algebra.HasGoingDown (MvPolynomial (Fin n) K) S := Algebra.HasGoingDown.of_flat
  let _ : Field (S ⧸ Q) := Ideal.Quotient.field Q
  have : Algebra.FiniteType (MvPolynomial (Fin n) K) (S ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (MvPolynomial (Fin n) K) Q)
      (Ideal.Quotient.mkₐ_surjective _ Q)
  have : Module.Finite (MvPolynomial (Fin n) K) (S ⧸ Q) :=
    finite_of_finite_type_of_isJacobsonRing _ (S ⧸ Q)
  have : Algebra.IsIntegral (MvPolynomial (Fin n) K) (S ⧸ Q) := Algebra.IsIntegral.of_finite _ _
  have hcomap : (⊥ : Ideal (S ⧸ Q)).under (MvPolynomial (Fin n) K) =
      Q.under (MvPolynomial (Fin n) K) := by
    ext a
    change Ideal.Quotient.mk Q (algebraMap _ S a) = 0 ↔ algebraMap _ S a ∈ Q
    exact Ideal.Quotient.eq_zero_iff_mem
  have hmmax : (Q.under (MvPolynomial (Fin n) K)).IsMaximal := by
    rw [← hcomap]
    exact Ideal.IsMaximal.under _ (⊥ : Ideal (S ⧸ Q))
  have : Q.LiesOver (Q.under (MvPolynomial (Fin n) K)) := ⟨rfl⟩
  rw [Ideal.height_eq_of_liesOver_of_hasGoingDown_of_quasiFinite
    (Q.under (MvPolynomial (Fin n) K)) Q]
  exact MvPolynomial.height_eq_of_isMaximal n _

/-- A standard smooth algebra of relative dimension `n` over a field: every maximal ideal has height `n`. -/
theorem RingHom.IsStandardSmoothOfRelativeDimension.height_eq_of_isMaximal
    {K S : Type u} [Field K] [CommRing S] {n : ℕ} {f : K →+* S}
    (hf : f.IsStandardSmoothOfRelativeDimension n) (Q : Ideal S) [Q.IsMaximal] :
    Q.height = n := by
  obtain ⟨g, -, hg⟩ := hf.exists_etale_mvPolynomial
  let _ : Algebra (MvPolynomial (Fin n) K) S := g.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) K) S := hg.toAlgebra
  exact Algebra.Etale.height_eq_of_isMaximal_of_mvPolynomial (K := K) (n := n) Q

/-- The algebraic form of Stacks 00T7(7): a nonzero standard smooth algebra of relative dimension `n`
over a field has Krull dimension `n`. -/
theorem RingHom.IsStandardSmoothOfRelativeDimension.ringKrullDim_eq
    {K S : Type u} [Field K] [CommRing S] [Nontrivial S] {n : ℕ} {f : K →+* S}
    (hf : f.IsStandardSmoothOfRelativeDimension n) : ringKrullDim S = n := by
  rw [← Ideal.sup_isMaximal_height_eq_ringKrullDim]
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal S
  have key : (⨆ (I : Ideal S) (_ : I.IsMaximal), I.height) = (n : ℕ∞) := by
    refine le_antisymm (iSup₂_le fun I hI => ?_) ?_
    · have := hI
      exact (hf.height_eq_of_isMaximal I).le
    · have := hQ
      exact (hf.height_eq_of_isMaximal Q).ge.trans (le_iSup₂ (f := fun I _ => I.height) Q hQ)
  rw [key]
  rfl
