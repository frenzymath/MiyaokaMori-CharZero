import MiyaokaMori.Prelude
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Auxiliary finiteness lemmas for polynomial rings in characteristic `p`

Four small ring-theoretic facts used by the characteristic-`p` proof of "polynomial rings over a
field are N-2" (`Stacks035b_PolynomialN2.lean`, `Field.polynomialRingsN2_of_charP`):

* `RingHom.Finite.of_comp_injective`: if `φ ∘ ι` is a finite ring homomorphism, `φ` is injective
  and the base is Noetherian, then `ι` is finite (a submodule of a finite module over a Noetherian
  ring is finite, transported along `φ`);
* `MvPolynomial.expand_finite`: `k[x_1, …, x_d]` is finite over its image under `x_i ↦ x_i^q`
  (the monomials with exponents `< q` generate);
* `MvPolynomial.map_finite`: `MvPolynomial.map f` is finite when `f` is;
* `MvPolynomial.mem_range_map_of_coeff_mem_range`: a polynomial whose coefficients lie in the
  range of `f` lies in the range of `MvPolynomial.map f`.

-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v

noncomputable section

/-- (B) If `φ ∘ ι : R → B` is a finite ring homomorphism, `φ : A → B` is injective and `R` is
Noetherian, then `ι : R → A` is finite: `A` embeds `R`-linearly into the finite `R`-module `B`. -/
theorem RingHom.Finite.of_comp_injective {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [IsNoetherianRing R] (ι : R →+* A) (φ : A →+* B) (hφ : Function.Injective φ)
    (h : (φ.comp ι).Finite) : ι.Finite := by
  algebraize [ι, φ.comp ι]
  have hB : Module.Finite R B := h
  let f : A →ₗ[R] B :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun r a => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra,
          RingHom.algebraMap_toAlgebra, RingHom.comp_apply] }
  exact Module.Finite.of_injective f hφ

/-- (A1) `k[x_1..x_d]` is a finite module over its image under `expand q` (`x_i ↦ x_i^q`, `q > 0`):
the monomials with exponents `< q` generate. -/
theorem MvPolynomial.expand_finite (k : Type u) [CommRing k] (d q : ℕ) (hq0 : 0 < q) :
    ((MvPolynomial.expand q : MvPolynomial (Fin d) k →ₐ[k] MvPolynomial (Fin d) k) :
      MvPolynomial (Fin d) k →+* MvPolynomial (Fin d) k).Finite := by
  classical
  set P := MvPolynomial (Fin d) k with hP
  set σ : P →+* P := ((MvPolynomial.expand q : P →ₐ[k] P) : P →+* P) with hσ
  letI : Algebra P P := σ.toAlgebra
  letI : Module P P := Algebra.toModule
  let gen : (Fin d → Fin q) → P := fun I =>
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => ((I i : ℕ))) 1
  refine ⟨⟨Finset.univ.image gen, ?_⟩⟩
  rw [eq_top_iff]
  rintro a -
  refine MvPolynomial.induction_on' a ?_ ?_
  · intro J c
    let J' : (Fin d) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => J i / q
    let I : Fin d → Fin q := fun i => ⟨J i % q, Nat.mod_lt _ hq0⟩
    have hJ : J = q • J' + Finsupp.equivFunOnFinite.symm fun i => ((I i : ℕ)) := by
      ext i
      simp only [J', I, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Finsupp.coe_equivFunOnFinite_symm]
      exact (Nat.div_add_mod (J i) q).symm
    have key : MvPolynomial.monomial J c = σ (MvPolynomial.monomial J' c) * gen I := by
      rw [hσ]
      change MvPolynomial.monomial J c = MvPolynomial.expand q (MvPolynomial.monomial J' c) * gen I
      simp only [gen]
      rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_mul, mul_one, hJ]
    have hmem : gen I ∈ Submodule.span P ((Finset.univ.image gen : Finset P) : Set P) :=
      Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem gen (Finset.mem_univ I)))
    have h2 := Submodule.smul_mem (Submodule.span P ((Finset.univ.image gen : Finset P) : Set P))
      (MvPolynomial.monomial J' c) hmem
    rw [key]
    exact h2
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb

/-- (A2) If `f : k →+* k'` is a finite ring homomorphism, so is `MvPolynomial.map f`:
if `b_1, …, b_n` generate `k'` over `k`, the constants `C b_l` generate `k'[x]` over `k[x]`. -/
theorem MvPolynomial.map_finite {k : Type u} {k' : Type v} [CommRing k] [CommRing k']
    (f : k →+* k') (hf : f.Finite) (d : ℕ) :
    (MvPolynomial.map (σ := Fin d) f).Finite := by
  classical
  letI : Algebra k k' := f.toAlgebra
  have hfin : Module.Finite k k' := hf
  obtain ⟨s, hs⟩ := hfin.fg_top
  set P := MvPolynomial (Fin d) k with hP
  set P' := MvPolynomial (Fin d) k' with hP'
  set σ : P →+* P' := MvPolynomial.map f with hσ
  letI : Algebra P P' := σ.toAlgebra
  letI : Module P P' := Algebra.toModule
  refine ⟨⟨s.image MvPolynomial.C, ?_⟩⟩
  rw [eq_top_iff]
  rintro a -
  refine MvPolynomial.induction_on' a ?_ ?_
  · intro J c
    have hc : c ∈ Submodule.span k (s : Set k') := by rw [hs]; trivial
    obtain ⟨lam, -, hlam⟩ := Submodule.mem_span_finset.mp hc
    rw [← hlam, map_sum]
    refine Submodule.sum_mem _ fun b hb => ?_
    have key : MvPolynomial.monomial J (lam b • b)
        = σ (MvPolynomial.monomial J (lam b)) * MvPolynomial.C b := by
      rw [hσ, MvPolynomial.map_monomial, MvPolynomial.C_apply, MvPolynomial.monomial_mul, add_zero,
        Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    have hmem : MvPolynomial.C b ∈ Submodule.span P ((s.image MvPolynomial.C : Finset P') : Set P') :=
      Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hb))
    have h2 := Submodule.smul_mem (Submodule.span P ((s.image MvPolynomial.C : Finset P') : Set P'))
      (MvPolynomial.monomial J (lam b)) hmem
    rw [key]
    exact h2
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb

/-- (C) A multivariate polynomial all of whose coefficients lie in the range of `f` lies in the
range of `MvPolynomial.map f`. -/
theorem MvPolynomial.mem_range_map_of_coeff_mem_range {k : Type u} {k' : Type v} [CommRing k]
    [CommRing k'] (f : k →+* k') {σ : Type*} (a : MvPolynomial σ k')
    (h : ∀ m, MvPolynomial.coeff m a ∈ Set.range f) : a ∈ (MvPolynomial.map (σ := σ) f).range := by
  classical
  rw [MvPolynomial.as_sum a]
  refine Subring.sum_mem _ fun m _ => ?_
  obtain ⟨c, hc⟩ := h m
  exact ⟨MvPolynomial.monomial m c, by rw [MvPolynomial.map_monomial, hc]⟩

end
