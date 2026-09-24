import MiyaokaMori.Prelude
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
import Mathlib.RingTheory.RegularLocalRing.Defs
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nq
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nu
import MiyaokaMori.RingTheory.RegularLocalRing.ProjectiveDimensionTools
import MiyaokaMori.RingTheory.RegularLocalRing.PdChangeOfRingsQuotient
import MiyaokaMori.RingTheory.RegularLocalRing.NagataRetraction

/-! # Finite projective dimension of the residue field implies regularity

**Serre's theorem, the hard direction of Stacks 00OC** ((1) ⇒ (3): a Noetherian local ring whose
residue field has finite projective dimension is regular).

Route: **not** the Stacks proof via 00OA/00OB (Koszul complex, Buchsbaum–Eisenbud), but
Matsumura, *Commutative Ring Theory*, Theorem 19.2 (with Nagata's lemma), reorganised as an
induction on `e = spanFinrank 𝔪` (the embedding dimension) instead of on `depth R` — the case
split "`depth R = 0` or not" is exactly "`𝔪` consists of zero divisors or not", and in the second
case the embedding dimension of `R/(x)` drops by one, so no notion of depth is needed.

Proof (all steps are formalised below or in the imported modules):
1. (`IsLocalRing.exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors`) If `𝔪` contains a
   nonzerodivisor, it contains one outside `𝔪²`: prime avoidance (Stacks 00DS, Mathlib
   `Ideal.subset_union_prime`) applied to `𝔪²` and the finitely many associated primes of `R`
   (whose union is the set of zero divisors, Mathlib `biUnion_associatedPrimes_eq_compl_nonZeroDivisors`):
   `𝔪 ⊄ 𝔪²` (else `𝔪 = 0`, `R` a field, no nonzerodivisor in `𝔪`), and `𝔪 ⊄ 𝔭 ∈ Ass R` (else
   `𝔪 = 𝔭` consists of zero divisors).
2. (`IsLocalRing.isField_of_hasProjectiveDimensionLE_residueField_of_forall_notMem_nonZeroDivisors`)
   If every element of `𝔪` is a zero divisor and `pd κ < ∞`, then `R` is a field: prime avoidance
   gives `𝔪 ⊆ 𝔭 ∈ Ass R`, so `𝔪 = 𝔭 = Ann(y)` with `y ≠ 0`; by the depth-zero lemma
   (`IsLocalRing.free_of_hasProjectiveDimensionLE_of_mul_maximalIdeal_eq_zero`) `κ` is a free
   `R`-module, and a nonzero free module is faithful while `𝔪 κ = 0`, so `𝔪 = 0`.
3. (`IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField`) Induction on `e` with
   `spanFinrank 𝔪 ≤ e`. If `e = 0` or `𝔪` consists of zero divisors, `R` is a field by (2), hence
   regular. Otherwise take `x ∈ 𝔪 ∖ 𝔪²` a nonzerodivisor (1), `R̄ = R/(x)`. From `pd_R κ ≤ n` we get
   `pd_R 𝔪 ≤ n` (dimension shift), then `pd_{R̄} (𝔪/x𝔪) ≤ n` (change of rings,
   `ModuleCat.hasProjectiveDimensionLE_quotSMulTop_of_isSMulRegular`), then `pd_{R̄} 𝔪̄ ≤ n` for
   `𝔪̄ = 𝔪R̄` since `𝔪̄` is a retract of `𝔪/x𝔪` (Nagata,
   `IsLocalRing.exists_retraction_quotSMulTop_maximalIdeal`), so `pd_{R̄} κ ≤ n + 1`. As
   `spanFinrank 𝔪̄ + 1 ≤ spanFinrank 𝔪` (`x ∉ 𝔪²`, Stacks 00NQ), induction gives `R̄`
   regular, and Stacks 00NU (
   `IsRegularLocalRing.of_quotient_span_singleton_of_mem_nonZeroDivisors`) gives `R` regular.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory IsLocalRing

noncomputable section

/-- **Prime avoidance step**: if the maximal ideal of a Noetherian local ring contains a
nonzerodivisor, it contains a nonzerodivisor outside `𝔪²` (Stacks 00DS applied to `𝔪²` and the
associated primes of `R`). -/
theorem IsLocalRing.exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : ∃ z ∈ maximalIdeal R, z ∈ nonZeroDivisors R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ x ∈ nonZeroDivisors R := by
  classical
  obtain ⟨z, hz, hz0⟩ := h
  by_contra hcon
  push Not at hcon
  have hfin := associatedPrimes.finite R R
  set s : Finset (Ideal R) := insert (maximalIdeal R ^ 2) hfin.toFinset with hs
  have hsub : ((maximalIdeal R : Ideal R) : Set R) ⊆ ⋃ i ∈ (↑s : Set (Ideal R)), (i : Set R) := by
    intro x hx
    by_cases hx2 : x ∈ maximalIdeal R ^ 2
    · exact Set.mem_biUnion (x := maximalIdeal R ^ 2) (by simp [hs]) hx2
    · have hx3 : x ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := by
        rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
        exact hcon x hx hx2
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx3
      exact Set.mem_biUnion (x := p) (by simp [hs, hp]) hxp
  rw [Ideal.subset_union_prime (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) ?_] at hsub
  · obtain ⟨i, hi, hle⟩ := hsub
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hlt := (IsLocalRing.maximalIdeal_sq_lt_maximalIdeal R)
      have hfield : IsField R := by
        by_contra hnf
        exact (not_lt_of_ge hle) (hlt.mpr hnf)
      have hbot : maximalIdeal R = ⊥ := (isField_iff_maximalIdeal_eq).mp hfield
      rw [hbot] at hz
      have : z = 0 := (Submodule.mem_bot R).mp hz
      subst this
      exact zero_notMem_nonZeroDivisors hz0
    · have hp : (i : Ideal R) ∈ associatedPrimes R R := by simpa using hi
      have hzi : z ∈ i := hle hz
      have : z ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := Set.mem_biUnion hp hzi
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at this
      exact this hz0
  · intro i hi _ _
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact absurd rfl ‹_›
    · exact (show i ∈ associatedPrimes R R by simpa using hi).isPrime

/-- **Depth-zero case of Serre's theorem**: if every element of `𝔪` is a zero divisor and `κ` has
finite projective dimension, then `R` is a field (Matsumura CRT, proof of Thm 19.2, case
`depth R = 0`). -/
theorem IsLocalRing.isField_of_hasProjectiveDimensionLE_residueField_of_forall_notMem_nonZeroDivisors
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ z ∈ maximalIdeal R, z ∉ nonZeroDivisors R) (n : ℕ)
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n) : IsField R := by
  classical
  have hfin := associatedPrimes.finite R R
  have hsub : ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ i ∈ (↑hfin.toFinset : Set (Ideal R)), (i : Set R) := by
    intro z hz
    have hz' : z ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
      exact h z hz
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz'
    exact Set.mem_biUnion (x := p) (by simpa using hp) hzp
  rw [Ideal.subset_union_prime ⊥ ⊥
    (fun i hi _ _ => (show i ∈ associatedPrimes R R by simpa using hi).isPrime)] at hsub
  obtain ⟨p, hp, hle⟩ := hsub
  have hp' : p ∈ associatedPrimes R R := by simpa using hp
  have hpm : p = maximalIdeal R :=
    ((maximalIdeal.isMaximal R).eq_of_le hp'.isPrime.ne_top hle).symm
  obtain ⟨-, y, hy⟩ := isAssociatedPrime_iff.mp hp'
  rw [hpm] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (1 : R) ∈ maximalIdeal R := by
      rw [hy, Submodule.mem_colon_singleton, smul_zero]; exact Submodule.zero_mem _
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hym : ∀ m ∈ maximalIdeal R, y * m = 0 := by
    intro m hm
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hm
    rw [mul_comm]; exact hm
  have hfree : Module.Free R (ResidueField R) :=
    IsLocalRing.free_of_hasProjectiveDimensionLE_of_mul_maximalIdeal_eq_zero hy0 hym _ n hpd
  rw [isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro m hm
  have hann : m ∈ Module.annihilator R (ResidueField R) := by
    rw [Module.mem_annihilator]
    intro q
    rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff m).mpr hm, zero_mul]
  rwa [Module.annihilator_eq_bot.mpr inferInstance] at hann

/-- A Noetherian local ring with `𝔪 = ⊥` (a field) is regular: `spanFinrank 𝔪 = 0 ≤ dim R`. -/
theorem IsRegularLocalRing.of_maximalIdeal_eq_bot {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R = ⊥) : IsRegularLocalRing R := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [h, Submodule.spanFinrank_bot]
  exact_mod_cast ringKrullDim_nonneg_of_nontrivial

/-- **Serre's theorem, Stacks 00OC (1) ⇒ (3)**: a Noetherian local ring whose residue field has
finite projective dimension is regular (Matsumura CRT Thm 19.2, induction on the embedding
dimension; see the module docstring for the complete argument). -/
theorem IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n) : IsRegularLocalRing R := by
  suffices H : ∀ e : ℕ, ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n →
      (maximalIdeal R).spanFinrank ≤ e → IsRegularLocalRing R from H _ R n h le_rfl
  intro e
  induction e with
  | zero =>
    intro R _ _ _ n _ he
    exact IsRegularLocalRing.of_maximalIdeal_eq_bot
      ((Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp (Nat.le_zero.mp he))
  | succ e ih =>
    intro R _ _ _ n h he
    by_cases hzd : ∀ z ∈ maximalIdeal R, z ∉ nonZeroDivisors R
    · have hF := IsLocalRing.isField_of_hasProjectiveDimensionLE_residueField_of_forall_notMem_nonZeroDivisors
        R hzd n h
      exact IsRegularLocalRing.of_maximalIdeal_eq_bot ((isField_iff_maximalIdeal_eq).mp hF)
    · push Not at hzd
      obtain ⟨x, hx, hx2, hreg⟩ := IsLocalRing.exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors hzd
      have hxreg : IsSMulRegular R x := Module.Flat.isSMulRegular_of_nonZeroDivisors hreg
      have hne : Ideal.span {x} ≠ ⊤ := fun htop =>
        (maximalIdeal.isMaximal R).ne_top
          (top_le_iff.mp (htop ▸ (Ideal.span_singleton_le_iff_mem _).mpr hx))
      have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
      have : IsLocalRing (R ⧸ Ideal.span {x}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
      -- `pd_R 𝔪 ≤ n`
      have h1 : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) (n + 1) :=
        hasProjectiveDimensionLT_of_ge _ (n + 1) (n + 2) (by omega)
      have h2 : HasProjectiveDimensionLE (ModuleCat.of R (maximalIdeal R)) n :=
        (IsLocalRing.hasProjectiveDimensionLE_residueField_succ_iff n).mp h1
      -- `pd_{R̄} (𝔪/x𝔪) ≤ n`
      have h3 := ModuleCat.hasProjectiveDimensionLE_quotSMulTop_of_isSMulRegular hxreg
        (maximalIdeal R) (hxreg.submodule _) n h2
      -- `pd_{R̄} 𝔪̄ ≤ n` (Nagata: `𝔪̄` is a retract of `𝔪/x𝔪`)
      obtain ⟨π, s, hπs⟩ := IsLocalRing.exists_retraction_quotSMulTop_maximalIdeal hx hx2
      have h4 : HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x})
          ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})))) n := by
        have hr : Retract (ModuleCat.of (R ⧸ Ideal.span {x})
            ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x}))))
            (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (maximalIdeal R))) :=
          { i := ModuleCat.ofHom s
            r := ModuleCat.ofHom π
            retract := by rw [← ModuleCat.ofHom_comp, hπs]; rfl }
        exact hr.hasProjectiveDimensionLT (n + 1)
      have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
          maximalIdeal (R ⧸ Ideal.span {x}) :=
        IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
      have h5 : HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x})
          (maximalIdeal (R ⧸ Ideal.span {x}))) n :=
        ModuleCat.hasProjectiveDimensionLE_of_linearEquiv_of (LinearEquiv.ofEq _ _ hmap) n h4
      -- `pd_{R̄} κ̄ ≤ n + 1`
      have h6 : HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x})
          (ResidueField (R ⧸ Ideal.span {x}))) (n + 1) :=
        (IsLocalRing.hasProjectiveDimensionLE_residueField_succ_iff n).mpr h5
      -- embedding dimension drops
      have he' : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ e := by
        have := IsLocalRing.spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le hx hx2
        omega
      have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := ih (R ⧸ Ideal.span {x}) (n + 1) h6 he'
      exact IsRegularLocalRing.of_quotient_span_singleton_of_mem_nonZeroDivisors hx hreg

end
