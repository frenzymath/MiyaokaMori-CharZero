import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentStalkFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.FromSpecStalkAssociatedPointsBridge

/-! # Nonzerodivisors act injectively on stalks of coherent sheaves without embedded points

Non-zero-divisors of `O_{X,x}` act injectively on the stalk `F_x` of a coherent sheaf `F` without
embedded associated points and with `Supp F = X` (`X` locally Noetherian). This is the algebraic heart
of Stacks 02P2 (`divisors-lemma-make-maps-regular-section`, step "`b₀` is a non-zero-divisor on `M`"),
used for the regularity of the denominator maps.

Three declarations:

* `MiyaokaMori.DenominatorMaps.isSMulRegular_of_associatedPrimes_pairwise` (pure commutative algebra):
  `R` Noetherian, `M` finite, no two distinct associated primes of `M` are comparable, and
  every prime of `R` contains `Ann M`; then every non-zero-divisor `r` of `R` acts injectively on `M`.
  Proof (Stacks 02OI + 0587 + 00LD): if `r` were a zero-divisor on `M`, it would lie in some `p ∈ Ass M`
  (Mathlib `biUnion_associatedPrimes_eq_compl_regular`). Choose a minimal prime `q` over `Ann M` with
  `q ≤ p` (`Ideal.exists_minimalPrimes_le`); `q ∈ Ass M` (`minimalPrimes_annihilator_subset_associatedPrimes`),
  so `q = p` by the no-embedded hypothesis. Since every prime contains `Ann M`, `q` is a minimal prime of
  `R`; its elements are zero-divisors of `R` (`notMem_nonZeroDivisors_of_mem_mem_minimalPrimes`),
  contradicting `r ∈ R⁰`.

* `AlgebraicGeometry.Scheme.Modules.exists_generization_of_stalk_primes`: the
  bridge between the prime spectrum of the local ring `O_{X,x}` and the generizations of `x`, compatible with
  associated points and support. Statement: there is `φ : Spec O_{X,x} → X`, injective, monotone for
  specialization (`p ≤ q → φ p ⤳ φ q`), such that `p ∈ Ass_{O_{X,x}}(F_x) ↔ φ p` is an associated point of
  `F`, and `p ∈ Supp_{O_{X,x}}(F_x) ↔ φ p ∈ Supp F`.
  Proof (Stacks 01J7 + 05AI + 01BA + 0310): `φ := (X.fromSpecStalk x).base` is a preimmersion, hence a
  topological embedding (injective), and continuous (preserves specialization; `p ≤ q ↔ p ⤳ q` in `Spec`,
  `PrimeSpectrum.le_iff_specializes`). The two `iff`s are
  `isAssociatedPoint_fromSpecStalk_iff_of_isQuasicoherent` and `mem_support_fromSpecStalk_iff` of
  `RegularMeromorphicDenominatorMaps_StalkRegular_FromSpecStalkBridge`: choose an affine open `W ∋ x`,
  `A := Γ(X, W)`, `N := Γ(F, W)`; the point `y = φ p` lies in `W` with prime `p ∩ A`
  (`primeIdealOf_fromSpecStalk`), and both stalks are localizations of `N` (`F_x = N_𝔮`, `F_y = N_{p ∩ A}`,
  `isLocalizedModule_germₗ_of_isQuasicoherent`), so `Ass` and `Supp` are compared over `A` via Mathlib
  `preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule` (needs `A` Noetherian) and
  the support lemma `mem_support_iff_comap_mem_of_isLocalizedModule`.

* `AlgebraicGeometry.Scheme.Modules.isSMulRegular_stalk_of_mem_nonZeroDivisors` (from the two above):
  the sheaf-level statement. The hypotheses `F.HasNoEmbeddedAssociatedPoints` and
  `F.support = univ` are transported to `F_x` along `φ`: comparable associated primes `p ≤ q` give
  `φ p ⤳ φ q`, both associated points, hence `φ p = φ q`, hence `p = q`; and every prime `p` of `O_{X,x}`
  lies in `Supp(F_x)` because `φ p ∈ Supp F = X`, i.e. `Ann(F_x) ≤ p` (`Module.mem_support_iff_of_finite`).

Source: Stacks 02P2 (proof), 02OI, 0587 (`Ass` of a finite module over a Noetherian ring is finite and
contains the minimal primes of the support), 00LD (zero-divisors on `M` = union of `Ass M`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Pure algebra (Stacks 02P2, 00LD, 0587).** Over a Noetherian ring `R`, a finite module `M` whose
associated primes are pairwise incomparable and whose annihilator lies in every prime has every
non-zero-divisor of `R` acting injectively. -/
theorem MiyaokaMori.DenominatorMaps.isSMulRegular_of_associatedPrimes_pairwise
    {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hemb : ∀ p q : Ideal R, p ∈ associatedPrimes R M → q ∈ associatedPrimes R M → p ≤ q → p = q)
    (hsupp : ∀ p : Ideal R, p.IsPrime → Module.annihilator R M ≤ p)
    {r : R} (hr : r ∈ nonZeroDivisors R) : IsSMulRegular M r := by
  by_contra hreg
  have hmem : r ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact hreg
  obtain ⟨p, hp, hrp⟩ := Set.mem_iUnion₂.mp hmem
  have hpprime : p.IsPrime := hp.isPrime
  have hann : Module.annihilator R M ≤ p := hsupp p hpprime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hann
  have hqass : q ∈ associatedPrimes R M :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq
  have hqp' : q = p := hemb q p hqass hp hqp
  have hqmin : q ∈ minimalPrimes R :=
    ⟨⟨hq.1.1, bot_le⟩, fun y hy hyq => hq.2 ⟨hy.1, hsupp y hy.1⟩ hyq⟩
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (hqp' ▸ hrp) hqmin hr

/-- **Bridge (Stacks 01J7, 05AI, 01BA): primes of the local ring `O_{X,x}` are the generizations of `x`,
compatibly with associated points and support of a coherent module.** `φ := (X.fromSpecStalk x).base`; see the
module docstring. `Function.Injective φ` and monotonicity hold for any scheme; the two `iff`s need `F`
quasi-coherent (here coherent) and, for `Ass`, `X` locally Noetherian
(`preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule` needs a Noetherian base ring). -/
theorem AlgebraicGeometry.Scheme.Modules.exists_generization_of_stalk_primes
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : X) :
    ∃ φ : PrimeSpectrum (X.presheaf.stalk x) → X,
      Function.Injective φ ∧ (∀ p q, p ≤ q → φ p ⤳ φ q) ∧
      (∀ p, p.asIdeal ∈ associatedPrimes (X.presheaf.stalk x) (F.stalk x) ↔
        F.IsAssociatedPoint (φ p)) ∧
      (∀ p, p ∈ Module.support (X.presheaf.stalk x) (F.stalk x) ↔ φ p ∈ F.support) := by
  have : F.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  refine ⟨fun p => (X.fromSpecStalk x).base p, (X.fromSpecStalk x).isEmbedding.injective, ?_, ?_, ?_⟩
  · intro p q hpq
    exact ((PrimeSpectrum.le_iff_specializes p q).mp hpq).map (X.fromSpecStalk x).base.hom.continuous
  · intro p
    exact (AlgebraicGeometry.Scheme.Modules.isAssociatedPoint_fromSpecStalk_iff_of_isQuasicoherent F p).symm
  · intro p
    exact (AlgebraicGeometry.Scheme.Modules.mem_support_fromSpecStalk_iff F p).symm

/-- **Stacks 02P2 (proof): non-zero-divisors of `O_{X,x}` act injectively on `F_x`** when `F` is coherent
without embedded associated points and `Supp F = X` on a locally Noetherian `X`. -/
theorem AlgebraicGeometry.Scheme.Modules.isSMulRegular_stalk_of_mem_nonZeroDivisors
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (hF : F.HasNoEmbeddedAssociatedPoints)
    (hsupp : F.support = Set.univ) (x : X) {r : X.presheaf.stalk x}
    (hr : r ∈ nonZeroDivisors (X.presheaf.stalk x)) : IsSMulRegular (F.stalk x) r := by
  obtain ⟨φ, hinj, hmono, hass, hsup⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_generization_of_stalk_primes F x
  have hfin : Module.Finite (X.presheaf.stalk x) (F.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  refine MiyaokaMori.DenominatorMaps.isSMulRegular_of_associatedPrimes_pairwise ?_ ?_ hr
  · intro p q hp hq hpq
    have hp' : p.IsPrime := hp.isPrime
    have hq' : q.IsPrime := hq.isPrime
    have h1 : F.IsAssociatedPoint (φ ⟨p, hp'⟩) := (hass ⟨p, hp'⟩).mp hp
    have h2 : F.IsAssociatedPoint (φ ⟨q, hq'⟩) := (hass ⟨q, hq'⟩).mp hq
    have h3 : φ ⟨p, hp'⟩ ⤳ φ ⟨q, hq'⟩ := hmono _ _ hpq
    have h4 := hinj (hF _ _ h1 h2 h3)
    exact congrArg PrimeSpectrum.asIdeal h4
  · intro p hp
    have h1 : φ ⟨p, hp⟩ ∈ F.support := by rw [hsupp]; trivial
    have h2 : (⟨p, hp⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈
        Module.support (X.presheaf.stalk x) (F.stalk x) := (hsup ⟨p, hp⟩).mpr h1
    exact Module.mem_support_iff_of_finite.mp h2

end
