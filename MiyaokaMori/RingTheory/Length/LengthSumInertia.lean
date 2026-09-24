import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Length.LengthLocalization

/-! # Length over a local ring as a sum over the maximal ideals of a semi-local algebra (Stacks 02M0)

Stacks 02M0: let `A` be a local ring, `B` an `A`-algebra with only finitely many maximal ideals, each maximal
ideal `m` lying over `m_A` with `[κ(m):κ(m_A)]` (`Ideal.inertiaDeg'`) nonzero (i.e. finite), and `M` a
`B`-module of finite length. Then `length_A M = Σ_m [κ(m):κ(m_A)]·length_{B_m} M_m`.

Proof:
1. Induction on the inductive definition of `IsFiniteLength B M`. `M = 0`: both sides are `0`.
2. Induction step `N ⊆ M` with `M/N` simple: both sides are additive on `0 → N → M → M/N → 0` (left:
   `Module.length_eq_add_of_exact`; right: additivity of `LengthLocalization` (2) termwise, finite sum); `N` by
   induction, so only the simple module `M/N` remains.
3. A simple `B`-module `S ≅ B/I` (`I` maximal, `isSimpleModule_iff_quot_maximal`), and both sides are
   invariant under `B`-linear isomorphisms (right: `LengthLocalization` (3)). Left: `length_A(B/I)`; `I` lies
   over `m_A`, `B/I` is an `A/m_A`-vector space, and its length is its dimension `= inertiaDeg'`
   (`Module.length_eq_of_surjective`, `Module.length_eq_finrank`; nonzero dimension, hence finite). Right:
   `LengthLocalization` (4): only the term `m = I` is nonzero, equal to `[κ(I):κ(m_A)]·1`.

Reference: Stacks 02M0.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

noncomputable section

namespace Module

variable {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
  [Finite (MaximalSpectrum B)]

/-- The right-hand side of 02M0. -/
def inertiaLengthSum (A : Type u) (B : Type u) [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] (M : Type u) [AddCommGroup M] [Module B M] : ℕ∞ :=
  ∑ᶠ m : MaximalSpectrum B,
    ((Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) m.asIdeal : ℕ) : ℕ∞) *
      Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl M)

theorem inertiaLengthSum_eq_add_of_exact {N M P : Type u} [AddCommGroup N] [Module B N]
    [AddCommGroup M] [Module B M] [AddCommGroup P] [Module B P] (f : N →ₗ[B] M) (g : M →ₗ[B] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    inertiaLengthSum A B M = inertiaLengthSum A B N + inertiaLengthSum A B P := by
  unfold inertiaLengthSum
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  refine finsum_congr fun m => ?_
  rw [length_localizedModule_eq_add_of_exact m.asIdeal.primeCompl f g hf hg hex, mul_add]

theorem inertiaLengthSum_congr {M P : Type u} [AddCommGroup M] [Module B M] [AddCommGroup P]
    [Module B P] (e : M ≃ₗ[B] P) : inertiaLengthSum A B M = inertiaLengthSum A B P := by
  unfold inertiaLengthSum
  refine finsum_congr fun m => ?_
  rw [length_localizedModule_congr m.asIdeal.primeCompl e]

theorem inertiaLengthSum_quotient (I : Ideal B) [hI : I.IsMaximal] :
    inertiaLengthSum A B (B ⧸ I) =
      ((Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) I : ℕ) : ℕ∞) := by
  unfold inertiaLengthSum
  rw [finsum_eq_single _ (⟨I, hI⟩ : MaximalSpectrum B)]
  · have := length_localizedModule_quotient_self I
    rw [this, mul_one]
  · intro m hm
    have hne : I ≠ m.asIdeal := fun h => hm (by ext1; exact h.symm)
    have : m.asIdeal.IsMaximal := m.isMaximal
    rw [length_localizedModule_quotient_of_ne I m.asIdeal hne, mul_zero]

theorem length_quotient_eq_inertiaDeg (I : Ideal B) [hI : I.IsMaximal]
    [hlo : I.LiesOver (IsLocalRing.maximalIdeal A)]
    (hfin : Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) I ≠ 0) :
    Module.length A (B ⧸ I) =
      ((Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) I : ℕ) : ℕ∞) := by
  rw [Ideal.inertiaDeg'_algebraMap] at hfin ⊢
  let _ : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have hfd : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hfin)
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ IsLocalRing.maximalIdeal A)
    (M := B ⧸ I) Ideal.Quotient.mk_surjective, Module.length_eq_finrank]

/-- Stacks 02M0. -/
theorem length_eq_inertiaLengthSum {M : Type u} [AddCommGroup M] [Module B M]
    (hB : ∀ m : MaximalSpectrum B, m.asIdeal.LiesOver (IsLocalRing.maximalIdeal A))
    (hfin : ∀ m : MaximalSpectrum B, Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) m.asIdeal ≠ 0)
    (hM : IsFiniteLength B M) :
    ∀ [Module A M] [IsScalarTower A B M], Module.length A M = inertiaLengthSum A B M := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    intro _ _
    rw [Module.length_eq_zero]
    unfold inertiaLengthSum
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    have h0 : Module.length B M = 0 := Module.length_eq_zero
    have : Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl M) = 0 :=
      le_antisymm ((length_localizedModule_le _).trans h0.le) (by simp)
    rw [this, mul_zero]
  | @of_simple_quotient M _ _ N hs _ ih =>
    intro _ _
    have hex : Function.Exact N.subtype N.mkQ := LinearMap.exact_subtype_mkQ N
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hex,
      inertiaLengthSum_eq_add_of_exact N.subtype N.mkQ (Submodule.subtype_injective N)
        (Submodule.mkQ_surjective N) hex, ih]
    congr 1
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have := hB ⟨I, hI⟩
    rw [(e.restrictScalars A).length_eq, inertiaLengthSum_congr e, inertiaLengthSum_quotient,
      length_quotient_eq_inertiaDeg I (hfin ⟨I, hI⟩)]

end Module

end
