import MiyaokaMori.Prelude

/-! # Length and localization

Let `R` be a commutative ring, `p ⊆ R` a multiplicative subset, `M` an `R`-module; write
`M_p = LocalizedModule p M`, `R_p = Localization p`.
(1) `length_{R_p}(M_p) ≤ length_R(M)`;
(2) localized length is additive on short exact sequences: `0 → N → M → P → 0` exact ⇒
    `length_{R_p}(M_p) = length_{R_p}(N_p) + length_{R_p}(P_p)`;
(3) an `R`-linear isomorphism `M ≃ M′` gives `length_{R_p}(M_p) = length_{R_p}(M′_p)`;
(4) for maximal ideals `I`, `J` of `R`: if `I ≠ J` then `(R/I)_J = 0`, of length `0`; if `I = J` then
    `length_{R_I}((R/I)_I) = 1`;
(5) `length_{R_p}((R/yR)_p) = ord_{R_p}(y)` (the definition `length(R_p/yR_p)` of `Ring.ord`).

Proof:
1. (1): `N′ ↦` its preimage in `M` is an order-preserving injection from `R_p`-submodules (Mathlib
   `Submodule.localized'gi` is a Galois insertion, `u` strictly monotone); length is the Krull dimension of
   the submodule lattice, `Order.krullDim_le_of_strictMono`.
2. (2): localization is exact (`LocalizedModule.map_exact`, `IsLocalizedModule.map_injective/surjective`),
   `R`-linear maps between `R_p`-modules are automatically `R_p`-linear
   (`LinearMap.extendScalarsOfIsLocalization`), then `Module.length_eq_add_of_exact`.
3. (3): apply (2) to `0 → 0 → M → M′ → 0`.
4. (4): for `I ≠ J` take `s ∈ I ∖ J` (maximal ideals are incomparable); `s` kills `R/I` and lies outside
   `J`, `LocalizedModule.subsingleton_iff`. For `I = J`, by (1) the length is `≤ length_R(R/I) = 1` (`R/I`
   simple), and `(R/I)_I ≠ 0` (`1` is not killed by elements outside `I`), so the length is `1`.
5. (5): localization of a quotient is the quotient of the localization (Mathlib
   `IsLocalizedModule.toLocalizedQuotient'`), and `(yR)R_p = yR_p` (`Submodule.localized'_span`).

Reference: the proof of Stacks 02M0 (exactness of localization, localization of simple modules).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u v

noncomputable section

namespace Module

variable {R : Type*} [CommRing R] (p : Submonoid R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]

theorem length_localizedModule_le :
    Module.length (Localization p) (LocalizedModule p M) ≤ Module.length R M := by
  have gi := Submodule.localized'gi (Localization p) p (LocalizedModule.mkLinearMap p M)
  have h := Order.krullDim_le_of_strictMono _ gi.strictMono_u
  rw [← Module.coe_length, ← Module.coe_length] at h
  exact WithBot.coe_le_coe.mp h

/-- The `R_p`-linear map between localized modules. -/
def locMap (f : N →ₗ[R] M) : LocalizedModule p N →ₗ[Localization p] LocalizedModule p M :=
  (IsLocalizedModule.map p (LocalizedModule.mkLinearMap p N) (LocalizedModule.mkLinearMap p M)
    f).extendScalarsOfIsLocalization p (Localization p)

theorem length_localizedModule_eq_add_of_exact (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Module.length (Localization p) (LocalizedModule p M) =
      Module.length (Localization p) (LocalizedModule p N) +
        Module.length (Localization p) (LocalizedModule p P) :=
  Module.length_eq_add_of_exact (locMap p f) (locMap p g)
    (IsLocalizedModule.map_injective p _ _ f hf) (IsLocalizedModule.map_surjective p _ _ g hg)
    (LocalizedModule.map_exact p f g hex)

theorem length_localizedModule_congr (e : M ≃ₗ[R] P) :
    Module.length (Localization p) (LocalizedModule p M) =
      Module.length (Localization p) (LocalizedModule p P) := by
  have h := length_localizedModule_eq_add_of_exact p (⊥ : Submodule R M).subtype
    (e : M →ₗ[R] P) (Submodule.subtype_injective _) e.surjective (by
      intro x
      constructor
      · intro hx
        have : x = 0 := e.injective (by simpa using hx)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨⟨y, hy⟩, rfl⟩
        rw [Submodule.mem_bot] at hy
        simp [hy])
  have h0 : Module.length (Localization p) (LocalizedModule p (⊥ : Submodule R M)) = 0 := by
    refine le_antisymm ((length_localizedModule_le p).trans ?_) zero_le
    rw [Module.length_bot]
  rw [h, h0, zero_add]

/-- The length of `(R/yR)_p` is `ord_{R_p}(y)`. -/
theorem length_localizedModule_quotient_span_singleton (y : R) :
    Module.length (Localization p) (LocalizedModule p (R ⧸ Ideal.span {y})) =
      Ring.ord (Localization p) (algebraMap R (Localization p) y) := by
  let S := Localization p
  let f : R →ₗ[R] S := Algebra.linearMap R S
  let I : Submodule R R := Ideal.span {y}
  let e₀ : (S ⧸ I.localized' S p f) ≃ₗ[R] LocalizedModule p (R ⧸ I) :=
    IsLocalizedModule.linearEquiv p (I.toLocalizedQuotient' S p f)
      (LocalizedModule.mkLinearMap p (R ⧸ I))
  let e : (S ⧸ I.localized' S p f) ≃ₗ[S] LocalizedModule p (R ⧸ I) :=
    e₀.extendScalarsOfIsLocalization p S
  have hI : I.localized' S p f = (Ideal.span {algebraMap R S y} : Ideal S) := by
    show (Submodule.span R {y}).localized' S p f = _
    rw [Submodule.localized'_span, Set.image_singleton]
    rfl
  unfold Ring.ord
  rw [← e.length_eq, hI]

section Maximal

variable (I J : Ideal R) [I.IsMaximal] [J.IsMaximal]

theorem length_localizedModule_quotient_of_ne (h : I ≠ J) :
    Module.length (Localization J.primeCompl) (LocalizedModule J.primeCompl (R ⧸ I)) = 0 := by
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  have hIJ : ¬ I ≤ J := fun hle => h (Ideal.IsMaximal.eq_of_le ‹I.IsMaximal› Ideal.IsPrime.ne_top' hle)
  obtain ⟨s, hsI, hsJ⟩ := Set.not_subset.mp hIJ
  intro x
  refine ⟨s, hsJ, ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right x hsI

theorem length_localizedModule_quotient_self :
    Module.length (Localization I.primeCompl) (LocalizedModule I.primeCompl (R ⧸ I)) = 1 := by
  have : IsSimpleModule R (R ⧸ I) := by
    rw [isSimpleModule_iff_quot_maximal]
    exact ⟨I, ‹_›, ⟨LinearEquiv.refl _ _⟩⟩
  refine le_antisymm ((length_localizedModule_le _).trans (Module.length_eq_one R (R ⧸ I)).le) ?_
  rw [Order.one_le_iff_ne_zero, Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  intro hx
  obtain ⟨s, hs, hs1⟩ := hx (Submodule.Quotient.mk 1)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one] at hs1
  exact hs hs1

end Maximal

end Module

end
