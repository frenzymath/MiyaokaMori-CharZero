import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Localization.Stacks02m6

/-! # Associated primes along a surjective ring homomorphism

Associated primes along a surjective ring homomorphism (used by Stacks 02OM):
if `φ : A →+* B` is surjective and `N` is a `B`-module, regarded also as an `A`-module through `φ`
(`a • n = φ a • n`), then

* `Ass_A(N) = φ⁻¹(Ass_B(N))` (`associatedPrimes_eq_comap_image`),
* `𝔮 ∈ Ass_B(N) ↔ φ⁻¹𝔮 ∈ Ass_A(N)` (`isAssociatedPrime_comap_iff`),
* `N` has no embedded primes over `A` iff it has none over `B` (`hasNoEmbeddedPrimes_iff_of_surjective`).

Proof. For `x : N`, `φ⁻¹(Ann_B(x)) = Ann_A(x)` because `a • x = φ a • x`; `comap` commutes with radicals
(`Ideal.comap_radical`) and preserves primes, so `comap φ` maps `Ass_B(N)` into `Ass_A(N)`. Conversely, if
`𝔭 = rad(Ann_A(x)) ∈ Ass_A(N)`, then `𝔭 = φ⁻¹(rad(Ann_B(x)))`, so `𝔭 ⊇ ker φ`; `J := rad(Ann_B x)` satisfies
`J = φ(φ⁻¹ J) = φ(𝔭)` (`Ideal.map_comap_of_surjective`), which is prime because `𝔭` is prime and contains
`ker φ` (`Ideal.map_isPrime_of_surjective`); hence `J ∈ Ass_B(N)` and `𝔭 = φ⁻¹ J`. For the last item, `comap φ`
is injective and order-reflecting on ideals of `B` (`Ideal.comap_injective_of_surjective`,
`Ideal.comap_le_comap_iff_of_surjective`).

Source: Stacks 00LD / 05BV-style bookkeeping (associated primes of a module over `A/I` are the associated
primes over `A`); self-contained proof above.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace MiyaokaMori.AssociatedPrimesComap

variable {A B N : Type*} [CommRing A] [CommRing B] [AddCommGroup N] [Module A N] [Module B N]
  (φ : A →+* B)

/-- `φ⁻¹(Ann_B(x)) = Ann_A(x)` (as colon ideals of `⊥`) when `A` acts through `φ`. -/
theorem comap_colon_bot_singleton (hsmul : ∀ (a : A) (n : N), a • n = φ a • n) (x : N) :
    Ideal.comap φ ((⊥ : Submodule B N).colon {x}) = (⊥ : Submodule A N).colon {x} := by
  ext a
  rw [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_colon_singleton,
    Submodule.mem_bot, Submodule.mem_bot, hsmul]

/-- `φ⁻¹` of an associated prime of `N` over `B` is an associated prime over `A`. -/
theorem isAssociatedPrime_comap_of_isAssociatedPrime (hsmul : ∀ (a : A) (n : N), a • n = φ a • n)
    {J : Ideal B} (hJ : IsAssociatedPrime J N) : IsAssociatedPrime (Ideal.comap φ J) N := by
  obtain ⟨hprime, x, rfl⟩ := hJ
  refine ⟨Ideal.comap_isPrime φ _, x, ?_⟩
  rw [Ideal.comap_radical, comap_colon_bot_singleton φ hsmul]

/-- Every associated prime of `N` over `A` is `φ⁻¹` of an associated prime over `B`. -/
theorem exists_isAssociatedPrime_comap_eq (hφ : Function.Surjective φ)
    (hsmul : ∀ (a : A) (n : N), a • n = φ a • n) {p : Ideal A} (hp : IsAssociatedPrime p N) :
    ∃ J : Ideal B, IsAssociatedPrime J N ∧ Ideal.comap φ J = p := by
  obtain ⟨hprime, x, rfl⟩ := hp
  set J : Ideal B := ((⊥ : Submodule B N).colon {x}).radical with hJdef
  have hcomap : Ideal.comap φ J = ((⊥ : Submodule A N).colon {x}).radical := by
    rw [hJdef, Ideal.comap_radical, comap_colon_bot_singleton φ hsmul]
  have hker : RingHom.ker φ ≤ ((⊥ : Submodule A N).colon {x}).radical := by
    rw [← hcomap]
    exact Ideal.comap_mono bot_le
  have hJmap : J = Ideal.map φ (((⊥ : Submodule A N).colon {x}).radical) := by
    rw [← hcomap, Ideal.map_comap_of_surjective φ hφ]
  have hJprime : J.IsPrime := by
    rw [hJmap]
    exact Ideal.map_isPrime_of_surjective hφ hker
  exact ⟨J, ⟨hJprime, x, rfl⟩, hcomap⟩

/-- `Ass_A(N) = φ⁻¹(Ass_B(N))` for `φ` surjective and `A` acting on `N` through `φ`. -/
theorem associatedPrimes_eq_comap_image (hφ : Function.Surjective φ)
    (hsmul : ∀ (a : A) (n : N), a • n = φ a • n) :
    associatedPrimes A N = Ideal.comap φ '' associatedPrimes B N := by
  ext p
  constructor
  · intro hp
    obtain ⟨J, hJ, hJp⟩ := exists_isAssociatedPrime_comap_eq φ hφ hsmul hp
    exact ⟨J, hJ, hJp⟩
  · rintro ⟨J, hJ, rfl⟩
    exact isAssociatedPrime_comap_of_isAssociatedPrime φ hsmul hJ

/-- `𝔮 ∈ Ass_B(N) ↔ φ⁻¹𝔮 ∈ Ass_A(N)` for `φ` surjective. -/
theorem isAssociatedPrime_comap_iff (hφ : Function.Surjective φ)
    (hsmul : ∀ (a : A) (n : N), a • n = φ a • n) (J : Ideal B) :
    IsAssociatedPrime (Ideal.comap φ J) N ↔ IsAssociatedPrime J N := by
  constructor
  · intro h
    obtain ⟨J', hJ', hJJ'⟩ := exists_isAssociatedPrime_comap_eq φ hφ hsmul h
    rwa [Ideal.comap_injective_of_surjective φ hφ hJJ'] at hJ'
  · exact isAssociatedPrime_comap_of_isAssociatedPrime φ hsmul

end MiyaokaMori.AssociatedPrimesComap

/-- **No embedded primes is insensitive to a surjection of the base ring**: for `φ : A →+* B` surjective and
`N` a `B`-module regarded as an `A`-module through `φ`, `N` has no embedded primes over `A` iff over `B`. -/
theorem Module.hasNoEmbeddedPrimes_iff_of_surjective {A B N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module A N] [Module B N] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hsmul : ∀ (a : A) (n : N), a • n = φ a • n) :
    Module.HasNoEmbeddedPrimes A N ↔ Module.HasNoEmbeddedPrimes B N := by
  unfold Module.HasNoEmbeddedPrimes
  rw [MiyaokaMori.AssociatedPrimesComap.associatedPrimes_eq_comap_image φ hφ hsmul]
  constructor
  · intro h J hJ J' hJ' hle
    have := h (Ideal.comap φ J) ⟨J, hJ, rfl⟩ (Ideal.comap φ J') ⟨J', hJ', rfl⟩ (Ideal.comap_mono hle)
    exact Ideal.comap_injective_of_surjective φ hφ this
  · rintro h _ ⟨J, hJ, rfl⟩ _ ⟨J', hJ', rfl⟩ hle
    rw [Ideal.comap_le_comap_iff_of_surjective φ hφ] at hle
    rw [h J hJ J' hJ' hle]

end
