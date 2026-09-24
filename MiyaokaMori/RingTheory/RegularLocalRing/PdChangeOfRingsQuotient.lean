import MiyaokaMori.Prelude
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.Regular.Free
import MiyaokaMori.RingTheory.RegularLocalRing.ProjectiveDimensionTools

/-! # Change of rings for the projective dimension along a quotient

**Change of rings, "reduction mod `x`"** (Matsumura, *Commutative Ring Theory*, §19 Lemma 2(i);
Bruns–Herzog Prop. 1.1.5-style; the ingredient of the proof of Serre's theorem 19.2):
let `(R, 𝔪)` be a Noetherian local ring, `x ∈ R` a nonzerodivisor and `N` a finite `R`-module on
which `x` is regular. If `pd_R N ≤ n` then `pd_{R/(x)} (N/xN) ≤ n`.

Proof (self-contained, by induction on `n`, no Tor needed). `n = 0`: `N` is projective, hence free
over the local ring `R`, so `N/xN` is free over `R/(x)` (Mathlib instance in `RingTheory.Regular.Free`),
hence projective. `n + 1`: choose `0 → K → R^k → N → 0` (`K` finite since `R` is Noetherian);
`x` is regular on `R^k` hence on `K ⊆ R^k`, and `pd_R K ≤ n`, so `pd_{R/(x)} (K/xK) ≤ n` by
induction. Because `x` is regular on `N`, reducing mod `x` keeps the sequence exact on the left
(Mathlib `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`, i.e. `Tor₁(N, R/x) = 0`),
and it is always right exact (`QuotSMulTop.map_exact`), so `0 → K/xK → R^k/xR^k → N/xN → 0` is a
short exact sequence of `R/(x)`-modules with free middle term, and dimension shifting
(`ShortExact.hasProjectiveDimensionLT_X₃`) gives `pd_{R/(x)} (N/xN) ≤ n + 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory IsLocalRing
open scoped Pointwise

noncomputable section

/-- **Change of rings, reduction mod a regular element**: `x` a nonzerodivisor of the Noetherian
local ring `R`, `N` a finite `R`-module with `x` `N`-regular; `pd_R N ≤ n ⇒ pd_{R/(x)} (N/xN) ≤ n`
(Matsumura CRT §19 Lemma 2(i)). -/
theorem ModuleCat.hasProjectiveDimensionLE_quotSMulTop_of_isSMulRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : IsSMulRegular R x)
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] (hN : IsSMulRegular N x)
    (n : ℕ) (h : HasProjectiveDimensionLE (ModuleCat.of R N) n) :
    HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x N)) n := by
  induction n generalizing N with
  | zero =>
    have hproj : Module.Projective R N := by
      rw [IsProjective.iff_projective]
      exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr h
    have hfree : Module.Free R N := Module.free_of_flat_of_isLocalRing
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective]
    exact Module.Projective.of_free
  | succ n ih =>
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R N
    set K := LinearMap.ker f with hKdef
    have hK : HasProjectiveDimensionLE (ModuleCat.of R K) n :=
      (ModuleCat.hasProjectiveDimensionLE_succ_iff_ker f hf n).mp h
    have hFreg : IsSMulRegular (Fin k → R) x := IsSMulRegular.pi fun _ => hx
    have hKreg : IsSMulRegular K x := hFreg.submodule K
    have : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    have h1 := ih K hKreg hK
    have hsurj : Function.Surjective (algebraMap R (R ⧸ Ideal.span {x})) :=
      Ideal.Quotient.mk_surjective
    let i : QuotSMulTop x K →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x (Fin k → R) :=
      (QuotSMulTop.map x K.subtype).extendScalarsOfSurjective hsurj
    let p : QuotSMulTop x (Fin k → R) →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N :=
      (QuotSMulTop.map x f).extendScalarsOfSurjective hsurj
    have hi : Function.Injective i := by
      have hex := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        (f₁ := (0 : K →ₗ[R] K)) (f₂ := K.subtype) (f₃ := f)
        ((LinearMap.exact_zero_iff_injective _ _).mpr K.injective_subtype)
        (LinearMap.exact_subtype_ker_map f) hN
      rw [map_zero] at hex
      exact (LinearMap.exact_zero_iff_injective _ _).mp hex
    have hp : Function.Surjective p := QuotSMulTop.map_surjective x hf
    have hexact : Function.Exact i p :=
      QuotSMulTop.map_exact x (LinearMap.exact_subtype_ker_map f) hf
    have hzero : ModuleCat.ofHom i ≫ ModuleCat.ofHom p = 0 := by
      rw [← ModuleCat.ofHom_comp]
      exact ModuleCat.hom_ext (LinearMap.ext fun a => hexact.apply_apply_eq_zero a)
    let S : ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {x})) :=
      ShortComplex.mk (ModuleCat.ofHom i) (ModuleCat.ofHom p) hzero
    have hmono : Mono S.f := (ModuleCat.mono_iff_injective (ModuleCat.ofHom i)).mpr hi
    have hepi : Epi S.g := (ModuleCat.epi_iff_surjective (ModuleCat.ofHom p)).mpr hp
    have hex : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr hexact
    have hS : S.ShortExact := { exact := hex, mono_f := hmono, epi_g := hepi }
    have hX₂ : HasProjectiveDimensionLT S.X₂ (n + 2) := by
      have : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x (Fin k → R)) := inferInstance
      have hproj : Projective S.X₂ := by
        rw [← IsProjective.iff_projective]; exact Module.Projective.of_free
      exact hasProjectiveDimensionLT_of_ge S.X₂ 1 (n + 2) (by omega)
    exact hS.hasProjectiveDimensionLT_X₃ (n + 1) h1 hX₂

end
