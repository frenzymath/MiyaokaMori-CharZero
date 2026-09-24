import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span

/-!
# The affine coordinate ring of a truncated one-parameter jet

In a local frame of a line bundle, the order-`T` infinitesimal neighborhood of its zero section
has coordinate ring `R[X] / (X^(T+1))`. This module names that ring and its canonical ring
homomorphism. It does not construct the global twisted jet or a line-bundle trivialization.

The coefficient API (`coeff`, `ext_coeff`, `rescale`, ...) lives here together with the ring, so
that the ring and the way to read a coefficient off it are in one place. The three `rescale` lemmas
that mention `GlobalTruncatedParameterAPI` are in the module `TruncatedJetRingRescale`, which is
downstream of this one.

**`TruncatedJetRing R T` is an `abbrev` of Mathlib's `AdjoinRoot ((X : R[X]) ^ (T + 1))`** rather than
the hand-written quotient `R[X] ⧸ truncationIdeal R T`. The two are the same term after one
δ-unfolding of `AdjoinRoot` (`AdjoinRoot f := R[X] ⧸ Ideal.span {f}`), so every statement below has
the expected meaning; the point is the *instance path*: `AdjoinRoot` is a `def`, so type-class search
on `TruncatedJetRing R T` finds `AdjoinRoot.instCommRing` / `AdjoinRoot.instAlgebra` and the module
structure `Algebra.toModule`, exactly the path `TensorProduct`/`Algebra.TensorProduct` are stated
with. With the reducible quotient spelling, type-class search would see a *module quotient* and pick
`Submodule.Quotient.module'`, which makes `algebraMap k (A ⊗[k] TruncatedJetRing k r) c` a stuck
instance problem and `Algebra.TensorProduct.includeRight` uncoercible.

Consequence for users: `rw`/`simp` with the generic quotient lemmas (`Ideal.Quotient.lift_mk`, `Ideal.Quotient.eq`,
`Ideal.Quotient.eq_zero_iff_mem`) no longer *match* a term whose type is `TruncatedJetRing R T` (they still
*typecheck* — `exact`/`show`/`rfl` are unaffected), because matching runs at instance transparency and does not
unfold `AdjoinRoot`. Use the restatements below (`jetProjection_surjective`, `jetProjection_eq_iff`,
`jetProjection_eq_zero_iff`, `jetProjection_X_pow_succ`, `lift_jetProjection`) or Mathlib's `AdjoinRoot.*` API
(`jetProjection R T = AdjoinRoot.mk _` by `rfl`, `jetProjection_eq_mk`).
-/

noncomputable section

namespace MiyaokaMori.Jet

open Polynomial

variable (R : Type*) [CommRing R]

/-- The ideal cutting out the order-`T` neighborhood of zero in the affine line over `R`.
A reducible name for `Ideal.span {X^(T+1)}` (the ideal `AdjoinRoot` divides by). -/
abbrev truncationIdeal (T : ℕ) : Ideal R[X] :=
  Ideal.span {(X : R[X]) ^ (T + 1)}

/-- The actual coordinate ring of the truncated affine line, with orders `0, …, T` retained:
Mathlib's `AdjoinRoot (X^(T+1)) = R[X] ⧸ Ideal.span {X^(T+1)}`. -/
abbrev TruncatedJetRing (T : ℕ) := AdjoinRoot ((X : R[X]) ^ (T + 1))

/-- The canonical quotient homomorphism, rather than an abstract list of coefficients.
Definitionally `AdjoinRoot.mk (X^(T+1))` (`jetProjection_eq_mk`); the body keeps the quotient spelling so
that `unfold jetProjection; rw [Ideal.Quotient.lift_mk]` in downstream proofs keeps matching. -/
def jetProjection (T : ℕ) : R[X] →+* TruncatedJetRing R T :=
  Ideal.Quotient.mk (truncationIdeal R T)

theorem jetProjection_eq_mk (T : ℕ) :
    jetProjection R T = AdjoinRoot.mk ((X : R[X]) ^ (T + 1)) := rfl

theorem jetProjection_eq_quotientMk (T : ℕ) :
    jetProjection R T = Ideal.Quotient.mk (truncationIdeal R T) := rfl

/-- The class of the parameter is Mathlib's `AdjoinRoot.root`. -/
theorem jetProjection_X (T : ℕ) :
    jetProjection R T X = AdjoinRoot.root ((X : R[X]) ^ (T + 1)) := rfl

theorem jetProjection_surjective (T : ℕ) : Function.Surjective (jetProjection R T) :=
  AdjoinRoot.mk_surjective

theorem jetProjection_eq_iff (T : ℕ) {p q : R[X]} :
    jetProjection R T p = jetProjection R T q ↔ (X : R[X]) ^ (T + 1) ∣ p - q :=
  AdjoinRoot.mk_eq_mk

theorem jetProjection_eq_zero_iff (T : ℕ) {p : R[X]} :
    jetProjection R T p = 0 ↔ (X : R[X]) ^ (T + 1) ∣ p :=
  AdjoinRoot.mk_eq_zero

@[simp] theorem jetProjection_X_pow_succ (T : ℕ) :
    jetProjection R T ((X : R[X]) ^ (T + 1)) = 0 :=
  AdjoinRoot.mk_self

/-- `Ideal.Quotient.lift_mk` restated with the abbreviation `TruncatedJetRing` as the domain of the coercion
(written out with `@DFunLike.coe`, because a type ascription does not change the inferred type), so that
`rw`/`simp` find it on a lift out of the truncated ring — e.g. an unfolded `GlobalTruncatedParameterAPI.map`
or `jetThickening.sectionsHom` — applied to a class `jetProjection R T p`. -/
@[simp] theorem lift_jetProjection {S : Type*} [CommRing S] (T : ℕ) (f : R[X] →+* S)
    (H : ∀ a ∈ truncationIdeal R T, f a = 0) (p : R[X]) :
    @DFunLike.coe (TruncatedJetRing R T →+* S) (TruncatedJetRing R T) (fun _ => S) _
      (Ideal.Quotient.lift (truncationIdeal R T) f H) (jetProjection R T p) = f p := rfl

/-- `Ideal.Quotient.liftₐ` version of `lift_jetProjection`. -/
@[simp] theorem liftₐ_jetProjection {A S : Type*} [CommRing A] [CommRing S] [Algebra A R] [Algebra A S]
    (T : ℕ) (f : R[X] →ₐ[A] S) (H : ∀ a ∈ truncationIdeal R T, f a = 0) (p : R[X]) :
    @DFunLike.coe (TruncatedJetRing R T →ₐ[A] S) (TruncatedJetRing R T) (fun _ => S) _
      (Ideal.Quotient.liftₐ (truncationIdeal R T) f H) (jetProjection R T p) = f p := rfl

section Coefficients

open Polynomial

variable {S : Type*} [CommRing S]

/-- Two polynomials have the same class in the truncated ring as soon as their coefficients
agree in every order `0, ..., r`. -/
theorem jetProjection_eq_of_coeff (r : ℕ) (p q : Polynomial S)
    (h : ∀ n : ℕ, n ≤ r → p.coeff n = q.coeff n) :
    jetProjection S r p = jetProjection S r q := by
  rw [jetProjection_eq_iff, Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, sub_eq_zero]
  exact h d (Nat.lt_succ_iff.mp hd)

namespace TruncatedJetRing

/-- The order-`n` coefficient of an element of `S[X]/(X^(r+1))`, for `n ≤ r`. Well defined
because a multiple of `X^(r+1)` has no term of order `≤ r`. -/
noncomputable def coeff (r n : ℕ) (hn : n ≤ r) : TruncatedJetRing S r → S :=
  Quotient.lift (fun p : Polynomial S => p.coeff n) (by
    intro a b hab
    have h1 : -a + b ∈ truncationIdeal S r := QuotientAddGroup.leftRel_apply.mp hab
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp h1
    have h2 : (-a + b).coeff n = 0 := by
      rw [hq, Polynomial.coeff_X_pow_mul', if_neg (by omega)]
    rw [Polynomial.coeff_add, Polynomial.coeff_neg] at h2
    exact neg_add_eq_zero.mp h2)

theorem coeff_mk (r n : ℕ) (hn : n ≤ r) (p : Polynomial S) :
    coeff r n hn (jetProjection S r p) = p.coeff n := rfl

theorem coeff_jetProjection (r n : ℕ) (hn : n ≤ r) (p : Polynomial S) :
    coeff r n hn (jetProjection S r p) = p.coeff n := rfl

/-- An element of the truncated ring is determined by its orders `0, ..., r`. -/
theorem ext_coeff (r : ℕ) {x y : TruncatedJetRing S r}
    (h : ∀ (n : ℕ) (hn : n ≤ r), coeff r n hn x = coeff r n hn y) : x = y := by
  obtain ⟨p, rfl⟩ := jetProjection_surjective S r x
  obtain ⟨q, rfl⟩ := jetProjection_surjective S r y
  exact jetProjection_eq_of_coeff r p q (fun n hn => h n hn)

/-- Rescaling the parameter, `p(X) ↦ p(c·X)`, preserves the truncation ideal `(X^(r+1))`. -/
theorem rescale_wellDefined (r : ℕ) (c : S) (p : Polynomial S)
    (hp : p ∈ truncationIdeal S r) :
    ((jetProjection S r).comp (Polynomial.compRingHom (C c * X))) p = 0 := by
  have h : truncationIdeal S r ≤ RingHom.ker
      ((jetProjection S r).comp (Polynomial.compRingHom (C c * X))) := by
    refine (Ideal.span_singleton_le_iff_mem (I := RingHom.ker _) (x := (X : Polynomial S) ^ (r + 1))).mpr ?_
    rw [RingHom.mem_ker]
    show jetProjection S r (((X : Polynomial S) ^ (r + 1)).comp (C c * X)) = 0
    rw [Polynomial.pow_comp, Polynomial.X_comp, mul_pow, map_mul, jetProjection_X_pow_succ, mul_zero]
  exact h hp

/-- Rescaling the jet parameter, `X ↦ c·X`. -/
noncomputable def rescale (r : ℕ) (c : S) :
    TruncatedJetRing S r →+* TruncatedJetRing S r :=
  Ideal.Quotient.lift (truncationIdeal S r)
    ((jetProjection S r).comp (Polynomial.compRingHom (C c * X)))
    (rescale_wellDefined r c)

@[simp] theorem rescale_projection (r : ℕ) (c : S) (p : Polynomial S) :
    rescale r c (jetProjection S r p) = jetProjection S r (p.comp (C c * X)) := rfl

/-- **The weight convention**: rescaling `X ↦ c·X` multiplies the order-`n` coefficient by `c^n`. -/
@[simp] theorem coeff_rescale (r : ℕ) (c : S) (n : ℕ) (hn : n ≤ r) (x : TruncatedJetRing S r) :
    coeff r n hn (rescale r c x) = c ^ n * coeff r n hn x := by
  obtain ⟨p, rfl⟩ := jetProjection_surjective S r x
  rw [rescale_projection, coeff_mk, coeff_mk, Polynomial.comp_C_mul_X_coeff, mul_comm]

@[simp] theorem rescale_one (r : ℕ) : rescale r (1 : S) = RingHom.id _ := by
  refine RingHom.ext fun x => ext_coeff r fun n hn => ?_
  simp

theorem rescale_mul (r : ℕ) (c d : S) :
    rescale r (c * d) = (rescale r c).comp (rescale r d) := by
  refine RingHom.ext fun x => ext_coeff r fun n hn => ?_
  simp [mul_pow, mul_assoc]

end TruncatedJetRing

end Coefficients

end MiyaokaMori.Jet
