import MiyaokaMori.RingTheory.TruncatedJetRing
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The canonical local truncated parameter algebra

This file is the first, algebraic part of the global-jet producer.  For a
commutative ring `R` and an order `r`, the parameter algebra is the actual
quotient `R[X] / (X^(r+1))`.  The coefficient inclusion, constant-term
augmentation, and coefficient-change maps are constructed as ordinary ring
homomorphisms, together with their strict identities.

The global relative parameter scheme and its affine gluing are deliberately
not defined here; this module contains no cone, nonzero section, tangent-rank
certificate, or gluing witness.
-/

noncomputable section

namespace MiyaokaMori.RingTheory

/-- The canonical local parameter algebra `R[X]/(X^(r+1))`.

This is the algebraic GJ0 carrier; a global scheme over a curve is a separate
construction and is not identified with this abbreviation. -/
abbrev GlobalTruncatedParameter (R : Type*) [CommRing R] (r : ℕ) :=
  Jet.TruncatedJetRing R r

namespace GlobalTruncatedParameterAPI

open Polynomial

variable {R S T : Type*}
variable [CommRing R] [CommRing S] [CommRing T]

/-! ## Canonical carrier -/

/-- The existing truncated polynomial quotient, with no second ring model. -/
abbrev carrier (R : Type*) [CommRing R] (r : ℕ) := GlobalTruncatedParameter R r

/-- Positive jet orders `1, ..., r`, represented by `Fin r`. -/
abbrev positiveOrderIndex (r : ℕ) : Type := Fin r

/-- Etale coefficient indices keep tangent rank and truncation order separate. -/
abbrev jetCoordinateIndex (n r : ℕ) : Type := Fin (n + 1) × Fin r

/-! ## Maps on the actual quotient -/

/-- The canonical inclusion of constant coefficients into the truncated ring. -/
def eta (r : ℕ) : R →+* carrier R r :=
  (Jet.jetProjection R r).comp Polynomial.C

private theorem truncation_eval_zero (r : ℕ) (p : R[X])
    (hp : p ∈ Jet.truncationIdeal R r) : p.eval 0 = 0 := by
  have h : Jet.truncationIdeal R r ≤ RingHom.ker (Polynomial.evalRingHom (0 : R)) := by
    rw [Jet.truncationIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp
  exact h hp

/-- Evaluation at the parameter value zero, i.e. the actual zero-section map. -/
def epsilon (r : ℕ) : carrier R r →+* R :=
  Ideal.Quotient.lift (Jet.truncationIdeal R r) (Polynomial.evalRingHom (0 : R))
    (truncation_eval_zero r)

private theorem truncation_map_zero (r : ℕ) (f : R →+* S) (p : R[X])
    (hp : p ∈ Jet.truncationIdeal R r) :
    ((Jet.jetProjection S r).comp (Polynomial.mapRingHom f)) p = 0 := by
  have h : Jet.truncationIdeal R r ≤ RingHom.ker
      ((Jet.jetProjection S r).comp (Polynomial.mapRingHom f)) := by
    rw [Jet.truncationIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    change Jet.jetProjection S r (((X : R[X]) ^ (r + 1)).map f) = 0
    rw [Polynomial.map_pow, Polynomial.map_X]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  exact h hp

/-- Coefficientwise transport of the actual truncated quotient along a ring map. -/
def map (r : ℕ) (f : R →+* S) : carrier R r →+* carrier S r :=
  Ideal.Quotient.lift (Jet.truncationIdeal R r)
    ((Jet.jetProjection S r).comp (Polynomial.mapRingHom f))
    (truncation_map_zero r f)

@[simp]
theorem map_projection (r : ℕ) (f : R →+* S) (p : R[X]) :
    map r f (Jet.jetProjection R r p) = Jet.jetProjection S r (p.map f) := rfl

@[simp]
theorem eta_apply (r : ℕ) (a : R) : eta r a = Jet.jetProjection R r (Polynomial.C a) := rfl

@[simp]
theorem epsilon_projection (r : ℕ) (p : R[X]) :
    epsilon r (Jet.jetProjection R r p) = p.eval 0 := rfl

/-! ## Strict identities needed by affine restriction and later gluing -/

theorem map_id (r : ℕ) : map r (RingHom.id R) = RingHom.id (carrier R r) := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change map r (RingHom.id R) (Jet.jetProjection R r p) = Jet.jetProjection R r p
  rw [map_projection, Polynomial.map_id]

theorem map_comp (r : ℕ) (f : R →+* S) (g : S →+* T) :
    map r (g.comp f) = (map r g).comp (map r f) := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change map r (g.comp f) (Jet.jetProjection R r p) =
    ((map r g).comp (map r f)) (Jet.jetProjection R r p)
  rw [map_projection, RingHom.comp_apply, map_projection, map_projection]
  rw [Polynomial.map_map]

theorem map_eta (r : ℕ) (f : R →+* S) :
    (map r f).comp (eta r) = (eta r).comp f := by
  apply RingHom.ext
  intro a
  change map r f (Jet.jetProjection R r (Polynomial.C a)) =
    Jet.jetProjection S r (Polynomial.C (f a))
  rw [map_projection]
  simp

theorem epsilon_map (r : ℕ) (f : R →+* S) :
    (epsilon r).comp (map r f) = f.comp (epsilon r) := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change epsilon r (map r f (Jet.jetProjection R r p)) =
    f (epsilon r (Jet.jetProjection R r p))
  rw [map_projection, epsilon_projection, epsilon_projection]
  simpa using (Polynomial.eval_map_apply (p := p) f 0)

theorem epsilon_eta (r : ℕ) :
    (epsilon r).comp (eta r) = RingHom.id R := by
  apply RingHom.ext
  intro a
  change epsilon r (Jet.jetProjection R r (Polynomial.C a)) = a
  rw [epsilon_projection]
  simp

end GlobalTruncatedParameterAPI

end MiyaokaMori.RingTheory
