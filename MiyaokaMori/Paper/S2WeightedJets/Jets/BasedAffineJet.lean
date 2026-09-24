import MiyaokaMori.RingTheory.TruncatedJetRing
import MiyaokaMori.RingTheory.GlobalTruncatedParameter
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Based jets of an affine algebra and their coefficient equations

For an `R`-algebra `A` with a section `s : A →ₐ[R] R`, a based order-`k` jet over an
`R`-algebra `S` is an actual homomorphism `A →ₐ[R] S[t]/(t^(k+1))` whose augmentation is
`algebraMap R S ∘ s`. The truncated ring is the shared `MiyaokaMori.Jet.TruncatedJetRing`.

For an affine presentation `A = R[x₁,…,xₙ]/I`, `universalEvaluation` substitutes the
universal coordinate series `x_i(t) = s(x_i) + Σ_q X_(i,q) t^(q+1)` into the equations; its
coefficients are the equations of the based jet scheme. The coefficient *algebra* itself is
not defined here: the one definition of `J_r(B, ε)` in this library is `BasedJetAlgebra`, which represents `Point`
below (`BasedJetAlgebra.homEquiv`). The augmentation `augmentation S k` is the `S`-algebra-hom packaging of the
constant-term ring hom `GlobalTruncatedParameterAPI.epsilon k`.

Sources: §2 of the paper (the based relative jet scheme and its local description, eq. (2.4) and
eq. (2.5)); Ein–Mustață, *Jet Schemes and Singularities*, §2, Proposition 2.2 and its
affine proof. Fixing the constant coefficients is the fiber over the given section.
The geometric gluing and étale coordinate comparison are treated elsewhere.
-/

noncomputable section

namespace MiyaokaMori.BasedAffineJet

open Polynomial
open scoped BigOperators

universe u v

section TruncatedRing

variable (S : Type*) [CommRing S]

/-- The constant-term augmentation of the shared truncated polynomial ring, as an
`S`-algebra homomorphism. Its underlying ring hom is *the* augmentation
`GlobalTruncatedParameterAPI.epsilon k` (`augmentation_toRingHom`, by `rfl`); this is a
constructor of that one definition, not a second one. -/
def augmentation (k : ℕ) : Jet.TruncatedJetRing S k →ₐ[S] S :=
  { MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon k with
    commutes' := fun a => RingHom.congr_fun (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_eta k) a }

/-- The augmentation is the constant-term ring hom `epsilon`. -/
theorem augmentation_toRingHom (k : ℕ) :
    (augmentation S k : Jet.TruncatedJetRing S k →+* S) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon k := rfl

theorem augmentation_apply (k : ℕ) (z : Jet.TruncatedJetRing S k) :
    augmentation S k z = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon k z := rfl

/-- Augmenting a polynomial class evaluates its representative at zero. -/
@[simp] theorem augmentation_projection (k : ℕ) (p : S[X]) :
    augmentation S k (Jet.jetProjection S k p) = p.eval 0 := rfl

/-- The class of the parameter is nilpotent of the required order. -/
theorem parameter_pow_eq_zero (k : ℕ) :
    (Jet.jetProjection S k (X : S[X])) ^ (k + 1) = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

end TruncatedRing

section CoefficientChange

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

private theorem truncation_map_zero (k : ℕ) (f : S →ₐ[R] T)
    (p : S[X]) (hp : p ∈ Jet.truncationIdeal S k) :
    ((Ideal.Quotient.mkₐ R (Jet.truncationIdeal T k)).comp (Polynomial.mapAlgHom f)) p =
      0 := by
  -- `TruncatedJetRing` is `AdjoinRoot (X^(k+1))`, so the `→ₐ` → `→+*` coercion does not unify the codomains at
  -- instance transparency; take `.toRingHom` explicitly.
  have h : Jet.truncationIdeal S k ≤ RingHom.ker
      (((Ideal.Quotient.mkₐ R (Jet.truncationIdeal T k)).comp
        (Polynomial.mapAlgHom f)).toRingHom : S[X] →+* Jet.TruncatedJetRing T k) := by
    rw [Jet.truncationIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    change Ideal.Quotient.mk (Jet.truncationIdeal T k)
      (Polynomial.map f.toRingHom ((X : S[X]) ^ (k + 1))) = 0
    rw [Polynomial.map_pow, Polynomial.map_X]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  exact h hp

/-- An algebra homomorphism acts on a truncated jet by mapping its coefficients. -/
def mapTruncated (k : ℕ) (f : S →ₐ[R] T) :
    Jet.TruncatedJetRing S k →ₐ[R] Jet.TruncatedJetRing T k :=
  Ideal.Quotient.liftₐ (Jet.truncationIdeal S k)
    ((Ideal.Quotient.mkₐ R (Jet.truncationIdeal T k)).comp (Polynomial.mapAlgHom f))
    (truncation_map_zero k f)

/-- Mapping the class of a polynomial gives the class of its coefficientwise image. -/
@[simp] theorem mapTruncated_projection (k : ℕ) (f : S →ₐ[R] T) (p : S[X]) :
    mapTruncated k f (Jet.jetProjection S k p) =
      Jet.jetProjection T k (p.map f.toRingHom) := rfl

/-- Coefficient change commutes with the actual constant-term augmentation. -/
@[simp] theorem augmentation_mapTruncated (k : ℕ) (f : S →ₐ[R] T)
    (z : Jet.TruncatedJetRing S k) :
    augmentation T k (mapTruncated k f z) = f (augmentation S k z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change (p.map f.toRingHom).eval 0 = f.toRingHom (p.eval 0)
  simpa only [map_zero] using (Polynomial.eval_map_apply (p := p) f.toRingHom 0)

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Affine based jets are algebra homomorphisms to the actual truncated ring, with their
constant term fixed by the given section. -/
abbrev Point (s : A →ₐ[R] R) (S : Type*) [CommRing S] [Algebra R S] (k : ℕ) :=
  {j : A →ₐ[R] Jet.TruncatedJetRing S k //
    ∀ a : A, augmentation S k (j a) = algebraMap R S (s a)}

/-- The action of a coefficient algebra homomorphism on a based jet. -/
def mapPoint {s : A →ₐ[R] R} {k : ℕ} (f : S →ₐ[R] T) (j : Point s S k) :
    Point s T k :=
  ⟨(mapTruncated k f).comp j.1, fun a ↦ by
    change augmentation T k (mapTruncated k f (j.1 a)) = algebraMap R T (s a)
    rw [augmentation_mapTruncated, j.2 a]
    exact f.commutes (s a)⟩

/-- Mapping a based jet is coefficient change on its actual algebra homomorphism. -/
@[simp] theorem mapPoint_apply {s : A →ₐ[R] R} {k : ℕ} (f : S →ₐ[R] T)
    (j : Point s S k) (a : A) :
    (mapPoint f j).1 a = mapTruncated k f (j.1 a) := rfl

end CoefficientChange

section CoefficientEquations

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The affine algebra presented by the given ideal of equations. -/
abbrev PresentedAlgebra (I : Ideal (MvPolynomial (Fin n) R)) :=
  MvPolynomial (Fin n) R ⧸ I

/-- The ambient polynomial ring in the positive-order jet coefficients. -/
abbrev CoefficientPolynomialRing (R : Type u) [CommRing R] (n k : ℕ) :=
  MvPolynomial (Fin n × Fin k) R

variable {I : Ideal (MvPolynomial (Fin n) R)} (s : PresentedAlgebra I →ₐ[R] R)

/-- The constant coordinate prescribed by the actual section of the affine scheme. -/
def baseCoordinate (i : Fin n) : R :=
  s (Ideal.Quotient.mk I (MvPolynomial.X i))

/-- The universal finite coordinate series, with constant term fixed by the section. -/
def universalCoordinate (k : ℕ) (i : Fin n) : (CoefficientPolynomialRing R n k)[X] :=
  Polynomial.C (MvPolynomial.C (baseCoordinate s i)) +
    ∑ q : Fin k, Polynomial.monomial (q.val + 1) (MvPolynomial.X (i, q))

/-- Substitute the universal based coordinate series into an equation over the base. -/
def universalEvaluation (k : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] (CoefficientPolynomialRing R n k)[X] :=
  MvPolynomial.aeval (universalCoordinate s k)

end CoefficientEquations

end MiyaokaMori.BasedAffineJet
