import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.CanonicalBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.CanonicalDivisorBundleCorrespondence
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.LinearEquivalence
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02sp

/-! # Canonical divisors

A canonical divisor `K_X` is a Cartier divisor with `O_X(K_X) ≅ ω_X = det Ω_X`; it is unique up to
linear equivalence, and `-K_X` in the paper is its negative (Theorem 1.1: `-K_X · f_*[C] > 0`,
and the degree identity `-K_X · f_*[C] = deg f^*T_X`).

A specific canonical divisor is not a canonical object, only its class is. `K_X` enters the paper only
through intersection numbers `K_X · Z`, which depend only on the isomorphism class of `O_X(K_X) ≅ ω_X`:
`D ⬝ Z = deg(c₁(O(D)) ∩ Z)` (`CartierDivisor.lineBundle_inter`). Hence no canonical divisor is chosen;
instead:
* existence: `exists_cartierDivisor_lineBundle_iso_canonicalBundle` gives some `K` with `O(K) ≅ ω_X`;
* `intersectionNumber_of_lineBundle_iso_canonicalBundle`: `K · Z = ω_X ⬝ Z` for every `K` with `O(K) ≅ ω_X`;
* `intersectionNumber_neg_of_lineBundle_iso_canonicalBundle`: `(-K) · Z = -(ω_X ⬝ Z)`.
The `if` in the definition of `firstChernClass` (the structural condition of Stacks 02TI) always holds
for varieties over `k` (`AlgebraicGeometry.firstChernClass_mk'`,
`AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over`), so `canonicalBundle X ⬝ Z` is the
genuine `c₁` intersection number.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `K` is a **canonical divisor** of `X`: `O_X(K) ≅ ω_X = det Ω_X`. A canonical divisor is determined only up to
linear equivalence (`exists_cartierDivisor_lineBundle_iso_canonicalBundle` gives existence and uniqueness up to a
principal divisor), so statements about `K_X` quantify over every `K` with `K.IsCanonical X` — the form in which
the paper's `-K_X · f_*[C] > 0` enters Theorem 1.1. A `Prop`, no chosen data. -/
def CartierDivisor.IsCanonical {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (K : CartierDivisor X.toVariety) : Prop :=
  Nonempty (K.lineBundle ≅ canonicalBundle X)

/-- For any canonical divisor `K` (`O(K) ≅ ω_X`), the intersection number with a one-cycle is the `c₁`
intersection number of the canonical bundle: `K · Z = deg(c₁(ω_X) ∩ Z)`.
Proof: `CartierDivisor.lineBundle_inter` (`D · Z = O(D) ⬝ Z`) and `LineBundle.inter_congr` (dependence
on the isomorphism class only). -/
theorem intersectionNumber_of_lineBundle_iso_canonicalBundle {k : Type u} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (K : CartierDivisor X.toVariety)
    (hK : Nonempty (K.lineBundle ≅ canonicalBundle X)) (Z : OneCycle X.toVariety) :
    intersectionNumber X K Z = canonicalBundle X ⬝ Z := by
  obtain ⟨e⟩ := hK
  rw [← CartierDivisor.lineBundle_inter K Z]
  exact LineBundle.inter_congr (modulesIsoOfLineBundleIso e) Z

/-- The anticanonical intersection number: `(-K) · Z = -(ω_X ⬝ Z)` for any canonical divisor `K`. The sign
comes from `capDivisor_neg` (the variety version of Stacks 02SP). -/
theorem intersectionNumber_neg_of_lineBundle_iso_canonicalBundle {k : Type u} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (K : CartierDivisor X.toVariety)
    (hK : Nonempty (K.lineBundle ≅ canonicalBundle X)) (Z : OneCycle X.toVariety) :
    intersectionNumber X (-K) Z = -(canonicalBundle X ⬝ Z) := by
  rw [← intersectionNumber_of_lineBundle_iso_canonicalBundle X K hK Z]
  unfold intersectionNumber
  rw [capDivisor_neg]
  simp

end
