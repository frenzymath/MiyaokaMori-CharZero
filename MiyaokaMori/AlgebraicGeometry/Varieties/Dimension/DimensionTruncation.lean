import MiyaokaMori.Prelude

/-! # The truncation of dimensions to `ℕ`

The one truncation `WithBot ℕ∞ → ℕ`, `d ↦ (d.unbotD 0).toNat` (`⊥ ↦ 0`, `⊤ ↦ 0`, `n ↦ n`), behind
every `ℕ`-valued dimension of this library — `AlgebraicGeometry.Scheme.dimension`,
`Variety.dim` (an abbrev of it) and `localDimension` — and the single lemma saying when it loses
nothing: away from `⊥` (empty space) and `⊤` (infinite dimension) the truncation is the inverse of
the coercion `ℕ → WithBot ℕ∞`.

Typing convention: the primitive carriers are
`topologicalKrullDim : WithBot ℕ∞` (spaces/schemes) and `Order.height : ℕ∞` (points, in the
specialization preorder). `ℕ`-valued dimensions are truncations of these and carry information only
under hypotheses excluding `⊥` and `⊤`; the `*_spec` / `*_eq_iff` lemmas of the three modules above
state exactly those hypotheses (for a variety they are automatic: integral ⇒ nonempty, finite type
over a field ⇒ finite dimension, `Variety.dim_spec` is unconditional). Every comparison of an
`ℕ` dimension with a `WithBot ℕ∞` one goes through those lemmas, which are all one-line corollaries
of `MiyaokaMori.natCast_unbotD_toNat` below; do not repeat the `⊥`/`⊤` case analysis at use sites.

Source: elementary (`WithBot.unbotD_coe`, `ENat.natCast_toNat`); written for the convention
`dim X = n` of the paper (`X` an integral variety).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace MiyaokaMori

/-- Truncation is faithful away from `⊥` and `⊤`: `(((d.unbotD 0).toNat : ℕ) : WithBot ℕ∞) = d`. -/
theorem natCast_unbotD_toNat {d : WithBot ℕ∞} (hbot : d ≠ ⊥) (htop : d ≠ ⊤) :
    (((d.unbotD 0).toNat : ℕ) : WithBot ℕ∞) = d := by
  cases d with
  | bot => exact (hbot rfl).elim
  | coe n =>
    have hn : n ≠ ⊤ := by
      rintro rfl
      exact htop rfl
    rw [WithBot.unbotD_coe]
    exact congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) (ENat.natCast_toNat hn)

/-- The single coercion lemma for comparing a truncated dimension with an untruncated one:
away from `⊥` and `⊤`, `(d.unbotD 0).toNat = n ↔ d = n`. -/
theorem unbotD_toNat_eq_iff {d : WithBot ℕ∞} (hbot : d ≠ ⊥) (htop : d ≠ ⊤) (n : ℕ) :
    (d.unbotD 0).toNat = n ↔ d = (n : WithBot ℕ∞) := by
  constructor
  · intro h
    rw [← natCast_unbotD_toNat hbot htop, h]
  · intro h
    exact_mod_cast (natCast_unbotD_toNat hbot htop).trans h

/-- The truncation never overshoots: `((d.unbotD 0).toNat : WithBot ℕ∞) ≤ d` when `d ≠ ⊥`
(for `d = ⊥` the left side is `0`). -/
theorem natCast_unbotD_toNat_le {d : WithBot ℕ∞} (hbot : d ≠ ⊥) :
    (((d.unbotD 0).toNat : ℕ) : WithBot ℕ∞) ≤ d := by
  cases d with
  | bot => exact (hbot rfl).elim
  | coe n =>
    rw [WithBot.unbotD_coe]
    exact WithBot.coe_le_coe.mpr (ENat.natCast_toNat_le_self n)

end MiyaokaMori
