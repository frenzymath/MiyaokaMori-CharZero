import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedAffineAlgebra
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Weighted polynomial atlases

The data form of "a graded algebra is locally a weighted polynomial algebra":
`GradedAffineAlgebra.WeightedPolynomialAtlas S w` is a family of affine opens `U i` covering `X`
together with ring isomorphisms `S(U i) ≃+* MvPolynomial σ Γ(X, U i)` identifying the graded pieces
of `S` with the weighted homogeneous components and the structure map with the constants `C`. The
predicate `IsLocallyWeightedPolynomial` is `Nonempty (WeightedPolynomialAtlas …)`.

Since a graded affine algebra is a presheaf on the affine Zariski site, restricting to an affine
open is just evaluating at it (`S.sections (U i)`); the atlas form therefore needs no pullback of
graded algebras along morphisms. The atlas only uses `GradedAffineAlgebra` and Mathlib's
`IsWeightedHomogeneous`, not a local model.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra) {σ : Type u} (w : σ → ℕ)

/-- **Weighted polynomial atlas**: an identification of `S` with the weighted polynomial algebra
on a family of affine opens covering `X` (as data, not as an existential statement). -/
structure WeightedPolynomialAtlas where
  /-- The index type of the charts. -/
  I : Type u
  /-- The affine open of the `i`-th chart. -/
  chart : I → X.AffineZariskiSite
  /-- The charts cover `X`. -/
  covers : ∀ x : X, ∃ i, x ∈ (chart i).toOpens
  /-- The ring isomorphism `S(U i) ≃ Γ(X, U i)[x_σ]` on the chart. -/
  equiv : ∀ i, S.toAffineAlgebra.sections (chart i) ≃+* MvPolynomial σ Γ(X, (chart i).toOpens)
  /-- It identifies the `m`-th piece of `S` with the homogeneous component of weight `m`. -/
  equiv_grading : ∀ (i : I) (m : ℕ) (a : S.toAffineAlgebra.sections (chart i)),
    a ∈ S.grading (chart i) m ↔ (equiv i a).IsWeightedHomogeneous w m
  /-- It identifies the structure map with the constants. -/
  equiv_unit : ∀ (i : I) (r : Γ(X, (chart i).toOpens)),
    equiv i (S.toAffineAlgebra.unitHom (chart i) r) = MvPolynomial.C r

/-- `S` is locally the weighted polynomial algebra of weights `w`. -/
def IsLocallyWeightedPolynomial : Prop := Nonempty (S.WeightedPolynomialAtlas w)

namespace WeightedPolynomialAtlas

variable {S w}

/-- The image of a homogeneous element on a chart is a weighted homogeneous polynomial. -/
theorem equiv_isWeightedHomogeneous (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) {m : ℕ}
    {a : S.toAffineAlgebra.sections (𝒜.chart i)} (ha : a ∈ S.grading (𝒜.chart i) m) :
    (𝒜.equiv i a).IsWeightedHomogeneous w m :=
  (𝒜.equiv_grading i m a).mp ha

/-- Conversely, weighted homogeneous polynomials come from the graded pieces of `S`. -/
theorem symm_mem (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) {m : ℕ}
    {p : MvPolynomial σ Γ(X, (𝒜.chart i).toOpens)} (hp : p.IsWeightedHomogeneous w m) :
    (𝒜.equiv i).symm p ∈ S.grading (𝒜.chart i) m :=
  (𝒜.equiv_grading i m _).mpr (by rw [RingEquiv.apply_symm_apply]; exact hp)

/-- Every point lies in some chart. -/
theorem exists_chart_mem (𝒜 : S.WeightedPolynomialAtlas w) (x : X) :
    ∃ i : 𝒜.I, x ∈ (𝒜.chart i).toOpens := 𝒜.covers x

end WeightedPolynomialAtlas

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
