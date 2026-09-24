import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineCartierFinitePresentation
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierFiniteSupport
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeAdditivity

/-!
# Cartier representatives on the integral curves of a one-cycle

The line module on a target is first pulled back to an actual integral closed curve.
Only then is a nonzero rational section chosen in that pullback's own generic stalk.
Its Cartier presentation is the one defined by `LineCartierPresentation`, with equations
equal to the coordinates of this section in actual local frames. The finite-support
and dimension lemmas of `CartierFiniteSupport` construct its actual divisor zero cycle.

`ClosedCurveCartierSection.pushforwardZeroCycle` pushes this same zero cycle to the
target with the proper pushforward `AlgebraicGeometry.AlgebraicCycle.properPushforward`.
No rational function on the target is pulled back through a non-dominant morphism.

The finite integral closed-curve presentation of the input one-cycle is an input of this
file; no presentation is chosen from an existence theorem here.
The resulting zero-cycle representatives need not agree as cycles when the rational
sections change; numerical independence is a separate assertion about their degrees.

Sources: Stacks Project, `chow.tex`, `definition-divisor-invertible-sheaf`,
`definition-cap-c1` (Tag 02SO), and `definition-degree-zero-cycle`;
Theorem 1.1 of the paper.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u v

namespace AlgebraicGeometry.Intersection

variable {k : Type u} [Field k]

/-- An actual curve in the target carries the composite structure morphism over the same field. -/
def closedCurveOver (X : AlgebraicGeometry.Proj.SchemeOver k) {W : Scheme.{u}} (i : W ⟶ X.scheme) :
    AlgebraicGeometry.Proj.SchemeOver k where
  scheme := W
  toBase := i ≫ X.toBase

/- The wrapper keeps the very same underlying scheme, but typeclass synthesis does not
   unfold this projection while elaborating a dependent field.  These transparent
   instances transport the witnesses already present on `W`; they introduce no new
   geometric assumption. -/
instance closedCurveOver_isIntegral (X : AlgebraicGeometry.Proj.SchemeOver k) {W : Scheme.{u}}
    (i : W ⟶ X.scheme) [hW : IsIntegral W] :
    IsIntegral (closedCurveOver X i).scheme := by
  change IsIntegral W
  exact hW

instance closedCurveOver_isNoetherian (X : AlgebraicGeometry.Proj.SchemeOver k) {W : Scheme.{u}}
    (i : W ⟶ X.scheme) [hW : IsNoetherian W] :
    IsNoetherian (closedCurveOver X i).scheme := by
  change IsNoetherian W
  exact hW

/-- A nonzero rational section and Cartier presentation of the actual pullback of the
specified target module. Its rank-one condition is witnessed by the presentation's frames. -/
structure ClosedCurveCartierSection (X : AlgebraicGeometry.Proj.SchemeOver k) (L : X.scheme.Modules)
    {W : Scheme.{u}} (i : W ⟶ X.scheme) [IsIntegral W] [IsNoetherian W] where
  rationalSection : ((Scheme.Modules.pullback i).obj L).presheaf.stalk (genericPoint W)
  presentation : AlgebraicGeometry.Divisors.LineCartierPresentation (closedCurveOver X i)
    ((Scheme.Modules.pullback i).obj L) rationalSection

namespace ClosedCurveCartierSection

variable {X : AlgebraicGeometry.Proj.SchemeOver k} {L : X.scheme.Modules} {W : Scheme.{u}}
    {i : W ⟶ X.scheme} [IsIntegral W] [IsNoetherian W]

/-- The section used to compute the divisor is nonzero in the actual generic stalk. -/
theorem rationalSection_ne_zero (P : ClosedCurveCartierSection X L i) :
    P.rationalSection ≠ 0 :=
  P.presentation.section_ne_zero

/-- The same pullback module, rather than an unrelated line, is locally free of rank one. -/
theorem isLocallyFreeRank (P : ClosedCurveCartierSection X L i) :
    AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank (closedCurveOver X i) ((Scheme.Modules.pullback i).obj L) 1 :=
  P.presentation.isLocallyFreeRank

/-- The divisor zero cycle computed from this section's actual local equations. -/
def divisorZeroCycle (P : ClosedCurveCartierSection X L i)
    (hdim : topologicalKrullDim W ≤ 1) : DimensionCycle W 0 :=
  P.presentation.cartier.zeroCycle hdim

/-- The coefficient is the order of this same Cartier presentation. -/
@[simp]
theorem divisorZeroCycle_apply (P : ClosedCurveCartierSection X L i)
    (hdim : topologicalKrullDim W ≤ 1) (x : W) :
    (P.divisorZeroCycle hdim).1 x = P.presentation.cartier.coefficient x := rfl

/-- Proper pushforward of the actual section divisor to the original target. -/
def pushforwardZeroCycle [IsProper i] (P : ClosedCurveCartierSection X L i)
    (hdim : topologicalKrullDim W ≤ 1) :
    DimensionCycle X.scheme 0 :=
  dimensionProperPushforward i 0 (P.divisorZeroCycle hdim)

/-- Target coefficients are the actual residue-degree-weighted sums of local divisor orders. -/
theorem pushforwardZeroCycle_apply [IsProper i] (P : ClosedCurveCartierSection X L i)
    (hdim : topologicalKrullDim W ≤ 1)
    (y : X.scheme) :
    (P.pushforwardZeroCycle hdim).1 y = ∑ᶠ x ∈ i ⁻¹' {y},
      P.presentation.cartier.coefficient x *
        (if Order.height x = Order.height (i x)
          then (i.residueDegree x : ℤ) else 0) :=
  AlgebraicGeometry.AlgebraicCycle.properPushforward_apply i (P.divisorZeroCycle hdim).1 y

/-- The divisor pushforward along a closed immersion (proper, so `pushforwardZeroCycle` applies). -/
def closedPushforwardZeroCycle [IsClosedImmersion i] (P : ClosedCurveCartierSection X L i)
    (hdim : topologicalKrullDim W ≤ 1) : DimensionCycle X.scheme 0 :=
  P.pushforwardZeroCycle hdim

end ClosedCurveCartierSection

/-- The zero cycle obtained from a finite family of actual integral closed curves, with the
specified integer multiplicities and the same target module on every branch. -/
def weightedClosedCurveCartierZeroCycle (X : AlgebraicGeometry.Proj.SchemeOver k) (L : X.scheme.Modules)
    {ι : Type v} (s : Finset ι) (multiplicity : ι → ℤ)
    (W : ι → Scheme.{u}) (i : ∀ j, W j ⟶ X.scheme)
    [∀ j, IsIntegral (W j)] [∀ j, IsNoetherian (W j)] [∀ j, IsClosedImmersion (i j)]
    (P : ∀ j, ClosedCurveCartierSection X L (i j))
    (hdim : ∀ j, topologicalKrullDim (W j) ≤ 1) : DimensionCycle X.scheme 0 :=
  DimensionCycle.weightedSum s multiplicity
    (fun j ↦ (P j).closedPushforwardZeroCycle (hdim j))

/-- The actual zero-cycle degree is the sum of the pushed section-divisor degrees with the
original integer multiplicities. This does not assert independence from the rational sections. -/
theorem rawZeroCycleDegree_weightedClosedCurveCartierZeroCycle
    (X : AlgebraicGeometry.Proj.SchemeOver k) [IsProper X.toBase] (L : X.scheme.Modules)
    {ι : Type v} (s : Finset ι) (multiplicity : ι → ℤ)
    (W : ι → Scheme.{u}) (i : ∀ j, W j ⟶ X.scheme)
    [∀ j, IsIntegral (W j)] [∀ j, IsNoetherian (W j)] [∀ j, IsClosedImmersion (i j)]
    (P : ∀ j, ClosedCurveCartierSection X L (i j))
    (hdim : ∀ j, topologicalKrullDim (W j) ≤ 1) :
    rawZeroCycleDegree X.toBase
        (weightedClosedCurveCartierZeroCycle X L s multiplicity W i P hdim) =
      ∑ j ∈ s, multiplicity j *
        rawZeroCycleDegree X.toBase ((P j).closedPushforwardZeroCycle (hdim j)) :=
  rawZeroCycleDegree_weightedSum X.toBase s multiplicity
    (fun j ↦ (P j).closedPushforwardZeroCycle (hdim j))

end AlgebraicGeometry.Intersection
