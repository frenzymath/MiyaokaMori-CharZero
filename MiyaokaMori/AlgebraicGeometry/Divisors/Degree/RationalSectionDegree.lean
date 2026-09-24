import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineCartierPresentationExistence
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveModuleDegree

/-! # The degree relation through the divisor of a rational section

(A) Let `X` be integral and locally Noetherian, `M` a module sheaf, `s` an element of the generic
stalk, and `P` any Cartier presentation of `(M, s)` (`LineCartierPresentation X M s`). Then the Cartier
coefficients of `P` equal pointwise `rationalSectionOrd M s`.
(B) Let `W` be a proper integral scheme of dimension `≤ 1` over a field `k`, `M` a line bundle on `W`
and `s` any nonzero rational section of `M`. Then the degree relation
`HasCurveModuleDegree ⟨W, W ↘ Spec k⟩ M (deg div_M(s))` holds, where `deg` is `AlgebraicCycle.degree`
(`Σ n_x [κ(x) : k]`).

Proof: (A) `x` lies in some chart `U_i` of `P`; `coefficient_eq_ord_of_mem` gives the coefficient as
`ord_x` of the local equation, `P.equation_eq` identifies the local equation with the generic
coordinate of `s` in the frame `i`, and `rationalSectionOrd_eq_ord_genericCoordinate'` (valid for any
trivialization) gives `ord_x(coordinate) = rationalSectionOrd`. (B) A line bundle is locally free of
rank one; `exists_lineCartierPresentation` gives a presentation `P` for this `s`; by (A) its zero cycle
is `div_M(s)`, and `rawZeroCycleDegree` is by definition `AlgebraicCycle.degree`.
(Stacks 02SE: the local computation of `div_L(s)` is independent of the cover.)
-/

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry AlgebraicGeometry.Divisors AlgebraicGeometry.Proj AlgebraicGeometry.Scheme.Modules
noncomputable section
namespace MiyaokaMori.RationalSectionDegree
variable {k : Type u} [Field k]

/-- The Cartier coefficients of any presentation of `(M, s)` equal `rationalSectionOrd M s`. -/
theorem coefficient_eq_rationalSectionOrd (X : SchemeOver k) [IsIntegral X.scheme]
    [IsLocallyNoetherian X.scheme] (M : X.scheme.Modules)
    (s : M.presheaf.stalk (genericPoint X.scheme)) (P : LineCartierPresentation X M s)
    (x : X.scheme) :
    P.cartier.coefficient x = Scheme.Modules.rationalSectionOrd M s x := by
  have hx := P.cartier.indexAt_mem x
  rw [P.cartier.coefficient_eq_ord_of_mem x _ hx, P.equation_eq _ ⟨⟨x, hx⟩⟩]
  exact (Scheme.Modules.rationalSectionOrd_eq_ord_genericCoordinate' M _ x hx (P.frame _) s).symm

/-- A line bundle is locally free of rank one in the sense of `IsLocallyFreeRank`. -/
theorem isLocallyFreeRank_one_of_isLineBundle (X : SchemeOver k) (M : X.scheme.Modules)
    [M.IsLineBundle] : IsLocallyFreeRank X M 1 := by
  constructor
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) x
  exact ⟨U, hx, ⟨e ≪≫ (LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).symm⟩⟩

/-- On a proper integral curve, the degree of the divisor of any nonzero rational section of a line
bundle satisfies the degree relation `HasCurveModuleDegree`. -/
theorem hasCurveModuleDegree_degree_rationalSectionDivisor {W : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k))] [IsIntegral W] [IsLocallyNoetherian W]
    (hW : IsProperOver k W) (hdim : topologicalKrullDim W ≤ 1)
    (M : W.Modules) [M.IsLineBundle] (s : M.stalk (genericPoint W)) (hs : s ≠ 0) :
    Intersection.HasCurveModuleDegree (⟨W, W ↘ Spec (CommRingCat.of k)⟩ : SchemeOver k) M
      (AlgebraicCycle.degree (k := k) (M.rationalSectionDivisor s)) := by
  have : IsProper (W ↘ Spec (CommRingCat.of k)) := hW
  have : IsNoetherian W := Intersection.properFieldScheme_isNoetherian (W ↘ Spec (CommRingCat.of k))
  let X : SchemeOver k := ⟨W, W ↘ Spec (CommRingCat.of k)⟩
  obtain ⟨P⟩ := AlgebraicGeometry.Divisors.LineCartierPresentationExistence.exists_lineCartierPresentation X M
    (isLocallyFreeRank_one_of_isLineBundle X M) s hs
  have hcyc : M.rationalSectionDivisor s = (P.cartier.zeroCycle hdim).1 := by
    ext x
    exact (coefficient_eq_rationalSectionOrd X M s P x).symm
  refine ⟨inferInstance, inferInstance, hW, hdim, s, P, ?_⟩
  rw [hcyc]
  -- `rawZeroCycleDegree X.toBase β` is by definition `AlgebraicCycle.degree β.1`
  rfl

/-- On a proper integral curve the divisor of a rational section is a zero-dimensional cycle (its
support points have height `0`). -/
theorem rationalSectionDivisor_mem_cycleSubgroup_zero {W : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k))] [IsIntegral W] [IsLocallyNoetherian W]
    (hW : IsProperOver k W) (hdim : topologicalKrullDim W ≤ 1)
    (M : W.Modules) [M.IsLineBundle] (s : M.stalk (genericPoint W)) (hs : s ≠ 0) :
    M.rationalSectionDivisor s ∈ cycleSubgroup W 0 := by
  have : IsProper (W ↘ Spec (CommRingCat.of k)) := hW
  have : IsNoetherian W := Intersection.properFieldScheme_isNoetherian (W ↘ Spec (CommRingCat.of k))
  let X : SchemeOver k := ⟨W, W ↘ Spec (CommRingCat.of k)⟩
  obtain ⟨P⟩ := AlgebraicGeometry.Divisors.LineCartierPresentationExistence.exists_lineCartierPresentation X M
    (isLocallyFreeRank_one_of_isLineBundle X M) s hs
  have hcyc : M.rationalSectionDivisor s = (P.cartier.zeroCycle hdim).1 := by
    ext x
    exact (coefficient_eq_rationalSectionOrd X M s P x).symm
  rw [hcyc]
  exact (P.cartier.zeroCycle hdim).2

end MiyaokaMori.RationalSectionDegree
end
