import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdeal

/-! # Ideal sheaves supported at finitely many points

The ideal sheaf determined by a point `x` and an ideal `q ⊆ O_{X,x}` of its stalk: the kernel of
`Spec(O_{X,x}/q) → Spec O_{X,x} → X`. When `q` contains a power of `𝔪_x` and `x` is a closed
point, this is the ideal sheaf with stalk `q` at `x` and the unit ideal elsewhere; multiplying
finitely many of these gives an ideal sheaf with prescribed finite cosupport and prescribed stalks.

References: Debarre, *Introduction to Mori theory*, proof of Thm 5.18 (base-point schemes);
Hartshorne II Example 7.17.3 (the base ideal of a linear system); input to Stacks 0AHH.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The ideal sheaf determined by `(x, q)`: the kernel (`Scheme.Hom.ker`) of the morphism
`Spec(O_{X,x}/q) → X`. -/
def AlgebraicGeometry.Scheme.pointIdealSheaf (X : AlgebraicGeometry.Scheme.{u}) (x : X)
    (q : Ideal (X.presheaf.stalk x)) : X.IdealSheafData :=
  (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q)) ≫ X.fromSpecStalk x).ker

/-- The ideal sheaf `∏_{x ∈ T} pointIdealSheaf x (q x)` determined by a finite set of points `T`
and an ideal `q x` of each stalk. -/
def AlgebraicGeometry.Scheme.finitePointsIdealSheaf (X : AlgebraicGeometry.Scheme.{u}) (T : Finset X)
    (q : ∀ x : X, Ideal (X.presheaf.stalk x)) : X.IdealSheafData :=
  ∏ x ∈ T, X.pointIdealSheaf x (q x)

end
