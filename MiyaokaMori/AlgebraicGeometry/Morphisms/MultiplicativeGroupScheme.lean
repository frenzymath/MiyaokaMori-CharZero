import MiyaokaMori.Prelude

/-! # The multiplicative group scheme

The multiplicative group scheme `G_m = Spec k[T, T⁻¹]` and its group scheme structure
(the scaling action of §2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def Gm (k : Type u) [CommRing k] : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (LaurentPolynomial k))

noncomputable instance (k : Type u) [CommRing k] :
    (Gm k).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  AlgebraicGeometry.specOverSpec

noncomputable instance (k : Type u) [CommRing k] :
    CategoryTheory.GrpObj ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))) :=
  AlgebraicGeometry.instGrpObjSpecAsOverSpec

end
