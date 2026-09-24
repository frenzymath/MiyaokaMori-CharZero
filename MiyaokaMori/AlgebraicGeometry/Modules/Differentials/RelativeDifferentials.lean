import MiyaokaMori.Prelude

/-! # The sheaf of relative differentials

The sheaf of relative differentials `Ω_{X/S}`: an `O_X`-module on `X` whose value on a pair of
affine opens `U ⊆ f⁻¹V` is `Ω[Γ(X,U)⁄Γ(S,V)]`, glued along the restriction maps. This is the
sheaf `Ω_X` used in §1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `f⁻¹O_S`: the inverse image presheaf of rings of the structure sheaf of `S` along `f.base`. -/

noncomputable def AlgebraicGeometry.Scheme.inverseImagePresheaf {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) : TopCat.Presheaf CommRingCat.{u} X :=
  (TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj S.presheaf

/-- `f⁻¹O_S ⟶ O_X`: the transpose of `f.c` under the adjunction `pullback ⊣ pushforward`. -/

noncomputable def AlgebraicGeometry.Scheme.inverseImageStructureMap {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) : AlgebraicGeometry.Scheme.inverseImagePresheaf f ⟶ X.presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm f.c

noncomputable def AlgebraicGeometry.Omega {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
      (AlgebraicGeometry.Scheme.inverseImageStructureMap f))

end
