import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSmoothRelativeDimension
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkOfIsLineBundle

/-! # The total space projection of a line bundle is universally open

Statement: if `L` is a line bundle on a scheme `X`, the total space projection `p_L : Tot(L) → X` is
universally open; in particular its underlying map is open.

Proof: a line bundle has rank `1` at every point (`rankAtStalk_eq_one_of_isLineBundle`), so `p_L` is a
smooth morphism of relative dimension `1`; smooth ⇒ flat and locally of finite presentation
(`SmoothOfRelativeDimension.smooth`, `Smooth → Flat`, `Smooth → LocallyOfFinitePresentation`);
flat + locally of finite presentation ⇒ universally open (`UniversallyOpen.of_flat`, Stacks 01UA).

Reference: Stacks 01UA (flat morphisms of finite presentation are universally open). Used to spread
out from the generic point to general closed fibres.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.totalSpace_hom_universallyOpen {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] [V.IsLineBundle] :
    AlgebraicGeometry.UniversallyOpen (AlgebraicGeometry.Scheme.totalSpace V).hom := by
  have : AlgebraicGeometry.SmoothOfRelativeDimension 1 (AlgebraicGeometry.Scheme.totalSpace V).hom :=
    AlgebraicGeometry.Scheme.totalSpace_smoothOfRelativeDimension V 1
      (fun x => AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle V x)
  have : AlgebraicGeometry.Smooth (AlgebraicGeometry.Scheme.totalSpace V).hom :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth 1 (AlgebraicGeometry.Scheme.totalSpace V).hom
  infer_instance

/-- The underlying map of the total space projection is an open map. -/
theorem AlgebraicGeometry.Scheme.totalSpace_hom_isOpenMap {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] [V.IsLineBundle] :
    IsOpenMap (AlgebraicGeometry.Scheme.totalSpace V).hom.base := by
  have := AlgebraicGeometry.Scheme.totalSpace_hom_universallyOpen V
  exact (AlgebraicGeometry.Scheme.totalSpace V).hom.isOpenMap

end
