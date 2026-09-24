import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentFreeStalksLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentStalkFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.TorsionFreeSheaf
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverFieldDimLeOneNormal
-- The next import is not used by this file; it is kept for downstream modules that reach
-- `LocallyFreeRankBridge` through it.
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankBridge

/-! # Torsion-free coherent sheaves on a smooth curve are locally free

On a smooth projective curve the local rings are discrete valuation rings (in particular
principal ideal domains), so a finitely generated torsion-free module over them is free;
hence a torsion-free coherent sheaf is locally free.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A torsion-free coherent sheaf on a smooth projective curve is locally free. -/
theorem isLocallyFree_of_torsionFree_on_curve {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (M : C.toScheme.Modules) [M.IsCoherent]
    (hM : AlgebraicGeometry.Scheme.Modules.IsTorsionFree M) : M.IsLocallyFree := by
  apply AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_free_stalk M
  intro x
  have hsm : AlgebraicGeometry.Smooth (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    C.smooth
  obtain ⟨hdom, hpid⟩ :=
    AlgebraicGeometry.Smooth.stalk_isDomain_and_isPrincipalIdealRing_of_dim_le_one
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (le_of_eq C.dim_one) x
  have hfin : Module.Finite (C.toScheme.presheaf.stalk x) (M.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent M x
  have htf : Module.IsTorsionFree (C.toScheme.presheaf.stalk x) (M.stalk x) := hM x
  exact Module.free_of_finite_type_torsion_free'

end
