import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.FlatOverTransport
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01b6
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt

/-! # Restricting a flat family to an affine open of the base

Let `f : Y ⟶ T`, let `M` be a sheaf of modules on `Y`, let `V ⊆ T` be an affine open,
`f_V := (f ∣_ V) ≫ (V ≅ Spec Γ(T, V)) : f⁻¹(V) ⟶ Spec Γ(T, V)`, and let `M_V` be the pullback
of `M` along the open immersion `f⁻¹(V) ⟶ Y`.

* If `M` is coherent then `M_V` is coherent (coherent = quasi-coherent + finite type, and
  both are preserved by pullback).
* If `M` is flat over `T` then `M_V` is flat over `Spec Γ(T, V)` along `f_V`. Flatness is
  defined stalkwise; the stalk map of the open immersion is an isomorphism, so the stalks of
  `M_V` are identified with those of `M`, and `morphismRestrictStalkMap` makes the module
  structures agree up to a ring isomorphism (`FlatOverTransport.isFlatOver_morphismRestrict`);
  composing with the isomorphism `V ≅ Spec Γ(T, V)` does not change flatness
  (`isFlatOver_comp_iso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

/-- The pullback of a coherent sheaf (quasi-coherent + finite type) is coherent. -/
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_pullback
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) [M.IsCoherent] :
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).IsCoherent := by
  have : M.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have : M.IsFiniteType := AlgebraicGeometry.Scheme.Modules.IsCoherent.finiteType
  exact ⟨inferInstance, AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback g M⟩

/-- The restriction of a coherent sheaf to `f⁻¹(V)` is coherent. -/
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_pullback_preimage_ι
    {Y T : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ T) (M : Y.Modules) [M.IsCoherent] (V : T.Opens) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M).IsCoherent :=
  AlgebraicGeometry.Scheme.Modules.isCoherent_pullback _ M

/-- A family flat over `T` restricts to a family flat over `Spec Γ(T, V)` for every affine
open `V ⊆ T`. -/
theorem AlgebraicGeometry.Scheme.Modules.isFlatOver_restrict_affine
    {Y T : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ T) (M : Y.Modules)
    (hM : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f M) (V : T.affineOpens) :
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver
      ((f ∣_ (V : T.Opens)) ≫ V.2.isoSpec.hom)
      ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ (V : T.Opens)).ι).obj M) :=
  MiyaokaMori.FlatOverTransport.isFlatOver_comp_iso _ _ _
    (MiyaokaMori.FlatOverTransport.isFlatOver_morphismRestrict f M hM (V : T.Opens))

end
