import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SchemeModulesPullbackFreeIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback

/-! # Pullback preserves finite type (Stacks 01B6)

The pullback of a sheaf of modules of finite type is of finite type.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 01B6: the pullback of a sheaf of modules of finite type is of finite type. -/
theorem AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (F : Y.Modules) [F.IsFiniteType] :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F).IsFiniteType := by
  open AlgebraicGeometry in
  refine Scheme.Modules.isFiniteType_of_epi_free_pullback _ fun x => ?_
  obtain ⟨U, J, hJ, π, hx, hπ⟩ :=
    Scheme.Modules.exists_epi_free_pullback_of_isFiniteType F (f x)
  -- V = f⁻¹U, f' : V ⟶ U; (V.ι)^*(f^*F) ≅ f'^*((U.ι)^*F)
  let f' : (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme := f ∣_ U
  let e : (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj F) ≅
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback U.ι).obj F) :=
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app F ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app F ≪≫
      ((Scheme.Modules.pullbackComp f' U.ι).app F).symm
  have h1 : Epi ((Scheme.Modules.pullback f').map π) :=
    @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback f') _ _ _ π hπ
  have h2 : Epi e.inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv e)
  have h3 : Epi (Scheme.Modules.pullbackObjFreeIso f' J).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  have h4 := @epi_comp _ _ _ _ _ _ h1 _ h2
  exact ⟨f ⁻¹ᵁ U, J, hJ, _, hx, @epi_comp _ _ _ _ _ _ h3 _ h4⟩

end
