import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualDualEvalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackComparisonMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameIsFrame

/-! # The dual commutes with pullback

For a locally free sheaf `F` of finite rank, the dual commutes with pullback, `(f^*F)^∨ ≃ f^*(F^∨)`,
and `F^∨∨ ≃ F`. Used for the conormal sheaf `I/I² = E^∨|_U` in §2.1 of the paper.

## Proof

Both statements are proved by the standard argument "natural map + local check on a frame"
(Stacks 01CM/01CN), formalized on the level of sections in the five helper modules
`DualPullbackCommute_{Frame, DualFrame, Eval, Theta, PullbackFrame}`:

* `dual_pullback`: the natural map `Psi f F : f^*(F^∨) ⟶ (f^*F)^∨` is the adjoint transpose of
  `Theta f F : F^∨ ⟶ f_*((f^*F)^∨)`, `φ ↦ (s ↦ f^♯(φ(s)))` (helper 4). Invertibility is local on `X`
  (`moduleHom_isIso_of_locally_isIso`); near `x` choose `V ∋ f(x)` with a finite frame `e` of `F`
  (helper 1, from `IsLocallyFree` + `IsFiniteType`). Then `unit(e^∨)` is a frame of `f^*(F^∨)` and
  `unit(e)^∨` is a frame of `(f^*F)^∨` on `f⁻¹V` (helpers 2 and 5), and `Psi` sends the first frame
  to the second because `Psi(unit(σ)) = Theta(σ)` and `Theta(eᵢ^∨)(unit(eⱼ)) = f^♯(δᵢⱼ) = δᵢⱼ`.
* `dual_dual`: the evaluation map `evHom F : F ⟶ F^∨^∨` is, in the coordinates of a frame `e` and
  its double dual frame, the identity, hence an isomorphism (helper 3).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.DualPullback

-- `res`/`res_res`/`res_self`/`res_smul` are the `Scheme.Modules` ones.
open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

open AlgebraicGeometry MiyaokaMori.ModuleDualSectionEquiv

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)

/-- `theta` sends the dual frame of `e` to the dual frame of the pulled-back frame `unit(e)`. -/
lemma theta_dualFrame {V : Y.Opens} {I : Type u} [Fintype I] {e : I → Γ(F, V)} (he : IsFrameOn F e)
    (i : I) :
    theta f F V (dualFrame he i) = dualFrame (isFrameOn_pullback f F V he) i := by
  apply ext_of_dualCoord (isFrameOn_pullback f F V he) le_rfl
  funext j
  rw [dualCoord_dualFrame]
  exact dualCoord_theta_dualFrame f F he i j

/-- `Psi f F` is an isomorphism when `F` is locally free of finite type. -/
theorem Psi_isIso [F.IsLocallyFree] [F.IsFiniteType] : IsIso (Psi f F) := by
  apply AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_of_locally_isIso
  intro x
  obtain ⟨V, I, _, e, hxV, he⟩ := exists_frame F (f.base x)
  refine ⟨f ⁻¹ᵁ V, hxV, ?_⟩
  have he1 : IsFrameOn ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F))
      (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he)) :=
    isFrameOn_pullback f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (isFrameOn_dual he)
  have he2 : IsFrameOn ((Scheme.Modules.pullback f).obj F) (unitFrame' f F V e) :=
    isFrameOn_pullback f F V he
  have he3 : IsFrameOn (AlgebraicGeometry.Scheme.Modules.moduleSheafDual ((Scheme.Modules.pullback f).obj F)) (dualFrameSec he2) :=
    isFrameOn_dual he2
  have hb1 : IsIso (frameHom _ (f ⁻¹ᵁ V) (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he))) :=
    isIso_frameHom_of_isFrameOn _ _ _ he1
  have hb3 : IsIso (frameHom _ (f ⁻¹ᵁ V) (dualFrameSec he2)) :=
    isIso_frameHom_of_isFrameOn _ _ _ he3
  have key : frameHom _ (f ⁻¹ᵁ V) (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he)) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map (Psi f F) =
      frameHom _ (f ⁻¹ᵁ V) (dualFrameSec he2) := by
    apply (((AlgebraicGeometry.Scheme.Modules.moduleSheafDual ((Scheme.Modules.pullback f).obj F)).restrict
      (f ⁻¹ᵁ V).ι).freeHomEquiv).injective
    rw [freeHomEquiv_frameHom]
    funext i
    change SheafOfModules.sectionsMap ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map (Psi f F))
      ((((Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F)).restrict (f ⁻¹ᵁ V).ι).freeHomEquiv
        (frameHom _ (f ⁻¹ᵁ V) (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he))) i) = _
    rw [freeHomEquiv_frameHom]
    apply PresheafOfModules.sections_ext
    rintro ⟨W₁⟩
    rw [frameSection_val]
    change (Psi f F).app ((f ⁻¹ᵁ V).ι ''ᵁ W₁)
        (res ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F)) ((f ⁻¹ᵁ V).ι_image_le W₁)
          (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he) i)) =
      res (AlgebraicGeometry.Scheme.Modules.moduleSheafDual ((Scheme.Modules.pullback f).obj F)) ((f ⁻¹ᵁ V).ι_image_le W₁)
        (dualFrameSec he2 i)
    have hnat := PresheafOfModules.naturality_apply (Psi f F).val
      (homOfLE ((f ⁻¹ᵁ V).ι_image_le W₁)).op (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he) i)
    change (Psi f F).app ((f ⁻¹ᵁ V).ι ''ᵁ W₁) (res _ ((f ⁻¹ᵁ V).ι_image_le W₁) _) =
      res (AlgebraicGeometry.Scheme.Modules.moduleSheafDual ((Scheme.Modules.pullback f).obj F)) ((f ⁻¹ᵁ V).ι_image_le W₁)
        ((Psi f F).app (f ⁻¹ᵁ V) (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he) i)) at hnat
    rw [hnat]
    congr 1
    change (Psi f F).app (f ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F)).app V
          (dualFrameSec he i)) = _
    rw [Psi_app_unit]
    change sectionEquiv ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V)
        (theta f F V ((sectionEquiv F V).symm (sectionEquiv F V (dualFrame he i)))) =
      sectionEquiv ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) (dualFrame he2 i)
    rw [LinearEquiv.symm_apply_apply, theta_dualFrame]
  have : IsIso (frameHom _ (f ⁻¹ᵁ V) (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he)) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map (Psi f F)) := by
    rw [key]; exact hb3
  exact IsIso.of_isIso_comp_left
    (frameHom _ (f ⁻¹ᵁ V) (unitFrame' f (AlgebraicGeometry.Scheme.Modules.moduleSheafDual F) V (dualFrameSec he))) _

end MiyaokaMori.DualPullback

theorem AlgebraicGeometry.Scheme.Modules.dual_pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (F : Y.Modules) [F.IsLocallyFree] [F.IsFiniteType] :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual F)) := by
  have := MiyaokaMori.DualPullback.Psi_isIso f F
  exact ⟨(asIso (MiyaokaMori.DualPullback.Psi f F)).symm⟩

theorem AlgebraicGeometry.Scheme.Modules.dual_dual {X : AlgebraicGeometry.Scheme.{u}}
    (F : X.Modules) [F.IsLocallyFree] [F.IsFiniteType] :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (AlgebraicGeometry.Scheme.Modules.dual F) ≅ F) := by
  have := MiyaokaMori.DualPullback.evHom_isIso F
  exact ⟨(asIso (MiyaokaMori.DualPullback.evHom F)).symm⟩

end
