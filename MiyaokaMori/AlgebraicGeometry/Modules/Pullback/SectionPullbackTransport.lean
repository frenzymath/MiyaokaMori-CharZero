import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback

/-! # Transport lemmas for the pullback of global sections

Bookkeeping lemmas for `sectionPullbackAlong` (pullback of global sections of `𝒪`-modules), all proved:

* `Scheme.Hom.resLE_congr_hom` — `resLE` depends on the morphism only up to propositional equality;
* `eqToHom_pullback_obj_app_sectionPullbackAlong` — transport of `g^*s` along `g = g'` via `eqToHom`;
* `Modules.comp_val_app_top_hom_apply` — evaluating a composite of module morphisms on a global section;
* `sectionPullbackAlong_comp_congr` — for a commutative square `g ≫ ι' = g' ≫ ι''`, the twice pulled-back
  sections `g^*ι'^*s` and `g'^*ι''^*s` correspond under `pullbackComp ≪≫ pullbackCongr ≪≫ pullbackComp⁻¹`;
* `pullbackComp_hom_val_app_sectionPullbackAlong` — `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp` in the
  spelling of `sectionPullbackAlong`.

All statements are at the variable level (schemes, morphisms and modules are variables), which is what keeps
them cheap to check. Source: Stacks 01CY-adjacent bookkeeping (mates of the pseudofunctor structure of
`Scheme.Modules.pullback`, `ModuleSectionPullback.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Restricting a morphism to opens depends on the morphism only up to propositional equality. -/
theorem AlgebraicGeometry.Scheme.Hom.resLE_congr_hom {X Y : AlgebraicGeometry.Scheme.{u}}
    {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) :
    f.resLE U V e = f'.resLE U V e' := by
  subst h; rfl

/-- Transporting a pulled-back section along an equality of morphisms (`eqToHom` on the pullback
objects) gives the section pulled back along the other morphism. -/
theorem eqToHom_pullback_obj_app_sectionPullbackAlong {X Y : AlgebraicGeometry.Scheme.{u}}
    {g g' : X ⟶ Y} (h : g = g') {M : Y.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((CategoryTheory.eqToHom
        (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj M) h) :
        (AlgebraicGeometry.Scheme.Modules.pullback g).obj M ⟶
          (AlgebraicGeometry.Scheme.Modules.pullback g').obj M).val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong g s) = sectionPullbackAlong g' s := by
  subst h; rfl

/-- Evaluating a composite of module morphisms on a global section (definitional). -/
theorem AlgebraicGeometry.Scheme.Modules.comp_val_app_top_hom_apply {X : AlgebraicGeometry.Scheme.{u}}
    {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((φ ≫ ψ).val.app (Opposite.op ⊤)).hom x
      = (ψ.val.app (Opposite.op ⊤)).hom ((φ.val.app (Opposite.op ⊤)).hom x) := rfl

/-- **Transport across a commutative square.** If `g ≫ ι' = g' ≫ ι''`, then the twice pulled-back
sections `g^*ι'^*s` and `g'^*ι''^*s` correspond under the canonical isomorphism
`(pullbackComp g ι') ≪≫ pullbackCongr h ≪≫ (pullbackComp g' ι'')⁻¹`
(Stacks 01CY-adjacent bookkeeping; proved from `pullback_comp` / `pullbackCongr_apply`). -/
theorem sectionPullbackAlong_comp_congr {X Y Y' Z : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (ι' : Y ⟶ Z) (g' : X ⟶ Y') (ι'' : Y' ⟶ Z) (h : g ≫ ι' = g' ≫ ι'')
    {M : Z.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp g' ι'').app M).inv.val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app M).hom.val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp g ι').app M).hom.val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong g (sectionPullbackAlong ι' s))))
      = sectionPullbackAlong g' (sectionPullbackAlong ι'' s) := by
  have h1 := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp g ι' (M := M) s
  have h2 := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply h (M := M) s
  have h3 := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp_inv g' ι'' (M := M) s
  exact (congrArg (fun y =>
      (((AlgebraicGeometry.Scheme.Modules.pullbackComp g' ι'').app M).inv.val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app M).hom.val.app (Opposite.op ⊤)).hom y))
      h1).trans ((congrArg (fun y =>
      (((AlgebraicGeometry.Scheme.Modules.pullbackComp g' ι'').app M).inv.val.app (Opposite.op ⊤)).hom y)
      h2).trans h3)

/-- `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp` in the `.val.app (op ⊤)` / `sectionPullbackAlong` spelling used in
this project (variable level, so the two spellings are compared without unfolding anything concrete). -/
theorem pullbackComp_hom_val_app_sectionPullbackAlong {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (i : X ⟶ Y) (p : Y ⟶ Z) {M : Z.Modules} (t : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i p).app M).hom.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong i (sectionPullbackAlong p t))) = sectionPullbackAlong (i ≫ p) t :=
  AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp i p t

end
