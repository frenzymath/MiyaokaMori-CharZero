import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback

/-! # `thickeningRestrict`: kernel-friendly form of "restrict a section along `i`, then transport
along `i ≫ p = g`"

Support module for `MiyaokaMori.Paper.S3PositiveLine.GenericallyScalarOfCoefficientsZero`.

`restrictToThickening L M κ P` (`ThickeningSectionsTruncated.lean`) is, by definition, the instance
`thickeningRestrict (jetNeighborhood.toTotalSpace L κ).left (totalSpace L.toModules).hom
  (jetNeighborhood.toTotalSpace_proj L κ) M.toModules P`
of the variable-level map defined here: `((pullbackComp i p).app M).hom ≫ eqToHom (i ≫ p = g)`
applied to `i^* P`.

Why a separate variable-level definition (measured):
the body of `restrictToThickening` is headed by `DFunLike.coe` (an `abbrev`) and contains
`eqToHom (congrArg _ (jetNeighborhood.toTotalSpace_proj L κ))`. Whenever the kernel compares
`restrictToThickening L M κ P` with any term that is not syntactically identical, it unfolds the
`abbrev`-headed side first and, while reducing the projection chain, computes `whnf` of the proof
`toTotalSpace_proj L κ` (the kernel unfolds theorem values), i.e. it tries to evaluate
`jetNeighborhood.toTotalSpace L κ` to a constructor. Even `restrictToThickening L M κ P = <its own body> := rfl`
exceeds the 60 s budget in the kernel (the elaborator, which does not unfold theorems, needs 8 s).
With the proof `h` a *variable*, `whnf` gets stuck at once, so every lemma below is cheap; the
concrete facts are then obtained by instantiation only (syntactic match). The definitive fix is to
make the body of `restrictToThickening` literally `thickeningRestrict … (toTotalSpace_proj L κ) …`:
then the kernel unfolds the regular head `restrictToThickening` first and compares the arguments
(proof irrelevance handles the proof), and `restrictToThickening_eq_thickeningRestrict` becomes `rfl`.
-/
/- `sectionPullbackAlong` is the one definition of the pullback of a global section (its body is the
adjunction unit) and `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback` its `Γ`-typed reducible abbrev: the sites below
use `simp only [sectionPullbackAlong_eq_pullback]` (to reach the abbrev spelling) or plain
`unfold sectionPullbackAlong` (to reach the unit). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Restrict a global section `P` of `p^* M` along `i : X ⟶ Y`, then identify `i^* p^* M` with
`g^* M` via `pullbackComp` and the transport along `h : i ≫ p = g`. Variable-level form of
`restrictToThickening` (see the module docstring). -/
noncomputable def thickeningRestrict {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (i : X ⟶ Y) (p : Y ⟶ Z) {g : X ⟶ Z} (h : i ≫ p = g) (M : Z.Modules)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u) :=
  ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i p).app M).hom ≫
      CategoryTheory.eqToHom
        (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj M) h)).val.app
      (Opposite.op ⊤)).hom
    (sectionPullbackAlong i P)

/-- Pulling back the zero section gives the zero section (the adjunction unit is linear). -/
theorem sectionPullbackAlong_zero_gsz {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) :
    sectionPullbackAlong g (0 : (M.val.obj (Opposite.op ⊤) : Type u)) = 0 := by
  unfold sectionPullbackAlong
  exact map_zero _

/-- `thickeningRestrict` is linear: it sends `0` to `0`. -/
theorem thickeningRestrict_zero {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (i : X ⟶ Y) (p : Y ⟶ Z) {g : X ⟶ Z} (h : i ≫ p = g) (M : Z.Modules) :
    thickeningRestrict i p h M 0 = 0 := by
  unfold thickeningRestrict
  rw [sectionPullbackAlong_zero_gsz]
  exact map_zero _

/-- `thickeningRestrict` of the pullback `p^* t` of a section `t ∈ Γ(Z, M)` is the pullback `g^* t`
(the `pullbackComp` half is `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp`; the transport along
`i ≫ p = g` is handled by `subst`). -/
theorem thickeningRestrict_sectionPullbackAlong {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (i : X ⟶ Y) (p : Y ⟶ Z) {g : X ⟶ Z} (h : i ≫ p = g) (M : Z.Modules)
    (t : (M.val.obj (Opposite.op ⊤) : Type u)) :
    thickeningRestrict i p h M (sectionPullbackAlong p t) = sectionPullbackAlong g t := by
  subst h
  unfold thickeningRestrict
  simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Category.comp_id]
  exact AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp i p t

end
