import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLes

/-! # Cohomology of the whole space versus the cohomology presheaf at `⊤`

Sheaf cohomology of the whole space agrees with the cohomology presheaf evaluated at the terminal
object `⊤`: `H'(F, n, ⊤) ≃ H(F, n)`. The isomorphism is constructed explicitly and shown to be
natural in `F` (`H'TopIso_naturality` / `H'TopAddEquiv_comp_mk₀`).

Both sides are `Ext` groups differing only in the first variable: `H F n = Ext (constant sheaf ℤ) F n`
and `H' F n U = Ext (ℤ[h_U]^#) F n` (Mathlib's `Sheaf.H` / `Sheaf.cohomologyPresheaf` are
abbreviations for `Ext`). They are **not** definitionally equal (one underlying presheaf is
`FreeAbelianGroup (U ⟶ ⊤)`, the other `ULift ℤ`; they already differ before sheafification). The
real content is the isomorphism in the first variable

  `ℤ[h_T]^# ≅ constant sheaf ℤ`  (`T` a terminal object of the site; on `Opens X`, `T = ⊤`),

which holds **before** sheafification, so it suffices that the sheafification functor preserves
isomorphisms:
* `h_T ≅ constant presheaf PUnit` (`T` terminal ⇒ every `U ⟶ T` is a singleton type,
  `yonedaTerminalIsoConst`);
* after applying the free abelian group functor, use `Functor.constComp` and `ℤ[PUnit] ≅ ULift ℤ`
  (`FreeAbelianGroup.uniqueEquiv`);
* `constantSheaf = Functor.const ⋙ presheafToSheaf`, so after sheafification the right side is the
  constant sheaf.
Naturality is free: the isomorphism comes from the functoriality of `extFunctor n` in the first
variable, and `H'TopIso` is a component of a natural transformation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w w' u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- `ℤ[PUnit] ≅ ULift ℤ` (the free abelian group functor on a one-point type). -/
def AddCommGrpCat.freePUnitIso :
    AddCommGrpCat.free.obj PUnit.{v + 1} ≅ AddCommGrpCat.of (ULift.{v} ℤ) :=
  AddEquiv.toAddCommGrpIso
    ((FreeAbelianGroup.uniqueEquiv PUnit.{v + 1}).trans AddEquiv.ulift.symm)

/-- The representable presheaf of a terminal object is the constant presheaf `PUnit`. -/
def yonedaTerminalIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ≅ (Functor.const Cᵒᵖ).obj PUnit.{v + 1} :=
  NatIso.ofComponents
    (fun U =>
      haveI : Unique (U.unop ⟶ T) := ⟨⟨hT.from _⟩, fun _ => hT.hom_ext _ _⟩
      Equiv.toIso (Equiv.equivPUnit _))
    (by intro U V f; rfl)

/-- The free abelian presheaf `ℤ[h_T]` is isomorphic to the constant presheaf `ℤ` (`T` terminal). -/
def freeYonedaTerminalIsoConst {T : C} (hT : IsTerminal T) :
    ((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free).obj
        (yoneda.obj T)
      ≅ (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  ((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free).mapIso
      (yonedaTerminalIsoConst hT) ≪≫
    Functor.constComp Cᵒᵖ PUnit.{v + 1} AddCommGrpCat.free ≪≫
    (Functor.const Cᵒᵖ).mapIso AddCommGrpCat.freePUnitIso

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- `ℤ[h_T]^# ≅ constant sheaf ℤ` (`T` a terminal object of the site): sheafification preserves
isomorphisms. -/
def freeSheafTerminalIsoConstantSheaf {T : C} (hT : IsTerminal T) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj
        (((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free).obj
          (yoneda.obj T))
      ≅ (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{v}).mapIso (freeYonedaTerminalIsoConst hT)

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

namespace Sheaf

/-- **The cohomology presheaf at a terminal object is sheaf cohomology** (an explicit isomorphism
in `AddCommGrpCat`): `H'(F, n, T) ≅ H(F, n)`. It is the component at `F` of the natural
transformation `(extFunctor n).map (ℤ[h_T]^# ≅ constant sheaf ℤ)ᵒᵖ`, hence natural in `F`
(see `H'TopIso_naturality`). -/
def H'TopIso {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    (F.H' n T : AddCommGrpCat.{w'}) ≅ AddCommGrpCat.of (F.H n) :=
  ((Abelian.extFunctor n).mapIso (freeSheafTerminalIsoConstantSheaf J hT).symm.op).app F

/-- `H'TopIso` as an additive equivalence. -/
def H'TopAddEquiv {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    (F.H' n T : AddCommGrpCat.{w'}) ≃+ F.H n :=
  (H'TopIso J hT F n).addCommGroupIsoToAddEquiv

/-- **Naturality (elementwise)**: the isomorphism commutes with postcomposition by a sheaf
morphism `f`. Taking `f` = multiplication by a global function `r` gives `Γ`-linearity
(see `AlgebraicGeometry.sheafCohomologyTopLinearEquiv`). -/
theorem H'TopAddEquiv_comp_mk₀ {T : C} (hT : IsTerminal T) {F G : Sheaf J AddCommGrpCat.{v}}
    (f : F ⟶ G) (n : ℕ) (x : (F.H' n T : AddCommGrpCat.{w'})) :
    H'TopAddEquiv J hT G n (x.comp (Abelian.Ext.mk₀ f) (add_zero n))
      = (H'TopAddEquiv J hT F n x).comp (Abelian.Ext.mk₀ f) (add_zero n) :=
  (Abelian.Ext.comp_assoc_of_third_deg_zero _ x (Abelian.Ext.mk₀ f) (zero_add n)).symm

/-- **Naturality (categorical form)**: `H'TopIso` is a component of a natural isomorphism from
`cohomologyPresheafFunctor J n ⋙ (evaluation at T)` to `functorH J n`. -/
theorem H'TopIso_naturality {T : C} (hT : IsTerminal T) {F G : Sheaf J AddCommGrpCat.{v}}
    (f : F ⟶ G) (n : ℕ) :
    ((cohomologyPresheafFunctor J n).map f).app (op T) ≫ (H'TopIso J hT G n).hom
      = (H'TopIso J hT F n).hom ≫ AddCommGrpCat.ofHom (H.map f n) := by
  ext x
  exact H'TopAddEquiv_comp_mk₀ J hT f n x

end Sheaf

end CategoryTheory

/-- The explicit isomorphism on the site of opens of a topological space: `H'(F, n, ⊤) ≃+ H(F, n)`. -/
def CategoryTheory.Sheaf.H'TopAddEquivOpens {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) :
    (F.H' n (⊤ : TopologicalSpace.Opens X) : AddCommGrpCat.{u}) ≃+ F.H n :=
  CategoryTheory.Sheaf.H'TopAddEquiv _ isTerminalTop F n

theorem CategoryTheory.Sheaf.H'TopEquiv {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) :
    Nonempty ((F.H' n (⊤ : TopologicalSpace.Opens X) : AddCommGrpCat.{u}) ≃+ F.H n) :=
  ⟨CategoryTheory.Sheaf.H'TopAddEquiv _ isTerminalTop F n⟩

end
