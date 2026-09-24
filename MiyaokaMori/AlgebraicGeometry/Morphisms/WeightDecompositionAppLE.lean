import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.WeightDefectSections

/-! # `appLE` lemmas for the weight decomposition of a `𝔾ₘ`-action

Small lemmas about `Scheme.Hom.appLE` shared by the modules on the weight decomposition of a
`𝔾ₘ`-action (`WeightDecompositionPolynomialChart`, `WeightDecompositionCoassoc`), collected here to
avoid cyclic imports:
* `appLE_hom_congr_of_eq`: equal morphisms have equal `appLE`;
* `act_comp_structure_eq`: `act ≫ q = pr₂ ≫ q` (`act_over` composed on the right with `S ↘ Spec k`);
* elementwise lemmas `appLE_comp_appLE_apply`, `appLE_congr_apply`, `appLE_top_apply`,
  `comp_appTop_apply`, `lambdaOn_eq_appLE`: every step of the weight-decomposition proofs rewrites
  with instances of these, so that all interfaces are syntactically identical (spelling differences
  such as `f ⁻¹ᵁ ⊤` versus `⊤`, or `appTop` versus `appLE ⊤ ⊤`, are only definitionally equal and
  would force the kernel to unfold everything).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace GroupSchemeAction

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}

/-- Equal morphisms have equal `appLE` (the `le` proof is transported along the equation). -/
theorem appLE_hom_congr_of_eq {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

/-- `act ≫ q = pr₂ ≫ q` (`act_over` composed on the right with `S ↘ Spec k`). -/
theorem act_comp_structure_eq (α : GmActionOver k T) :
    α.act ≫ (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
      (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
  rw [← CategoryTheory.Category.assoc, α.act_over, CategoryTheory.Category.assoc]

/-! ## Elementwise lemmas -/

/-- Every open subset is contained in `f⁻¹ ⊤` (the type is literally `W ≤ f ⁻¹ᵁ ⊤`; writing `le_top`
directly would give the type `W ≤ ⊤`, which later `rw`s do not match at implicit transparency). -/
theorem le_preimage_top {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (W : X.Opens) : W ≤ f ⁻¹ᵁ ⊤ :=
  le_top

/-- Elementwise form of `appLE_comp_appLE`: `f^♯(g^♯ x) = (f ≫ g)^♯ x`. -/
theorem appLE_comp_appLE_apply {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) =
      ((f ≫ g).appLE U W (e₂.trans ((TopologicalSpace.Opens.map f.base).map (CategoryTheory.homOfLE e₁)).le)).hom x := by
  have h := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂
  exact congrArg (fun φ : Γ(Z, U) ⟶ Γ(X, W) => φ.hom x) h

/-- Equal morphisms have elementwise equal `appLE` (for arbitrary `le` proofs). -/
theorem appLE_congr_apply {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (f.appLE U V e).hom x = (g.appLE U V e').hom x := by
  subst h; rfl

/-- `appLE` from `⊤` is "`appTop`, then restrict" (the definition of `appLE`). -/
theorem appLE_top_apply {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (W : X.Opens)
    (e : W ≤ f ⁻¹ᵁ ⊤) (x : Γ(Y, ⊤)) :
    (f.appLE ⊤ W e).hom x =
      (X.presheaf.map (CategoryTheory.homOfLE (le_top : W ≤ ⊤)).op).hom (f.appTop.hom x) := rfl

/-- Elementwise form of `comp_appTop`: `(f ≫ g)^♯ x = f^♯ (g^♯ x)`. -/
theorem comp_appTop_apply {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    ((f ≫ g).appTop).hom x = (f.appTop).hom ((g.appTop).hom x) := rfl

/-- The definition of `λ` unfolded through `appLE`: `Gm.lambdaOn q V = pr₁.appLE ⊤ (pr₂⁻¹V) (Gm.lambda k)`. -/
theorem lambdaOn_eq_appLE {T : AlgebraicGeometry.Scheme.{u}}
    (q : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (V : T.Opens) :
    Gm.lambdaOn q V =
      ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q).appLE
        ⊤ (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V)
        (le_preimage_top _ _)).hom (Gm.lambda k) := rfl

end GroupSchemeAction

end
