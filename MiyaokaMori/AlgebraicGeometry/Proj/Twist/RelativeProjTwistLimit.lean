import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistComp

/-! # The twisting sheaf `O(m)` of a relative Proj as a limit

The transition maps `twistTransition` of `RelativeProjTwist` form a diagram
`twistDiagram m : X.AffineZariskiSiteᵒᵖ ⥤ (Proj_X S).Modules`, whose limit is **`O_{Proj_X S}(m)`**
(`twist m`, the gluing of Stacks 01LI). We also give the projections `twistπ` to the pushforwards of the chart
sheaves, their compatibility with the transition maps `twistπ_transition`, and the comparison map `twistChartHom`
(`ι_U^* O(m) ⟶ O_U(m)`) obtained by restricting to a chart.

Compile-time remarks. This module once took 53 s; the profiler pointed at the kernel: 27.2 s in `twistDiagram._proof_6`
(the `map_comp` field), 23.3 s in `twistπ_transition`, 2.1 s in `twistDiagram._proof_4` (the `map_id` field). Two
causes:
* `twistπ_transition`: the statement is spelled `S.twistπ … ≫ S.twistTransition …`, the instance of `limit.w` is
  spelled `limit.π … ≫ (twistDiagram m).map …`; each differs by one delta step buried under `CategoryStruct.comp`
  (an `abbrev` head). Cured by `comp_eq_of_heq_bridge` (see `RelativeProjTwistComp`).
* the fields of `twistDiagram`: Lean abstracts nested proofs in the value of a `def`; the Prop instance
  `AddSubgroup.instAddSubgroupClass` inside `Proj (S.grading U)` becomes `twistDiagram._proof_1 S U`, `leOfHom f.unop`
  becomes `_proof_2 f`, and the **type** of the auxiliary lemma `_proof_6` is abstracted as well, while the type of
  its value (`twistTransition_comp …`) is not. A node-by-node comparison found 23 differences, all of these two kinds,
  14 of them below the object and morphism arguments of `comp`. No choice of proof avoids this (the type of any proof
  term is the unabstracted spelling); the only way out is a body of `twistDiagram` with nothing to abstract: the
  objects and morphisms are wrapped in plain `def`s with atomic parameters (`twistChartPush`, `twistDiagramMap`), and
  the two fields are named theorems of the shape "constant head + atomic arguments" (which
  `Lean.Meta.AbstractNestedProofs.isNonTrivialProof` judges trivial, so they are not abstracted). The respelling happens
  inside these two theorems via the bridge lemmas. `twistChartPush` / `twistDiagramMap` are only the internal spelling
  of `twistDiagram`; the public statements (`twistπ`, `twistπ_transition`, `twistChartHom`) use the unfolded
  spelling, and `(S.twistDiagram m).obj (op U)` is definitionally equal to it.

Sources: Stacks 01LI, 01NP; Lemma 2.2 of the paper.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

-- `Proj.twist` is a `def`; it is made locally irreducible here. This module treats the `O_U(m)` on the charts as opaque
-- sheaves of modules: the fields of `twistDiagram`, the limit, `twistπ` and `twistChartHom` never need to unfold it.
-- The module also compiles without this line (only the elaboration of `twistπ_transition` goes from 0.75 s to 1.0 s);
-- it is kept as a guard on the elaborator side and has no effect on kernel time.
attribute [local irreducible] AlgebraicGeometry.Proj.twist

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- The pushforward `(ι_U)_* O_U(m)` of a chart sheaf, wrapped in a plain `def` with atomic parameters: the body of
`twistDiagram` then contains no Prop instance of `Proj (S.grading U)`, and nested-proof abstraction has nothing to
abstract (see the module docstring). Only used as the internal spelling of `twistDiagram`. -/
def twistChartPush (m : ℤ) (U : X.AffineZariskiSite) : S.relativeProj.left.Modules :=
  (Scheme.Modules.pushforward (S.projChart U)).obj (Proj.twist (S.grading U) m)

/-- The morphism part of `twistDiagram`: `twistTransition` transported to the morphisms of the index category
`X.AffineZariskiSiteᵒᵖ`. -/
def twistDiagramMap (m : ℤ) {U V : X.AffineZariskiSiteᵒᵖ} (f : U ⟶ V) :
    S.twistChartPush m U.unop ⟶ S.twistChartPush m V.unop :=
  S.twistTransition m (leOfHom f.unop)

theorem twistDiagramMap_id (m : ℤ) (U : X.AffineZariskiSiteᵒᵖ) :
    S.twistDiagramMap m (𝟙 U) = 𝟙 (S.twistChartPush m U.unop) :=
  eq_id_of_heq_bridge (S.twistTransition_id m U.unop) (S.twistDiagramMap m (𝟙 U)) rfl HEq.rfl

theorem twistDiagramMap_comp (m : ℤ) {U V W : X.AffineZariskiSiteᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    S.twistDiagramMap m (f ≫ g) = S.twistDiagramMap m f ≫ S.twistDiagramMap m g :=
  eq_comp_of_heq_bridge (S.twistTransition_comp m (leOfHom g.unop) (leOfHom f.unop))
    (S.twistDiagramMap m f) (S.twistDiagramMap m g) (S.twistDiagramMap m (f ≫ g))
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl

/-- The gluing diagram of `O(m)`. None of the four fields contains a proof that could be abstracted (see the module
docstring); do **not** inline `obj` / `map` again. -/
def twistDiagram (m : ℤ) : X.AffineZariskiSiteᵒᵖ ⥤ S.relativeProj.left.Modules where
  obj U := S.twistChartPush m U.unop
  map f := S.twistDiagramMap m f
  map_id U := S.twistDiagramMap_id m U
  map_comp f g := S.twistDiagramMap_comp m f g

/-- **O_{Proj_X S}(m)** -/
def twist (m : ℤ) : S.relativeProj.left.Modules :=
  haveI : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ S.relativeProj.left.Modules :=
    SheafOfModules.hasLimitsOfShape _ _
  limit (S.twistDiagram m)

/-- The projection `O(m) → (ι_U)_* O_U(m)` to the pushforward of a chart sheaf. -/
def twistπ (m : ℤ) (U : X.AffineZariskiSite) :
    S.twist m ⟶ (Scheme.Modules.pushforward (S.projChart U)).obj (Proj.twist (S.grading U) m) :=
  haveI : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ S.relativeProj.left.Modules :=
    SheafOfModules.hasLimitsOfShape _ _
  limit.π (S.twistDiagram m) (op U)

@[reassoc]
theorem twistπ_transition (m : ℤ) {U V : X.AffineZariskiSite} (h : U ≤ V) :
    S.twistπ m V ≫ S.twistTransition m h = S.twistπ m U :=
  haveI : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ S.relativeProj.left.Modules :=
    SheafOfModules.hasLimitsOfShape _ _
  comp_eq_of_heq_bridge (limit.w (S.twistDiagram m) (homOfLE h).op)
    (S.twistπ m V) (S.twistTransition m h) (S.twistπ m U)
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl

/-- Restriction to a chart: `ι_U^* O(m) → O_U(m)` (the adjoint transpose of `twistπ`). It is an isomorphism
    (Stacks 01LI), see `twistChartIso` and `isIso_twistChartHom`. -/
def twistChartHom (m : ℤ) (U : X.AffineZariskiSite) :
    (Scheme.Modules.pullback (S.projChart U)).obj (S.twist m) ⟶ Proj.twist (S.grading U) m :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (S.projChart U)).homEquiv _ _).symm (S.twistπ m U)

/-- `twist m` is the limit of `twistDiagram m` (a definitional equality). Once `twist` is made irreducible below, use
this lemma wherever that definitional equality is needed. -/
theorem twist_eq_limit (m : ℤ) :
    haveI : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ S.relativeProj.left.Modules :=
      SheafOfModules.hasLimitsOfShape _ _
    S.twist m = limit (S.twistDiagram m) := rfl

end AlgebraicGeometry.Scheme.GradedAffineAlgebra


/- From here on `twist` is **irreducible**. `twist m = limit (twistDiagram m)`, the objects on the charts are
`Proj.twist` (a sheafification predicate over homogeneous localizations), and a single unfolding is a huge term.
Downstream only uses `O(m)` as an opaque sheaf of modules, but as long as it is a plain `def`, the elaborator's
`isDefEq`, when unifying two types containing `O(m)`, whnf-reduces both sides all the way down to it (one downstream
module exhausted 400000 heartbeats in 21 s this way; with this attribute it takes 4 s). The attribute is kept as a
guard: the body of `O(m)` only grows, and downstream should never see it. The only places that need to unfold it are
`twistπ` / `twistπ_transition` / `twistChartHom` in this file (all above this line), `twist_eq_limit` above, and
downstream through `twist_eq` (`RelativeProjTwist`). -/
attribute [irreducible] AlgebraicGeometry.Scheme.GradedAffineAlgebra.twist


end
