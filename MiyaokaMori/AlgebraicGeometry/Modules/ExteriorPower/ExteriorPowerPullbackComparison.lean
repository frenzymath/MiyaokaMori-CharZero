import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestriction

/-!
# The canonical exterior-power pullback comparison

For an arbitrary scheme morphism, pulling sections back by the actual
pullback-pushforward adjunction unit and then taking their wedge gives an
alternating map on every target open. These maps commute with restriction.
The exterior universal property and the original module sheafification
therefore produce a morphism to the pushforward of the exterior power.
Its adjoint is the canonical map from the pullback of the exterior power
to the exterior power of the pullback.

The unit and wedge formulas identify this actual map, including degree zero.
No isomorphism or local-freeness hypothesis is an input. Invertibility of the
constructed map remains a separate construction obligation. This provides
the comparison morphism needed for the determinant of a pullback; it does not
identify the source and target degrees.

Sources: Stacks Project, `modules.tex`, `lemma-local-tensor-algebra` and `lemma-pullback-tensor-algebra`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ)

-- Must be named: the automatic name of an anonymous `local instance` is generated from its type and
-- would collide with the instance of the same type in `ExteriorPowerStalk` ('environment already
-- contains …' when both are imported).
local instance exteriorPullbackComparisonSectionCommRing (U : Y.Opensᵒᵖ) :
    CommRing (Y.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(Y, U.unop))

/-- `Γ((pushforward f).obj N, U)` is `Γ(N, f ⁻¹ᵁ U)`, hence a `Γ(X, f ⁻¹ᵁ U)`-module; but
`Scheme.Modules.pushforward` is a plain `def`, and there is a composite functor on top
(`(F ⋙ G).obj M` and `G.obj (F.obj M)` are only defeq, not syntactically equal), so instance search
cannot see through it. This pins the instance by hand; the name carries a module prefix since a
`local instance` is local only as an attribute. -/
local instance exteriorPullbackComparisonCompSectionModule (U : Y.Opens) :
    Module ↑Γ(X, f ⁻¹ᵁ U)
      ↑Γ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).obj M, U) :=
  inferInstanceAs (Module ↑Γ(X, f ⁻¹ᵁ U) ↑Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U))


set_option backward.isDefEq.respectTransparency false in
/-- Wedge the original sections after applying the actual pullback adjunction unit. -/
def moduleExteriorPullbackAlternating (U : Y.Opens) :
    (M.val.obj (op U)).AlternatingMap
      (((Scheme.Modules.pushforward f).obj
        (moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n)).val.obj (op U)) n where
  toFun v := moduleExteriorWedge X ((Scheme.Modules.pullback f).obj M) n (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ∘ v)
  map_update_add' v j a b := by
    simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
  map_update_smul' v j r a := by
    -- Two steps: (a) pull the scalar `r` out of `φ` with `Scheme.Modules.Hom.app_smul` (this is the
    -- **linearity** of `φ`, a theorem, not a defeq); (b) the `Γ(Y,U)`-action on pushforward sections
    -- is by definition restriction of scalars along `f.app U`, which is defeq and handled by the
    -- unification in `apply`.
    simp only [Function.comp_update]
    erw [Scheme.Modules.Hom.app_smul]
    exact (moduleExteriorWedge X ((Scheme.Modules.pullback f).obj M) n
      (f ⁻¹ᵁ U)).map_update_smul' _ j _ _
  map_eq_zero_of_eq' v j l h hjl :=
    (moduleExteriorWedge X ((Scheme.Modules.pullback f).obj M) n (f ⁻¹ᵁ U)).map_eq_zero_of_eq
      _ (congrArg (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U) h) hjl

set_option backward.isDefEq.respectTransparency false in
/-- The exterior-presheaf map whose values are wedges of the actual pulled-back sections. -/
def moduleExteriorPullbackPresheafComparison :
    moduleExteriorPresheaf Y M.val n ⟶
      (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).obj
        (((Scheme.Modules.pushforward f).obj
          (moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n)).val) where
  app U := ModuleCat.exteriorPower.desc (moduleExteriorPullbackAlternating f M n U.unop)
  naturality {U V} i := by
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    change ModuleCat.exteriorPower.desc (moduleExteriorPullbackAlternating f M n V.unop)
        (exteriorRestriction Y M.val n i (ModuleCat.exteriorPower.mk v)) =
      (((Scheme.Modules.pushforward f).obj
        (moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n)).val.map i)
        (ModuleCat.exteriorPower.desc (moduleExteriorPullbackAlternating f M n U.unop)
          (ModuleCat.exteriorPower.mk v))
    rw [exteriorRestriction_mk, ModuleCat.exteriorPower.desc_mk,
      ModuleCat.exteriorPower.desc_mk]
    change moduleExteriorWedge X ((Scheme.Modules.pullback f).obj M) n (f ⁻¹ᵁ V.unop)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V.unop ∘
          (M.val.map i ∘ v)) =
      (moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map i.unop).op
        (moduleExteriorWedge X ((Scheme.Modules.pullback f).obj M) n (f ⁻¹ᵁ U.unop)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U.unop ∘ v))
    rw [moduleExteriorWedge_restrict]
    congr 1
    funext j
    exact PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val i (v j)

/-- Descend the exterior-presheaf comparison through its original sheafification. -/
def moduleExteriorPullbackAdjoint :
    moduleExteriorPower Y M n ⟶ (Scheme.Modules.pushforward f).obj
      (moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n) :=
  moduleExteriorDesc Y M n
    ((Scheme.Modules.pushforward f).obj
      (moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n))
    (moduleExteriorPullbackPresheafComparison f M n)

/-- The sheafified comparison has the prescribed composite with the exterior unit. -/
theorem moduleExteriorPullbackAdjoint_sheafificationUnit :
    moduleExteriorSheafUnit Y M n ≫
      (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
        (moduleExteriorPullbackAdjoint f M n).val =
      moduleExteriorPullbackPresheafComparison f M n :=
  moduleExteriorDesc_unit_comp Y M n _ _

set_option backward.isDefEq.respectTransparency false in
/-- The descended map wedges precisely the sections supplied by the pullback unit. -/
theorem moduleExteriorPullbackAdjoint_wedge (U : Y.Opens) (v : Fin n → Γ(M, U)) :
    (moduleExteriorPullbackAdjoint f M n).app U (moduleExteriorWedge Y M n U v) =
      moduleExteriorWedge X ((Scheme.Modules.pullback f).obj M) n (f ⁻¹ᵁ U)
        (fun i ↦ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U (v i)) := by
  rw [moduleExteriorPullbackAdjoint, moduleExteriorDesc_wedge]
  exact ModuleCat.exteriorPower.desc_mk _ _

/-- The canonical map from pullback of exterior power to exterior power of pullback. -/
def moduleExteriorPullbackComparison :
    (Scheme.Modules.pullback f).obj (moduleExteriorPower Y M n) ⟶
      moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (moduleExteriorPower Y M n)
    (moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n)).symm
    (moduleExteriorPullbackAdjoint f M n)

/-- The pullback unit followed by the constructed comparison is its specified adjoint. -/
theorem moduleExteriorPullbackComparison_unit :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (moduleExteriorPower Y M n) ≫
      (Scheme.Modules.pushforward f).map (moduleExteriorPullbackComparison f M n) =
      moduleExteriorPullbackAdjoint f M n := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _
    (moduleExteriorPullbackComparison f M n)).symm.trans
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison sends a pulled-back wedge to the wedge of pulled-back sections.
For `n = 0` this also specifies the image of the empty wedge. -/
theorem moduleExteriorPullbackComparison_wedge (U : Y.Opens) (v : Fin n → Γ(M, U)) :
    (moduleExteriorPullbackComparison f M n).app (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (moduleExteriorPower Y M n)).app U (moduleExteriorWedge Y M n U v)) =
      moduleExteriorWedge X ((Scheme.Modules.pullback f).obj M) n (f ⁻¹ᵁ U)
        (fun i ↦ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U (v i)) := by
  exact (congrArg (fun φ ↦ φ.app U (moduleExteriorWedge Y M n U v))
    (moduleExteriorPullbackComparison_unit f M n)).trans
    (moduleExteriorPullbackAdjoint_wedge f M n U v)

end AlgebraicGeometry.Scheme.Modules
