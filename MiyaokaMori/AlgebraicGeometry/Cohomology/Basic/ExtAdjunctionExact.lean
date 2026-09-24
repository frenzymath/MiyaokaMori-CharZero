import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.ExtAdjunctionUnitCounit

/-! # `Ext` isomorphism induced by an exact adjunction

An adjunction `F ⊣ G` between abelian categories with `F` and `G` both exact induces
isomorphisms `Ext^n(F X, Y) ≃ Ext^n(X, G Y)`.

Source: standard homological algebra (Weibel, *An introduction to homological algebra*, 2.3.10,
compared termwise along the adjunction; a consequence of Stacks 015F).

The three proof obligations of `extAddEquiv` (`extAddEquiv_map_add`, `extAddEquiv_left_inv`,
`extAddEquiv_right_inv`) are separate theorems; the inverse laws rely on the naturality of the
unit and counit on `Ext` proved in `ExtAdjunctionUnitCounit.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Both directions are written explicitly:
   `Ext^n(F X, Y) → Ext^n(X, G Y)`: `e ↦ mk₀(η_X) ∘ G(e)` (`Ext.mapExactFunctor G`, precomposed with
   the unit `η_X : X → G F X`);
   `Ext^n(X, G Y) → Ext^n(F X, Y)`: `e ↦ F(e) ∘ mk₀(ε_Y)` (`Ext.mapExactFunctor F`, postcomposed with
   the counit `ε_Y : F G Y → Y`).
   The inverse laws (triangle identities + compatibility of `mapExactFunctor` with `comp` and `mk₀`)
   and additivity are the proof obligations. A left adjoint preserves colimits and a right adjoint
   preserves limits, so `F` and `G` are exact, hence additive. -/

section Obligations

variable {C D : Type*} [CategoryTheory.Category C] [CategoryTheory.Category D]
  [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
  [CategoryTheory.HasExt C] [CategoryTheory.HasExt D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  [CategoryTheory.Limits.PreservesFiniteLimits F]
  [CategoryTheory.Limits.PreservesFiniteColimits F]
  [CategoryTheory.Limits.PreservesFiniteLimits G]
  [CategoryTheory.Limits.PreservesFiniteColimits G]

omit [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
  [CategoryTheory.Limits.PreservesFiniteColimits F] in
/-- Additivity obligation of `extAddEquiv`: `e ↦ mk₀(η_X) ∘ G(e)` is an additive map. -/
theorem CategoryTheory.Adjunction.extAddEquiv_map_add (X : C) (Y : D) (n : ℕ)
    (e₁ e₂ : CategoryTheory.Abelian.Ext (F.obj X) Y n) :
    (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app X)).comp
        ((e₁ + e₂).mapExactFunctor G) (zero_add n)
      = (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app X)).comp
            (e₁.mapExactFunctor G) (zero_add n)
        + (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app X)).comp
            (e₂.mapExactFunctor G) (zero_add n) := by
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_add, CategoryTheory.Abelian.Ext.comp_add]

/-- Left inverse obligation of `extAddEquiv`: `F(mk₀(η_X) ∘ G(e)) ∘ mk₀(ε_Y) = e`.

Proof: compatibility of `mapExactFunctor` with `comp` and `mk₀` rewrites the left side as
`mk₀(F η_X) ∘ (F G e) ∘ mk₀(ε_Y)`; naturality of the counit on `Ext`
(`Adjunction.ext_comp_mk₀_counit`) turns the last two factors into `mk₀(ε_{F X}) ∘ e`; the triangle
identity `F η_X ≫ ε_{F X} = 𝟙` then gives `e`. -/
theorem CategoryTheory.Adjunction.extAddEquiv_left_inv (X : C) (Y : D) (n : ℕ)
    (e : CategoryTheory.Abelian.Ext (F.obj X) Y n) :
    (((CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app X)).comp
          (e.mapExactFunctor G) (zero_add n)).mapExactFunctor F).comp
        (CategoryTheory.Abelian.Ext.mk₀ (adj.counit.app Y)) (add_zero n) = e := by
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀,
    CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
    adj.ext_comp_mk₀_counit X Y n e,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]
  simp

/-- Right inverse obligation of `extAddEquiv`: `mk₀(η_X) ∘ G(F(e) ∘ mk₀(ε_Y)) = e`.

Proof: dual to the left inverse, using naturality of the unit on `Ext`
(`Adjunction.ext_mk₀_unit_comp`) and the triangle identity `η_{G Y} ≫ G ε_Y = 𝟙`. -/
theorem CategoryTheory.Adjunction.extAddEquiv_right_inv (X : C) (Y : D) (n : ℕ)
    (e : CategoryTheory.Abelian.Ext X (G.obj Y) n) :
    (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app X)).comp
        (((e.mapExactFunctor F).comp
            (CategoryTheory.Abelian.Ext.mk₀ (adj.counit.app Y)) (add_zero n)).mapExactFunctor G)
        (zero_add n) = e := by
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀,
    ← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
    adj.ext_mk₀_unit_comp X Y n e,
    CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  simp

end Obligations

/-- The additive equivalence `Ext^n(F X, Y) ≃+ Ext^n(X, G Y)` induced by an exact adjunction
`F ⊣ G`. -/
noncomputable def CategoryTheory.Adjunction.extAddEquiv {C D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
    [CategoryTheory.HasExt C] [CategoryTheory.HasExt D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [CategoryTheory.Limits.PreservesFiniteLimits F] [CategoryTheory.Limits.PreservesFiniteColimits G]
    (X : C) (Y : D) (n : ℕ) :
    CategoryTheory.Abelian.Ext (F.obj X) Y n ≃+ CategoryTheory.Abelian.Ext X (G.obj Y) n :=
  haveI := adj.leftAdjoint_preservesColimits
  haveI := adj.rightAdjoint_preservesLimits
  haveI : F.Additive := F.additive_of_preserves_binary_products
  haveI : G.Additive := G.additive_of_preserves_binary_products
  { toFun := fun e =>
      (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app X)).comp (e.mapExactFunctor G) (zero_add n)
    invFun := fun e =>
      (e.mapExactFunctor F).comp (CategoryTheory.Abelian.Ext.mk₀ (adj.counit.app Y)) (add_zero n)
    left_inv := fun e => adj.extAddEquiv_left_inv X Y n e
    right_inv := fun e => adj.extAddEquiv_right_inv X Y n e
    map_add' := fun e₁ e₂ => adj.extAddEquiv_map_add X Y n e₁ e₂ }

end
