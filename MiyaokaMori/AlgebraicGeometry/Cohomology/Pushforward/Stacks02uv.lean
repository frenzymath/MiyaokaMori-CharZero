import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.ExtAdjunctionExact
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.PushforwardClosedEmbeddingEpi

/-! # Closed immersions preserve cohomology (Stacks 02UV)

Closed immersions do not change cohomology (Stacks 02UV): for a closed immersion `i : Z → X` and an
abelian sheaf `F` on `Z`, `H^p(Z, F) ≅ H^p(X, i_*F)`.

This module gives a **concrete** additive isomorphism `sheafCohomologyClosedImmersionAddEquiv` and proves
that it is **natural in morphisms of `M`** (`sheafCohomologyClosedImmersionAddEquiv_naturality`); the
`Nonempty` form `sheafCohomology_closedImmersion_equiv` is a corollary. Naturality is what the downstream
`K`-linearization, equality of `χ` and equality of dimensions need.

Construction of the isomorphism (all terms explicit):
* `pushforwardAb i` (= the topological `i_*`) and `pullbackAb i` (= `i^{-1}`) form the adjunction
  `pullbackPushforwardAbAdjunction i`;
* `i^{-1}` is exact (a left adjoint preserves colimits; preservation of finite limits is Mathlib's
  `sheafPullbackConstruction.preservesFiniteLimits`, using `RepresentablyFlat` for `Opens.map`); this does
  not depend on `i` being a closed immersion;
* `i^{-1}(constant sheaf ℤ) ≅ constant sheaf ℤ`: both are left adjoint to the same functor `F ↦ Γ(Z, F)`
  (`Γ(X, i_*F) = Γ(Z, F)` holds by definition since `i⁻¹(⊤_X) = ⊤_Z`), so by uniqueness of left adjoints
  (`constantSheafPullbackAbIso`);
* hence `H^p(Z, M) = Ext(ℤ_Z, M) ≅ Ext(i^{-1} ℤ_X, M) ≅ Ext(ℤ_X, i_*M) = H^p(X, i_*M)`, the second step being
  the `Ext` isomorphism of an exact adjoint pair (`Adjunction.extAddEquiv`).

`pushforwardAb_nonempty_preservesFiniteColimits` (right exactness of `i_*` on abelian sheaves for a closed
immersion) uses that pushforward along a closed embedding preserves epimorphisms
(`PushforwardClosedEmbeddingEpi.lean`).

Source: Stacks 02UV.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- the `haveI`s below must stay inline (the `show` must match the instance terms in the body of `extAddEquiv`
-- literally); they cannot be replaced by `have`
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : AlgebraicGeometry.Scheme.{u}}

/-- The pushforward `i_*` of a morphism of schemes `i` on **abelian sheaves** (as a functor between sheaf
categories on the sites of opens). Compatible with `Scheme.Modules.pushforward`:
`((pushforward i).obj M).toAddCommGrpSheaf` and `(pushforwardAb i).obj M.toAddCommGrpSheaf` are
definitionally equal (`pushforwardAb_obj_toAddCommGrpSheaf`). -/
def pushforwardAb (i : Z ⟶ X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)

/-- The inverse image `i^{-1}` of a morphism of schemes `i` on abelian sheaves (left adjoint of
`pushforwardAb i`). -/
def pullbackAb (i : Z ⟶ X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} :=
  (Opens.map i.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)

/-- The adjunction `i^{-1} ⊣ i_*`. -/
def pullbackPushforwardAbAdjunction (i : Z ⟶ X) : pullbackAb i ⊣ pushforwardAb i :=
  (Opens.map i.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- `i^{-1}` preserves finite limits (the content of Stacks 008H; here directly from Mathlib: `Opens.map`
is representably flat, so `sheafPullback` is left exact). -/
instance preservesFiniteLimits_pullbackAb (i : Z ⟶ X) :
    CategoryTheory.Limits.PreservesFiniteLimits (pullbackAb i) :=
  CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map i.base) AddCommGrpCat.{u} _ _

/-- The pushforward `i_*` of a closed immersion preserves finite colimits on abelian sheaves (i.e. it is
right exact; left exactness is automatic for a right adjoint).

Proof:
1. `i` is a closed immersion, so `i.base` is a closed embedding (`IsClosedImmersion.isClosedEmbedding`);
2. by `TopCat.Sheaf.pushforward_preservesEpimorphisms_of_isClosedEmbedding`, `i_*` preserves
   epimorphisms;
3. `i_*` is a right adjoint, hence preserves all limits, in particular kernels; "preserves kernels + epis
   ⇒ preserves homology" is Mathlib's `CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels`,
   and `Functor.preservesFiniteColimits_of_preservesHomology` concludes.
Returned as `Nonempty` rather than an instance so that the data of the isomorphisms below stays free of
instance arguments. -/
theorem pushforwardAb_nonempty_preservesFiniteColimits (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    Nonempty (CategoryTheory.Limits.PreservesFiniteColimits (pushforwardAb i)) := by
  have _hepi : (pushforwardAb i).PreservesEpimorphisms :=
    TopCat.Sheaf.pushforward_preservesEpimorphisms_of_isClosedEmbedding i.base
      (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i)
  haveI := (pullbackPushforwardAbAdjunction i).rightAdjoint_preservesLimits
  haveI : (pushforwardAb i).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  haveI : (pushforwardAb i).PreservesHomology :=
    CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact ⟨CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology _⟩

/-- `i^{-1}` sends the constant sheaf on `X` to the constant sheaf on `Z`: both are left adjoint to
`F ↦ Γ(Z, F)`. -/
def constantSheafPullbackAbIso (i : Z ⟶ X) :
    constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ≅
      constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙ pullbackAb i :=
  Adjunction.natIsoOfRightAdjointNatIso
    (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u} isTerminalTop)
    ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).comp
      (pullbackPushforwardAbAdjunction i))
    (Iso.refl _)

/-- `i_*` agrees with `Scheme.Modules.pushforward` on objects (definitionally). -/
theorem pushforwardAb_obj_toAddCommGrpSheaf (i : Z ⟶ X) (M : Z.Modules) :
    (pushforwardAb i).obj M.toAddCommGrpSheaf
      = ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).toAddCommGrpSheaf := rfl

/-- `i_*` agrees with `Scheme.Modules.pushforward` on morphisms (definitionally). -/
theorem pushforwardAb_map_toAddCommGrpSheaf (i : Z ⟶ X) {M N : Z.Modules} (f : M ⟶ N) :
    (pushforwardAb i).map ((SheafOfModules.toSheaf Z.ringCatSheaf).map f)
      = (SheafOfModules.toSheaf X.ringCatSheaf).map
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).map f) := rfl

end AlgebraicGeometry.Scheme.Modules

/-- An isomorphism in the first variable induces an isomorphism of `Ext` (precomposition with `Ext.mk₀`). -/
def CategoryTheory.Abelian.extAddEquivOfIsoLeft {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C] {A B : C} (e : A ≅ B)
    (Y : C) (n : ℕ) :
    CategoryTheory.Abelian.Ext A Y n ≃+ CategoryTheory.Abelian.Ext B Y n where
  toFun x := (CategoryTheory.Abelian.Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (CategoryTheory.Abelian.Ext.mk₀ e.hom).comp x (zero_add n)
  left_inv x := by
    show (CategoryTheory.Abelian.Ext.mk₀ e.hom).comp
      ((CategoryTheory.Abelian.Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id,
      CategoryTheory.Abelian.Ext.mk₀_id_comp]
  right_inv x := by
    show (CategoryTheory.Abelian.Ext.mk₀ e.inv).comp
      ((CategoryTheory.Abelian.Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id,
      CategoryTheory.Abelian.Ext.mk₀_id_comp]
  map_add' x y := by
    exact map_add ((CategoryTheory.Abelian.Ext.mk₀ e.inv).precomp Y (zero_add n)) x y

/-- `extAddEquivOfIsoLeft` is natural in morphisms of the second variable (associativity). -/
theorem CategoryTheory.Abelian.extAddEquivOfIsoLeft_naturality {C : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Abelian C] [CategoryTheory.HasExt C]
    {A B : C} (e : A ≅ B) {Y Y' : C} (g : Y ⟶ Y') (n : ℕ)
    (x : CategoryTheory.Abelian.Ext A Y n) :
    CategoryTheory.Abelian.extAddEquivOfIsoLeft e Y' n
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n))
      = (CategoryTheory.Abelian.extAddEquivOfIsoLeft e Y n x).comp
          (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n) :=
  (CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
    (CategoryTheory.Abelian.Ext.mk₀ e.inv) x (CategoryTheory.Abelian.Ext.mk₀ g) (zero_add n)).symm

/-- The `Ext` isomorphism of an exact adjoint pair (`Adjunction.extAddEquiv`) is natural in morphisms of
the second variable. -/
theorem CategoryTheory.Adjunction.extAddEquiv_naturality {C D : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Category D] [CategoryTheory.Abelian C]
    [CategoryTheory.Abelian D] [CategoryTheory.HasExt C] [CategoryTheory.HasExt D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (A : C) {Y Y' : D} (g : Y ⟶ Y') (n : ℕ) (x : CategoryTheory.Abelian.Ext (F.obj A) Y n) :
    adj.extAddEquiv A Y' n (x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n))
      = (adj.extAddEquiv A Y n x).comp
          (CategoryTheory.Abelian.Ext.mk₀ (G.map g)) (add_zero n) := by
  haveI := adj.leftAdjoint_preservesColimits
  haveI := adj.rightAdjoint_preservesLimits
  haveI : F.Additive := F.additive_of_preserves_binary_products
  haveI : G.Additive := G.additive_of_preserves_binary_products
  show (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app A)).comp
      ((x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n)).mapExactFunctor G)
      (zero_add n) = _
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
  exact (CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
    (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app A)) (x.mapExactFunctor G)
    (CategoryTheory.Abelian.Ext.mk₀ (G.map g)) (zero_add n)).symm

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : AlgebraicGeometry.Scheme.{u}}

/-- **The concrete isomorphism of 02UV**: `H^p(Z, M) ≃+ H^p(X, i_*M)`, given by

`Ext(ℤ_Z, M) ≃ Ext(i^{-1} ℤ_X, M) ≃ Ext(ℤ_X, i_*M)`.

The first step is `constantSheafPullbackAbIso`, the second the `Ext` isomorphism of an exact adjoint pair. -/
def sheafCohomologyClosedImmersionAddEquiv (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (M : Z.Modules) (p : ℕ) :
    CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p ≃+
      CategoryTheory.Sheaf.H
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).toAddCommGrpSheaf p :=
  haveI := (pushforwardAb_nonempty_preservesFiniteColimits i).some
  (CategoryTheory.Abelian.extAddEquivOfIsoLeft
      ((constantSheafPullbackAbIso i).app (AddCommGrpCat.of (ULift ℤ)))
      M.toAddCommGrpSheaf p).trans
    ((pullbackPushforwardAbAdjunction i).extAddEquiv
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))) M.toAddCommGrpSheaf p)

/-- **Naturality**: the isomorphism above commutes with the maps on cohomology induced by any morphism `f`
of `M`. This is what the downstream uses (`K`-linearization, equality of `χ`, equality of dimensions)
need: taking `f` = multiplication by a global function `r` gives `Γ`-linearity. -/
theorem sheafCohomologyClosedImmersionAddEquiv_naturality (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] {M N : Z.Modules} (f : M ⟶ N) (p : ℕ)
    (α : CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p) :
    sheafCohomologyClosedImmersionAddEquiv i N p
        (CategoryTheory.Sheaf.H.map ((SheafOfModules.toSheaf Z.ringCatSheaf).map f) p α)
      = CategoryTheory.Sheaf.H.map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map
            ((AlgebraicGeometry.Scheme.Modules.pushforward i).map f)) p
          (sheafCohomologyClosedImmersionAddEquiv i M p α) := by
  haveI := (pushforwardAb_nonempty_preservesFiniteColimits i).some
  show (pullbackPushforwardAbAdjunction i).extAddEquiv _ _ p
      (CategoryTheory.Abelian.extAddEquivOfIsoLeft _ _ p
        (α.comp (CategoryTheory.Abelian.Ext.mk₀
          ((SheafOfModules.toSheaf Z.ringCatSheaf).map f)) (add_zero p))) = _
  rw [CategoryTheory.Abelian.extAddEquivOfIsoLeft_naturality,
    CategoryTheory.Adjunction.extAddEquiv_naturality]
  rfl

/-- The existence form of Stacks 02UV, a corollary of the concrete isomorphism above. -/
theorem _root_.sheafCohomology_closedImmersion_equiv
    {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (M : Z.Modules) (p : ℕ) :
    Nonempty (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p ≃+
      CategoryTheory.Sheaf.H ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).toAddCommGrpSheaf p) :=
  ⟨sheafCohomologyClosedImmersionAddEquiv i M p⟩

end AlgebraicGeometry.Scheme.Modules

end
