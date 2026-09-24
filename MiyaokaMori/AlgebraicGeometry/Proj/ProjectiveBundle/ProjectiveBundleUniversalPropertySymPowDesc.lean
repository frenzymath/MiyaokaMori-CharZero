import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesRestrictMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyMonoidalPow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue

/-! # The symmetric-power descent `symPowPullbackDesc`

Companion of `ProjectiveBundleUniversalProperty.lean`.

Contents:
1. abstract braided-monoidal lemmas and the naturality of the adjacent transpositions `monoidalPowTransp`
   (`monoidalPowTransp_naturality`, `pullback_map_monoidalPowTransp`), the braiding of a line bundle is the identity
   (`braiding_hom_eq_id_of_isLineBundle`, Stacks 01CR), hence `monoidalPowTransp_eq_id_of_isLineBundle`;
2. the descent of `ψ : f^*W ⟶ M` (`M` a line bundle) to the symmetric powers:
   `symPowPullbackDesc f ψ m : f^*(Sym^m W) ⟶ M^{⊗m}` and its `dite`-transport `symGradedPullbackDesc`;
3. the degree-0 computations (`pullback_map_one_comp_symGradedPullbackDesc_zero` = `LiftData.map_one` form,
   `app_top_map_unit_app_eq`, `homEquiv_pullbackUnitIso_hom_pbup`), used by (1/6) and (5/6);
4. multiplicativity `pullback_map_symPowMul_comp_symPowPullbackDesc` /
   `pullback_map_mul_comp_symGradedPullbackDesc` (= `LiftData.map_mul` form):
   `f^*(Sym(W).mul m n) ≫ Ψ_{m+n} = δ ≫ (Ψ_m ⊗ₘ Ψ_n) ≫ (monoidalPowCat M m n).hom`, proved by transposing along
   `f^* ⊣ f_*`, cancelling the epimorphism `π_m ⊗ₘ π_n` (`symPowπ_tensorHom_cancel`) and chaining
   `tensorHom_symPowπ_symPowMul`, `pullback_map_symPowπ_comp_symPowPullbackDesc` and the compatibilities (a), (b)
   of `ProjectiveBundleUniversalPropertyMonoidalPow`; it generalises
   `pullback_map_symPowMul_symPowPullbackDesc` (`M = O_T`) to a line bundle `M`;
5. the abstract rewriting lemmas `projBundle.MulAux.chain_aux` / `inv_comp_δ_aux` used by
   `projBundle.pullback_map_mul_comp_localRingHomSheafHom` in the parent module.

Source: Stacks 01O4 (Proj represents F_1), 01CR (braiding on an invertible module), 01LQ/01M2 (maps out of the
symmetric algebra). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Three general lemmas in a braided monoidal category and two for (braided) monoidal functors: naturality
   of the adjacent transposition `α ≫ (P ◁ β) ≫ α⁻¹`, commutation with right whiskering, the
   transposition is the identity when `β = 𝟙`, and their compatibility with the comultiplication `δ` of
   the functor. Applied below to `X.Modules` and `pullback f`. -/

section MonoidalAux

open CategoryTheory.MonoidalCategory CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.LaxMonoidal
  CategoryTheory.Functor.Monoidal

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type w} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

private theorem transpAux_naturality {P P' V W : C} (a : P ⟶ P') (g : V ⟶ W) :
    ((α_ P V V).hom ≫ P ◁ (β_ V V).hom ≫ (α_ P V V).inv) ≫ ((a ⊗ₘ g) ⊗ₘ g) =
      ((a ⊗ₘ g) ⊗ₘ g) ≫ (α_ P' W W).hom ≫ P' ◁ (β_ W W).hom ≫ (α_ P' W W).inv := by
  have h : P ◁ (β_ V V).hom ≫ (a ⊗ₘ (g ⊗ₘ g)) = (a ⊗ₘ (g ⊗ₘ g)) ≫ P' ◁ (β_ W W).hom := by
    rw [tensorHom_def', ← whiskerLeft_comp_assoc, ← BraidedCategory.braiding_naturality,
      whiskerLeft_comp_assoc, whisker_exchange, Category.assoc]
  simp only [Category.assoc]
  rw [← associator_inv_naturality, reassoc_of% h, associator_naturality_assoc]

omit [BraidedCategory C] in
private theorem whiskerRight_tensorHom_comm {P P' V W : C} (a : P ⟶ P') (g : V ⟶ W) (t : P ⟶ P)
    (t' : P' ⟶ P') (ht : t ≫ a = a ≫ t') :
    (t ▷ V) ≫ (a ⊗ₘ g) = (a ⊗ₘ g) ≫ (t' ▷ W) := by
  rw [MonoidalCategory.tensorHom_def, ← comp_whiskerRight_assoc, ht, comp_whiskerRight_assoc,
    ← whisker_exchange, Category.assoc]

private theorem transpAux_eq_id {P V : C} (h : (β_ V V).hom = 𝟙 _) :
    (α_ P V V).hom ≫ P ◁ (β_ V V).hom ≫ (α_ P V V).inv = 𝟙 _ := by
  rw [h]; simp

omit [BraidedCategory C] [BraidedCategory D] in
private theorem map_whiskerRight_δ_comm (F : C ⥤ D) [F.OplaxMonoidal] {P V : C} {Q : D}
    (c : F.obj P ⟶ Q) (t : P ⟶ P) (t' : Q ⟶ Q) (h : F.map t ≫ c = c ≫ t') :
    F.map (t ▷ V) ≫ δ F P V ≫ c ▷ F.obj V = (δ F P V ≫ c ▷ F.obj V) ≫ t' ▷ F.obj V := by
  rw [← δ_natural_left_assoc, ← comp_whiskerRight, h, comp_whiskerRight, Category.assoc]

private theorem map_transpAux_δ_comm (F : C ⥤ D) [F.Braided] {P V : C} {Q : D} (c : F.obj P ⟶ Q) :
    F.map ((α_ P V V).hom ≫ P ◁ (β_ V V).hom ≫ (α_ P V V).inv) ≫
        δ F (P ⊗ V) V ≫ (δ F P V ≫ c ▷ F.obj V) ▷ F.obj V =
      (δ F (P ⊗ V) V ≫ (δ F P V ≫ c ▷ F.obj V) ▷ F.obj V) ≫
        (α_ Q (F.obj V) (F.obj V)).hom ≫ Q ◁ (β_ (F.obj V) (F.obj V)).hom ≫
          (α_ Q (F.obj V) (F.obj V)).inv := by
  have hb : F.map (β_ V V).hom ≫ δ F V V = δ F V V ≫ (β_ (F.obj V) (F.obj V)).hom := by
    rw [F.map_braiding, Category.assoc, Category.assoc, μ_δ, Category.comp_id]
  have h1' := transpAux_naturality c (𝟙 (F.obj V))
  simp only [tensorHom_id, Category.assoc] at h1'
  simp only [F.map_comp, Category.assoc, comp_whiskerRight]
  rw [← Functor.OplaxMonoidal.associativity_inv_assoc, ← δ_natural_right_assoc, ← whiskerLeft_comp_assoc, hb,
    whiskerLeft_comp_assoc, ← Functor.OplaxMonoidal.associativity_assoc, h1']

end MonoidalAux

private theorem braiding_unit_eq_id_generic {C : Type u'} [Category.{v'} C]
    [MonoidalCategory C] [BraidedCategory C] :
    (BraidedCategory.braiding (MonoidalCategoryStruct.tensorUnit C)
      (MonoidalCategoryStruct.tensorUnit C)).hom =
      CategoryStruct.id (MonoidalCategoryStruct.tensorObj (C := C)
        (MonoidalCategoryStruct.tensorUnit C) (MonoidalCategoryStruct.tensorUnit C)) := by
  rw [CategoryTheory.braiding_tensorUnit_left]
  rw [CategoryTheory.MonoidalCategory.unitors_equal]
  simp

private theorem braiding_eq_id_of_iso_unit {C : Type u'} [Category.{v'} C]
    [MonoidalCategory C] [BraidedCategory C] (M : C)
    (e : M ≅ MonoidalCategoryStruct.tensorUnit C) :
    (BraidedCategory.braiding M M).hom =
      CategoryStruct.id (MonoidalCategoryStruct.tensorObj M M) := by
  let t : MonoidalCategoryStruct.tensorObj M M ⟶
      MonoidalCategoryStruct.tensorObj (MonoidalCategoryStruct.tensorUnit C)
        (MonoidalCategoryStruct.tensorUnit C) :=
    MonoidalCategoryStruct.tensorHom e.hom e.hom
  have ht : IsIso t := by
    dsimp [t]
    infer_instance
  apply (cancel_mono t).1
  have hn := BraidedCategory.braiding_naturality e.hom e.hom
  rw [braiding_unit_eq_id_generic] at hn
  simpa [t] using hn.symm

/-- Restriction along an open immersion sends the braiding of a line bundle to the identity where the
bundle is trivialized (via `restrictFunctor_braided`). -/
private theorem restrict_braiding_eq_id_of_iso_unit
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] (M : Y.Modules)
    (e : (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj M ≅
      MonoidalCategoryStruct.tensorUnit X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
        (BraidedCategory.braiding M M).hom =
      CategoryStruct.id ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj
        (MonoidalCategoryStruct.tensorObj M M)) := by
  letI := AlgebraicGeometry.Scheme.Modules.restrictFunctor_monoidal f
  letI := AlgebraicGeometry.Scheme.Modules.restrictFunctor_braided f
  have hN := braiding_eq_id_of_iso_unit
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj M) e
  have hb := Functor.LaxBraided.braided
    (F := AlgebraicGeometry.Scheme.Modules.restrictFunctor f) M M
  rw [hN, Category.id_comp] at hb
  haveI : IsIso (Functor.LaxMonoidal.μ
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f) M M) :=
    inferInstanceAs (IsIso (Functor.Monoidal.μIso
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f) M M).hom)
  exact (cancel_epi (Functor.LaxMonoidal.μ
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor f) M M)).1
    (hb.trans (Category.comp_id _).symm)

/-- The adjacent transposition is natural in `g : V ⟶ W`: `transp_V ≫ g^{⊗m} = g^{⊗m} ≫ transp_W`
(naturality of the braiding and the associator, levelwise along the recursion of `transp`). -/

theorem AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_naturality {X : AlgebraicGeometry.Scheme.{u}}
    {V W : X.Modules} (g : V ⟶ W) : ∀ (m i : ℕ),
    AlgebraicGeometry.Scheme.Modules.monoidalPowTransp V m i ≫ AlgebraicGeometry.Scheme.Modules.monoidalPowMap g m =
      AlgebraicGeometry.Scheme.Modules.monoidalPowMap g m ≫ AlgebraicGeometry.Scheme.Modules.monoidalPowTransp W m i
  | 0, 0 => (Category.id_comp _).trans (Category.comp_id _).symm
  | 0, _ + 1 => (Category.id_comp _).trans (Category.comp_id _).symm
  | 1, 0 => (Category.id_comp _).trans (Category.comp_id _).symm
  | n + 2, 0 => transpAux_naturality (AlgebraicGeometry.Scheme.Modules.monoidalPowMap g n) g
  | 0 + 1, i + 1 => whiskerRight_tensorHom_comm (AlgebraicGeometry.Scheme.Modules.monoidalPowMap g 0) g _ _
      (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_naturality g 0 i)
  | (n + 1) + 1, i + 1 => whiskerRight_tensorHom_comm (AlgebraicGeometry.Scheme.Modules.monoidalPowMap g (n + 1)) g _ _
      (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_naturality g (n + 1) i)

/-- The braiding on a line bundle is the identity: `β_{M,M} = 𝟙` (a consequence of Stacks 01CR; false for
general modules, e.g. `M = O ⊕ O`). Proof: (1) equality of morphisms of sheaves can be checked on an open
cover; on a trivializing cover `{U}` of `M`, the restriction functor `restrict U.ι` is braided monoidal
(`restrict ≅ pullback U.ι`), so `β_{M,M}|_U` is conjugate to `β_{O,O}` by `e : M|_U ≅ O_U`; (2) on the
unit object `β_{𝟙,𝟙} = 𝟙` (Mathlib `CategoryTheory.BraidedCategory.braiding_tensorUnit_*`:
`β_{𝟙,X} = λ ≫ ρ⁻¹` and `λ_𝟙 = ρ_𝟙` by `unitors_equal`); (3) naturality of the braiding
`(e ⊗ e) ≫ β_{O,O} = β_{M|U,M|U} ≫ (e ⊗ e)` with `e ⊗ e` an isomorphism gives `β_{M|U,M|U} = 𝟙`. -/

theorem AlgebraicGeometry.Scheme.Modules.braiding_hom_eq_id_of_isLineBundle {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLineBundle] :
    (BraidedCategory.braiding M M).hom = CategoryStruct.id (MonoidalCategoryStruct.tensorObj M M) := by
  let hU := fun x : X => SheafOfModules.IsLineBundle.locally_trivial (M := M) x
  let U : X → X.Opens := fun x => (hU x).choose
  let e : ∀ x, M.restrict (U x).ι ≅ SheafOfModules.unit (U x).toScheme.ringCatSheaf :=
    fun x => (hU x).choose_spec.2.some
  have hUtop : ⨆ x, U x = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, (hU x).choose_spec.1⟩
  apply AlgebraicGeometry.Scheme.Modules.hom_ext_of_cover U hUtop _ _
  intro x
  let f := (U x).ι
  rw [(AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map_id]
  exact restrict_braiding_eq_id_of_iso_unit f M (e x)

/-- All adjacent transpositions on the tensor powers of a line bundle are the identity (from the previous
lemma, levelwise along the recursion of `transp`). -/

theorem AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_eq_id_of_isLineBundle
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsLineBundle] : ∀ (m i : ℕ),
    AlgebraicGeometry.Scheme.Modules.monoidalPowTransp M m i = CategoryStruct.id (AlgebraicGeometry.Scheme.Modules.monoidalPow M m)
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | 1, 0 => rfl
  | _ + 2, 0 => transpAux_eq_id (AlgebraicGeometry.Scheme.Modules.braiding_hom_eq_id_of_isLineBundle M)
  | 0 + 1, i + 1 =>
    (congrArg (fun t => MonoidalCategoryStruct.whiskerRight t M)
      (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_eq_id_of_isLineBundle M 0 i)).trans (MonoidalCategory.id_whiskerRight _ _)
  | (n + 1) + 1, i + 1 =>
    (congrArg (fun t => MonoidalCategoryStruct.whiskerRight t M)
      (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_eq_id_of_isLineBundle M (n + 1) i)).trans (MonoidalCategory.id_whiskerRight _ _)

/-- Pullback commutes with the adjacent transpositions:
`f^*(transp_W) ≫ (f^*(W^{⊗m}) → (f^*W)^{⊗m}) = (the same comparison morphism) ≫ transp_{f^*W}`.
The comultiplication `δ` of `pullback f` is by definition `pullbackTensorObjHom` (the inverse of the
`μIso` of `CoreMonoidal`), so this follows from the general lemmas `map_transpAux_δ_comm` (associativity,
naturality and braiding compatibility of `δ`) and `map_whiskerRight_δ_comm` (naturality of `δ`) along
the recursion of `transp`. -/

theorem AlgebraicGeometry.Scheme.Modules.pullback_map_monoidalPowTransp {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (W : Y.Modules) : ∀ (m i : ℕ),
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp W m i) ≫ AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow f W m =
      AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow f W m ≫
        AlgebraicGeometry.Scheme.Modules.monoidalPowTransp ((AlgebraicGeometry.Scheme.Modules.pullback f).obj W) m i
  | 0, 0 => by
    refine ((congrArg (· ≫ _) ((AlgebraicGeometry.Scheme.Modules.pullback f).map_id _)).trans (Category.id_comp _)).trans
      (Category.comp_id _).symm
  | 0, _ + 1 => by
    refine ((congrArg (· ≫ _) ((AlgebraicGeometry.Scheme.Modules.pullback f).map_id _)).trans (Category.id_comp _)).trans
      (Category.comp_id _).symm
  | 1, 0 => by
    refine ((congrArg (· ≫ _) ((AlgebraicGeometry.Scheme.Modules.pullback f).map_id _)).trans (Category.id_comp _)).trans
      (Category.comp_id _).symm
  | n + 2, 0 => map_transpAux_δ_comm (AlgebraicGeometry.Scheme.Modules.pullback f) (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow f W n)
  | 0 + 1, i + 1 => map_whiskerRight_δ_comm (AlgebraicGeometry.Scheme.Modules.pullback f) (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow f W 0) _ _
      (AlgebraicGeometry.Scheme.Modules.pullback_map_monoidalPowTransp f W 0 i)
  | (n + 1) + 1, i + 1 => map_whiskerRight_δ_comm (AlgebraicGeometry.Scheme.Modules.pullback f) (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow f W (n + 1)) _ _
      (AlgebraicGeometry.Scheme.Modules.pullback_map_monoidalPowTransp f W (n + 1) i)

/-- Descent of the pullback to symmetric powers: `ψ : f^*W ⟶ M` induces `f^*(Sym^m W) ⟶ M^{⊗m}` for a line
bundle `M`. The composite `f^*(W^{⊗m}) → (f^*W)^{⊗m} →(ψ^{⊗m}) M^{⊗m}` corresponds under the
pullback–pushforward adjunction to `W^{⊗m} → f_*(M^{⊗m})`; this is invariant under the adjacent
transpositions (`pullback_map_monoidalPowTransp`, `monoidalPowTransp_naturality`, and the transpositions
on a line bundle are the identity), so it descends along the quotient map to `Sym^m W` (`symPowDesc`),
and the adjunction brings it back to `f^*(Sym^m W)`.
The hypothesis `[M.IsLineBundle]` is necessary for the transposition invariance: for `X = Y = Spec k`,
`f = 𝟙`, `W = M = O ⊕ O`, `ψ` an isomorphism and `m = 2`, invariance would mean that the transposition on
`M ⊗ M` is the identity, but `e₁⊗e₂ ≠ e₂⊗e₁`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symPowPullbackDesc {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) {W : Y.Modules} {M : X.Modules} [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj W ⟶ M) (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.symPow W m) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow M m :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (AlgebraicGeometry.Scheme.Modules.symPowDesc W m
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow f W m ≫
          AlgebraicGeometry.Scheme.Modules.monoidalPowMap ψ m))
      (fun i => by
        rw [← CategoryTheory.Adjunction.homEquiv_naturality_left, ← Category.assoc,
          AlgebraicGeometry.Scheme.Modules.pullback_map_monoidalPowTransp, Category.assoc,
          AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_naturality,
          AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_eq_id_of_isLineBundle, Category.comp_id]))

/-- The descent on the `m`-th piece of `Sym(W)`. `symGradedAlgebra` is a `dite` on whether `W` is
quasi-coherent: the quasi-coherent branch (`Sym^m W`) uses `symPowPullbackDesc`; the trivial branch (`W`
not quasi-coherent; it does not occur for `W = V^∨` with `V` locally free) takes the zero morphism. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) {W : Y.Modules} {M : X.Modules} [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj W ⟶ M) (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).part m) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow M m := by
  unfold AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
  split
  · exact AlgebraicGeometry.Scheme.Modules.symPowPullbackDesc f ψ m
  · exact 0

/-! ## Degree-zero computations

The unfoldings of `monoidalPowMap`, `unitPowCollapse`, `pullbackMonoidalPow` at `m = 0`; `symPowπ`
followed by `symPowPullbackDesc` is the tensor-power map; in the quasi-coherent branch
`symGradedPullbackDesc` equals `symPowPullbackDesc` (heterogeneously); hence the identity
`f^*(S.one) ≫ Ψ_0 = (pullbackUnitIso f).hom` in the form of `LiftData.map_one` (for any line bundle `M`;
`pullback_map_one_symGradedPullbackDesc_zero` is the special case `M = O`).

`set_option backward.isDefEq.respectTransparency.types false`: in this file
`SheafOfModules.unit X.ringCatSheaf` and `𝟙_ X.Modules`, and `TopCat.Sheaf` and
`Sheaf (Opens.grothendieckTopology _)`, are equal only after unfolding `def`s, which Lean does not do
by default in the type checks of `rw`/`simp` (Mathlib's `AlgebraicGeometry/Modules/Sheaf.lean` disables
the option in the same way); without it, `rw [Category.comp_id]` and the like find no pattern. -/

section ZeroDegreeLemmas

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules

theorem monoidalPowMap_zero_eq_id {X : AlgebraicGeometry.Scheme.{u}} {V W : X.Modules} (g : V ⟶ W) :
    monoidalPowMap g 0 = 𝟙 _ := rfl

theorem unitPowCollapse_zero_eq_id (X : AlgebraicGeometry.Scheme.{u}) : unitPowCollapse X 0 = 𝟙 _ := rfl

theorem pullbackMonoidalPow_zero_eq_unitIso {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (W : Y.Modules) :
    pullbackMonoidalPow f W 0 = (pullbackUnitIso f).hom := rfl

/-- `f^*(symPowπ W m) ≫ symPowPullbackDesc f ψ m` is the tensor-power map `pullbackMonoidalPow ≫ ψ^{⊗m}`
(definition + `symPowπ_desc`). -/
theorem pullback_map_symPowπ_comp_symPowPullbackDesc {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) {M : T.Modules} [M.IsLineBundle] (ψ : (pullback g).obj W ⟶ M) (m : ℕ) :
    (pullback g).map (symPowπ W m) ≫ symPowPullbackDesc g ψ m =
      pullbackMonoidalPow g W m ≫ monoidalPowMap ψ m := by
  unfold symPowPullbackDesc
  rw [← Adjunction.homEquiv_naturality_left_symm, symPowπ_desc, Equiv.symm_apply_apply]

private theorem casesOn_const_pbup {P : Prop} {T : Type u} (d : Decidable P) (f : ¬P → T) (g : P → T)
    (hp : P) : Decidable.casesOn (motive := fun _ => T) d f g = g hp := by
  cases d with
  | isFalse h => exact absurd hp h
  | isTrue h => rfl

/-- Quasi-coherent branch: `symGradedPullbackDesc` is `symPowPullbackDesc` (heterogeneous equality). -/
theorem symGradedPullbackDesc_heq_of_isQuasicoherent {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    {W : Y.Modules} (hq : W.IsQuasicoherent) {M : X.Modules} [M.IsLineBundle]
    (ψ : (pullback f).obj W ⟶ M) (m : ℕ) :
    HEq (symGradedPullbackDesc f ψ m) (symPowPullbackDesc f ψ m) := by
  unfold symGradedPullbackDesc
  rw [casesOn_const_pbup _ _ _ hq]
  exact cast_heq _ _

private theorem symGradedAlgebra_eq_ofQC_pbup {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules)
    (hq : W.IsQuasicoherent) : symGradedAlgebra W = symGradedAlgebraOfQC W hq := by
  delta symGradedAlgebra
  exact dif_pos hq

private theorem pullback_map_one_comp_symGradedPullbackDesc_zero_aux {X T : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) (W : X.Modules) (hq : W.IsQuasicoherent) {M : T.Modules} [M.IsLineBundle]
    (ψ : (pullback g).obj W ⟶ M)
    (S : X.GradedQCAlgebra) (hS : S = symGradedAlgebraOfQC W hq)
    (D : (pullback g).obj (S.part 0) ⟶ monoidalPow M 0)
    (hD : HEq D (symPowPullbackDesc g ψ 0)) :
    (pullback g).map S.one ≫ D = (pullbackUnitIso g).hom := by
  subst hS
  have hD' : D = symPowPullbackDesc g ψ 0 := eq_of_heq hD
  subst hD'
  show (pullback g).map (symPowπ W 0) ≫ symPowPullbackDesc g ψ 0 = (pullbackUnitIso g).hom
  refine (pullback_map_symPowπ_comp_symPowPullbackDesc g W ψ 0).trans ?_
  show pullbackMonoidalPow g W 0 ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- **`LiftData.map_one` form**: for `W` quasi-coherent,
`g^*(Sym(W).one) ≫ symGradedPullbackDesc g ψ 0 = (pullbackUnitIso g).hom` (`M` any line bundle). -/
theorem pullback_map_one_comp_symGradedPullbackDesc_zero {X T : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) (W : X.Modules) (hq : W.IsQuasicoherent) {M : T.Modules} [M.IsLineBundle]
    (ψ : (pullback g).obj W ⟶ M) :
    (pullback g).map (symGradedAlgebra W).one ≫ symGradedPullbackDesc g ψ 0 =
      (pullbackUnitIso g).hom :=
  pullback_map_one_comp_symGradedPullbackDesc_zero_aux g W hq ψ _ (symGradedAlgebra_eq_ofQC_pbup W hq) _
    (symGradedPullbackDesc_heq_of_isQuasicoherent g hq ψ 0)

/-- Under the pullback–pushforward adjunction, the value of `Φ : g^*A ⟶ B` on a section obtained by the
adjunction unit and restriction to `⊤ ≤ g⁻¹W` equals the value of the adjoint transpose of `Φ` on `W`,
restricted (naturality of `Φ` + `Adjunction.homEquiv_unit`). -/
theorem app_top_map_unit_app_eq {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    {A : X.Modules} {B : T.Modules} (Φ : (pullback g).obj A ⟶ B) (W : X.Opens)
    (hgW : (⊤ : T.Opens) ≤ g ⁻¹ᵁ W) (s : A.val.obj (op W)) :
    (Φ.val.app (op ⊤)).hom
        (((pullback g).obj A).presheaf.map (homOfLE hgW).op
          ((((pullbackPushforwardAdjunction g).unit.app A).val.app (op W)).hom s)) =
      (B.presheaf.map (homOfLE hgW).op).hom
        ((((pullbackPushforwardAdjunction g).homEquiv A B Φ).val.app (op W)).hom s) := by
  rw [Adjunction.homEquiv_unit]
  have hn := Φ.val.naturality (homOfLE hgW).op
  exact congrArg (fun k => k.hom ((((pullbackPushforwardAdjunction g).unit.app A).val.app (op W)).hom s)) hn

/-- The adjoint transpose of `pullbackUnitIso g` is Mathlib's `unitToPushforwardObjUnit` (on sections,
`g^♯`). -/
theorem homEquiv_pullbackUnitIso_hom_pbup {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) :
    (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
  haveI : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction g).isRightAdjoint
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u} g.toRingCatSheafHom

end AlgebraicGeometry.Scheme.Modules

end ZeroDegreeLemmas

open scoped CategoryTheory.MonoidalCategory

/-! ## (S3a) multiplicativity of `symPowPullbackDesc` / `symGradedPullbackDesc` for a line bundle `M` -/

section SymPowDescMul

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.MonoidalCategory

variable {X T : AlgebraicGeometry.Scheme.{u}}

theorem pullback_map_symPowMul_comp_symPowPullbackDesc (g : T ⟶ X) (W : X.Modules)
    {M : T.Modules} [M.IsLineBundle] (ψ : (pullback g).obj W ⟶ M) (m n : ℕ) :
    (pullback g).map (symPowMul W m n) ≫ symPowPullbackDesc g ψ (m + n) =
      pullbackTensorObjHom g (symPow W m) (symPow W n) ≫
        (symPowPullbackDesc g ψ m ⊗ₘ symPowPullbackDesc g ψ n) ≫ (monoidalPowCat M m n).hom := by
  apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply symPowπ_tensorHom_cancel W m n
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  congr 1
  have hR : (pullback g).map (symPowπ W m ⊗ₘ symPowπ W n) ≫ pullbackTensorObjHom g (symPow W m) (symPow W n) ≫
        (symPowPullbackDesc g ψ m ⊗ₘ symPowPullbackDesc g ψ n) ≫ (monoidalPowCat M m n).hom =
      pullbackTensorObjHom g (monoidalPow W m) (monoidalPow W n) ≫
        (((pullback g).map (symPowπ W m) ≫ symPowPullbackDesc g ψ m) ⊗ₘ
          ((pullback g).map (symPowπ W n) ≫ symPowPullbackDesc g ψ n)) ≫ (monoidalPowCat M m n).hom :=
    AlgebraicGeometry.Scheme.projBundle.MonoidalPowAux.map_tensorHom_δ_comp (pullback g) (symPowπ W m) (symPowπ W n)
      (symPowPullbackDesc g ψ m) (symPowPullbackDesc g ψ n) (monoidalPowCat M m n).hom
  have hL1 : (pullback g).map (symPowπ W m ⊗ₘ symPowπ W n) ≫ (pullback g).map (symPowMul W m n) ≫
        symPowPullbackDesc g ψ (m + n) =
      (pullback g).map (monoidalPowCat W m n).hom ≫ (pullback g).map (symPowπ W (m + n)) ≫
        symPowPullbackDesc g ψ (m + n) := by
    rw [← Functor.map_comp_assoc, tensorHom_symPowπ_symPowMul, Functor.map_comp_assoc]
  rw [hL1, pullback_map_symPowπ_comp_symPowPullbackDesc,
    AlgebraicGeometry.Scheme.projBundle.pullbackMonoidalPow_monoidalPowCat_assoc,
    ← AlgebraicGeometry.Scheme.projBundle.monoidalPowCat_monoidalPowMap, hR, pullback_map_symPowπ_comp_symPowPullbackDesc,
    pullback_map_symPowπ_comp_symPowPullbackDesc, tensorHom_comp_tensorHom_assoc]

private theorem symGradedAlgebra_eq_ofQC_mul (W : X.Modules)
    (hq : W.IsQuasicoherent) : symGradedAlgebra W = symGradedAlgebraOfQC W hq := by
  delta symGradedAlgebra
  exact dif_pos hq

private theorem pullback_map_mul_comp_symGradedPullbackDesc_aux (g : T ⟶ X) (W : X.Modules)
    (hq : W.IsQuasicoherent) {M : T.Modules} [M.IsLineBundle] (ψ : (pullback g).obj W ⟶ M)
    (S : X.GradedQCAlgebra) (hS : S = symGradedAlgebraOfQC W hq)
    (D : ∀ m : ℕ, (pullback g).obj (S.part m) ⟶ monoidalPow M m)
    (hD : ∀ m, HEq (D m) (symPowPullbackDesc g ψ m)) (m n : ℕ) :
    (pullback g).map (S.mul m n) ≫ D (m + n) =
      pullbackTensorObjHom g (S.part m) (S.part n) ≫ (D m ⊗ₘ D n) ≫ (monoidalPowCat M m n).hom := by
  subst hS
  have hD' : D = fun m => symPowPullbackDesc g ψ m := funext fun m => eq_of_heq (hD m)
  subst hD'
  exact pullback_map_symPowMul_comp_symPowPullbackDesc g W ψ m n

/-- **`LiftData.map_mul` form**: for `W` quasicoherent and `M` a line bundle,
`g^*(Sym(W).mul m n) ≫ Ψ_{m+n} = δ ≫ (Ψ_m ⊗ₘ Ψ_n) ≫ (monoidalPowCat M m n).hom`. -/
theorem pullback_map_mul_comp_symGradedPullbackDesc (g : T ⟶ X) (W : X.Modules)
    (hq : W.IsQuasicoherent) {M : T.Modules} [M.IsLineBundle] (ψ : (pullback g).obj W ⟶ M) (m n : ℕ) :
    (pullback g).map ((symGradedAlgebra W).mul m n) ≫ symGradedPullbackDesc g ψ (m + n) =
      pullbackTensorObjHom g ((symGradedAlgebra W).part m) ((symGradedAlgebra W).part n) ≫
        (symGradedPullbackDesc g ψ m ⊗ₘ symGradedPullbackDesc g ψ n) ≫ (monoidalPowCat M m n).hom :=
  pullback_map_mul_comp_symGradedPullbackDesc_aux g W hq ψ _ (symGradedAlgebra_eq_ofQC_mul W hq) _
    (fun m => symGradedPullbackDesc_heq_of_isQuasicoherent g hq ψ m) m n

end AlgebraicGeometry.Scheme.Modules

end SymPowDescMul

namespace AlgebraicGeometry.Scheme.projBundle.MulAux

open CategoryTheory.MonoidalCategory

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

theorem inv_comp_δ_aux {P Q R Si Sj Ti Tj : D} (h : P ⟶ Q) (h' : Q ⟶ P) (hh : h' ≫ h = 𝟙 Q)
    (hi : Si ⟶ Ti) (hi' : Ti ⟶ Si) (hhi : hi ≫ hi' = 𝟙 Si)
    (hj : Sj ⟶ Tj) (hj' : Tj ⟶ Sj) (hhj : hj ≫ hj' = 𝟙 Sj)
    (d₁ : P ⟶ R) (d₂ : R ⟶ Si ⊗ Sj) (dg : Q ⟶ Ti ⊗ Tj)
    (H : h ≫ dg = d₁ ≫ d₂ ≫ (hi ⊗ₘ hj)) :
    h' ≫ d₁ ≫ d₂ = dg ≫ (hi' ⊗ₘ hj') := by
  calc h' ≫ d₁ ≫ d₂ = h' ≫ d₁ ≫ d₂ ≫ ((hi ⊗ₘ hj) ≫ (hi' ⊗ₘ hj')) := by
        rw [tensorHom_comp_tensorHom, hhi, hhj, id_tensorHom_id, Category.comp_id]
    _ = h' ≫ (h ≫ dg) ≫ (hi' ⊗ₘ hj') := by rw [H]; simp only [Category.assoc]
    _ = dg ≫ (hi' ⊗ₘ hj') := by
        rw [← Category.assoc h', ← Category.assoc h' h, hh, Category.id_comp]

theorem chain_aux {A Aij Ai Aj B' B₂ Bi Bj Bij C₂ Ci Cj Cij Di Dj Dij Ei Ej Eij O : D}
    (m : A ⟶ Aij) (c : Aij ⟶ Bij) (c' : A ⟶ B') (ci : Ai ⟶ Bi) (cj : Aj ⟶ Bj) (m' : B' ⟶ Bij)
    (E1 : m ≫ c = c' ≫ m')
    (ψij : Bij ⟶ Cij) (d₁ : B' ⟶ B₂) (t : B₂ ⟶ C₂) (k : C₂ ⟶ Cij)
    (E2 : m' ≫ ψij = d₁ ≫ t ≫ k)
    (d₂ : B₂ ⟶ Bi ⊗ Bj) (ψi : Bi ⟶ Ci) (ψj : Bj ⟶ Cj) (d₃ : C₂ ⟶ Ci ⊗ Cj)
    (E3 : t ≫ d₃ = d₂ ≫ (ψi ⊗ₘ ψj))
    (P : Cij ⟶ Dij) (Pi : Ci ⟶ Di) (Pj : Cj ⟶ Dj) (cat' : Di ⊗ Dj ⟶ Dij)
    (E4 : k ≫ P = d₃ ≫ (Pi ⊗ₘ Pj) ≫ cat')
    (E : Dij ⟶ Eij) (Fi : Di ⟶ Ei) (Fj : Dj ⟶ Ej) (cat'' : Ei ⊗ Ej ⟶ Eij)
    (E5 : cat' ≫ E = (Fi ⊗ₘ Fj) ≫ cat'')
    (C : Eij ⟶ O) (Ci' : Ei ⟶ O) (Cj' : Ej ⟶ O) (lam : O ⊗ O ⟶ O)
    (E6 : cat'' ≫ C = (Ci' ⊗ₘ Cj') ≫ lam)
    (dg : A ⟶ Ai ⊗ Aj)
    (E7 : c' ≫ d₁ ≫ d₂ = dg ≫ (ci ⊗ₘ cj)) :
    m ≫ c ≫ ψij ≫ P ≫ E ≫ C =
      dg ≫ ((ci ≫ ψi ≫ Pi ≫ Fi ≫ Ci') ⊗ₘ (cj ≫ ψj ≫ Pj ≫ Fj ≫ Cj')) ≫ lam := by
  calc m ≫ c ≫ ψij ≫ P ≫ E ≫ C = (m ≫ c) ≫ ψij ≫ P ≫ E ≫ C := by simp only [Category.assoc]
    _ = c' ≫ (m' ≫ ψij) ≫ P ≫ E ≫ C := by rw [E1]; simp only [Category.assoc]
    _ = c' ≫ d₁ ≫ t ≫ (k ≫ P) ≫ E ≫ C := by rw [E2]; simp only [Category.assoc]
    _ = c' ≫ d₁ ≫ (t ≫ d₃) ≫ (Pi ⊗ₘ Pj) ≫ (cat' ≫ E) ≫ C := by rw [E4]; simp only [Category.assoc]
    _ = c' ≫ d₁ ≫ d₂ ≫ (ψi ⊗ₘ ψj) ≫ (Pi ⊗ₘ Pj) ≫ (Fi ⊗ₘ Fj) ≫ (cat'' ≫ C) := by
        rw [E3, E5]; simp only [Category.assoc]
    _ = (c' ≫ d₁ ≫ d₂) ≫ (ψi ⊗ₘ ψj) ≫ (Pi ⊗ₘ Pj) ≫ (Fi ⊗ₘ Fj) ≫ (Ci' ⊗ₘ Cj') ≫ lam := by
        rw [E6]; simp only [Category.assoc]
    _ = dg ≫ (ci ⊗ₘ cj) ≫ (ψi ⊗ₘ ψj) ≫ (Pi ⊗ₘ Pj) ≫ (Fi ⊗ₘ Fj) ≫ (Ci' ⊗ₘ Cj') ≫ lam := by
        rw [E7]; simp only [Category.assoc]
    _ = dg ≫ ((ci ≫ ψi ≫ Pi ≫ Fi ≫ Ci') ⊗ₘ (cj ≫ ψj ≫ Pj ≫ Fj ≫ Cj')) ≫ lam := by
        rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc]

end AlgebraicGeometry.Scheme.projBundle.MulAux

end
