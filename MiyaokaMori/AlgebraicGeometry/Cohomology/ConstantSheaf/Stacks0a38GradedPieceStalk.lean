import MiyaokaMori.Prelude
import Mathlib.Topology.Sheaves.Abelian
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.ExtendByZeroStalk
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02utStalkAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.Stacks0a38ConstantInclusion
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.Stacks0a38GenSub

/-! # Stalk toolkit for the graded pieces of Stacks 0A38

Stalkwise facts about abelian sheaves on a topological space `X`, the constant sheaf `ℤ_X`, the extensions
by zero `j_!ℤ_U` (`extendByZeroConstant U`), the canonical inclusions `c_U : j_!ℤ_U ⟶ ℤ_X`
(`constantInclusion U`) and the subsheaves `K_k = genSub ψ n k` of Stacks 0A38. The stalk functor
`Sheaf.forget ⋙ stalkFunctor x` on abelian sheaves is exact (Mathlib `Mathlib.Topology.Sheaves.Abelian`:
`PreservesFiniteLimits`, `PreservesFiniteColimits`, `exact_iff_stalkFunctor_map_exact`,
`isZero_iff_stalkFunctor_obj_isZero`, `mono_iff_stalk_mono`, `isIso_iff_stalkFunctor_map_iso`).

* `hom_ext_of_stalkFunctor_map` — two morphisms of sheaves agreeing on all stalks are equal;
* `isIso_stalkFunctor_map_restrictUnit_hom_of_mem` — the restriction map `F ⟶ j_*(F|_U)` is an isomorphism
  on stalks at points of `U`;
* `isIso_stalkFunctor_map_constantInclusion_hom_of_mem` — `c_U` is an isomorphism on stalks at points of `U`;
* `mono_zsmul_id_constantSheaf` — `ℤ_X` has no torsion: `n • 𝟙 : ℤ_X ⟶ ℤ_X` is a monomorphism for `n ≠ 0`;
* `isZero_stalk_genSub_of_forall_notMem` — the stalk of `K_k` vanishes outside `⋃_{n_i ≤ k} V_i`.

Source: Stacks 0A38 (cohomology-lemma-subsheaf-of-constant-sheaf), proof, paragraph 3; Stacks 00A5 (3). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- Two morphisms of abelian sheaves on `X` that agree on every stalk are equal
(`TopCat.Presheaf.section_ext`: a section is determined by its germs). -/
theorem hom_ext_of_stalkFunctor_map {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f g : F ⟶ G)
    (h : ∀ x : X, (stalkFunctor AddCommGrpCat.{u} x).map f.hom = (stalkFunctor AddCommGrpCat.{u} x).map g.hom) :
    f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  induction U with | op U => ?_
  ext s
  apply TopCat.Presheaf.section_ext G U
  intro x hx
  rw [← stalkFunctor_map_germ_apply U x hx f.hom s, ← stalkFunctor_map_germ_apply U x hx g.hom s, h x]

/-- A morphism of abelian sheaves that vanishes on every stalk is zero. -/
theorem eq_zero_of_stalkFunctor_map {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (h : ∀ x : X, (stalkFunctor AddCommGrpCat.{u} x).map f.hom = 0) : f = 0 :=
  hom_ext_of_stalkFunctor_map f 0 fun x => by
    rw [h x]
    exact (Functor.map_zero (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalkFunctor AddCommGrpCat.{u} x) F G).symm

/-- On an open `V ≤ U` the component of the restriction map `η_U : F ⟶ j_*(F|_U)` is `F(V) ⟶ F(V ⊓ U) = F(V)`,
a bijection. -/
theorem bijective_restrictUnit_hom_app_of_le (U : Opens X)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens X) (hV : V ≤ U) :
    Function.Bijective ((restrictUnit U F).hom.app (op V)) := by
  change Function.Bijective (F.obj.map (homOfLE (functor_map_le U V)).op)
  have hVeq : (Opens.isOpenEmbedding U).functor.obj ((Opens.map (Opens.inclusion' U)).obj V) = V :=
    le_antisymm (functor_map_le U V) (le_functor_map_of_le U V hV)
  have heq : (homOfLE (functor_map_le U V)).op = eqToHom (congrArg op hVeq.symm) :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [heq]
  exact ConcreteCategory.bijective_of_isIso (F.obj.map (eqToHom (congrArg op hVeq.symm)))

/-- The restriction map `η_U : F ⟶ j_*(F|_U)` is an isomorphism on stalks at every point of `U`. -/
theorem isIso_stalkFunctor_map_restrictUnit_hom_of_mem (U : Opens X)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (x : X) (hx : x ∈ U) :
    IsIso ((stalkFunctor AddCommGrpCat.{u} x).map (restrictUnit U F).hom) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (stalkFunctor_map_bijective_of_app_bijective_of_le _ U x hx
      (fun V hV => bijective_restrictUnit_hom_app_of_le U F V hV))

/-- The canonical inclusion `c_U : j_!ℤ_U ⟶ ℤ_X` is an isomorphism on stalks at every point of `U`:
`c_U ≫ η_U = ε_U ≫ j_*(ℤ_U ≅ ℤ_X|_U)` (`constantInclusion_comp_restrictUnit`), and the stalk maps of `η_U`
(`isIso_stalkFunctor_map_restrictUnit_hom_of_mem`) and of `ε_U : j_!ℤ_U ⟶ j_*ℤ_U`
(`isIso_stalkFunctor_map_extendByZeroToPushforward`) are isomorphisms at `x ∈ U`. -/
theorem isIso_stalkFunctor_map_constantInclusion_hom_of_mem (U : Opens X) (x : X) (hx : x ∈ U) :
    IsIso ((stalkFunctor AddCommGrpCat.{u} x).map (constantInclusion U).hom) := by
  have h : (stalkFunctor AddCommGrpCat.{u} x).map (constantInclusion U).hom ≫
      (stalkFunctor AddCommGrpCat.{u} x).map (restrictUnit U _).hom =
      (stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroToPushforward U _).hom ≫
        (stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map
            (restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).inv).hom := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun f => (stalkFunctor AddCommGrpCat.{u} x).map f.hom) (constantInclusion_comp_restrictUnit U)
  have h1 := isIso_stalkFunctor_map_restrictUnit_hom_of_mem U
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) x hx
  have h2 := isIso_stalkFunctor_map_extendByZeroToPushforward U
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) x hx
  have h3 : IsIso ((stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map
        (restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).inv).hom) := by
    have hi : IsIso ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map
        (restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).inv) :=
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).mapIso
        (restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).symm).isIso_hom
    have hi' := @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      _ hi
    exact @Functor.map_isIso _ _ _ _ _ _ (stalkFunctor AddCommGrpCat.{u} x) _ hi'
  have h4 : IsIso ((stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroToPushforward U _).hom ≫
      (stalkFunctor AddCommGrpCat.{u} x).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map
          (restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).inv).hom) := inferInstance
  exact IsIso.of_isIso_fac_right h

/-- `ℤ_X` has no torsion: for `n ≠ 0`, `n • 𝟙 : ℤ_X ⟶ ℤ_X` is a monomorphism. Indeed `ℤ_X` is the
sheafification of the constant presheaf `P` with value `ℤ`, `n • 𝟙_P` is objectwise injective, hence a
monomorphism of presheaves, and sheafification preserves finite limits, hence monomorphisms. -/
theorem mono_zsmul_id_constantSheaf (n : ℤ) (hn : n ≠ 0) :
    Mono (n • 𝟙 ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ)))) := by
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))
  have hP : Mono (n • 𝟙 P) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    rw [NatTrans.app_zsmul, NatTrans.id_app, AddCommGrpCat.mono_iff_injective]
    intro a b hab
    have hab' : n • a = n • b := by simpa using hab
    exact smul_right_injective (ULift ℤ) hn hab'
  change Mono (n • 𝟙 ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P))
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_zsmul]
  exact CategoryTheory.Functor.map_mono _ _

section Biproduct

-- Mathlib states `Abelian.hasFiniteBiproducts` as a theorem, not an instance; we use it section-locally
-- (no global instance is registered).
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- The stalk at `x` of a finite biproduct of sheaves all of whose stalks at `x` vanish is zero
(`𝟙 = ∑ π_i ≫ ι_i` and every `π_i` has zero target on stalks). -/
theorem isZero_stalk_biproduct_of_forall_isZero {ι : Type} [Fintype ι]
    (F : ι → CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (x : X)
    (h : ∀ i, IsZero ((stalkFunctor AddCommGrpCat.{u} x).obj (F i).obj)) :
    IsZero ((stalkFunctor AddCommGrpCat.{u} x).obj (⨁ F).obj) := by
  rw [IsZero.iff_id_eq_zero]
  have htot := biproduct.total (f := F)
  have h1 : (stalkFunctor AddCommGrpCat.{u} x).map
        ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (𝟙 (⨁ F))) =
      (stalkFunctor AddCommGrpCat.{u} x).map
        ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          (∑ i, biproduct.π F i ≫ biproduct.ι F i)) := by
    rw [htot]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_sum,
    CategoryTheory.Functor.map_sum] at h1
  refine h1.trans ?_
  apply Finset.sum_eq_zero
  intro i _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    (h i).eq_zero_of_tgt ((stalkFunctor AddCommGrpCat.{u} x).map
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (biproduct.π F i))), zero_comp]

/-- The stalk of `K_k = genSub ψ n k` at a point `x` lying in no `V_i` with `n_i ≤ k` is zero: `K_k` is the
image of `⨁_{n_i ≤ k} j_!ℤ_{V_i} ⟶ K`, the stalk functor is exact (so the stalk of `K_k` is a quotient of
the stalk of the biproduct), and the stalks of the `j_!ℤ_{V_i}` vanish at `x` (`isZero_extendByZero_stalk_of_notMem`). -/
theorem isZero_stalk_genSub_of_forall_notMem
    {K : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {t : ℕ} {V : Fin t → Opens X} (ψ : ∀ i, extendByZeroConstant (V i) ⟶ K) (n : Fin t → ℕ) (k : ℕ)
    (x : X) (hx : ∀ i, n i ≤ k → x ∉ V i) :
    IsZero ((stalkFunctor AddCommGrpCat.{u} x).obj (genSub ψ n k).obj) := by
  have hsrc : IsZero ((stalkFunctor AddCommGrpCat.{u} x).obj
      (⨁ fun i : {i : Fin t // n i ≤ k} => extendByZeroConstant (V i.1)).obj) :=
    isZero_stalk_biproduct_of_forall_isZero _ x fun i =>
      isZero_extendByZero_stalk_of_notMem (V i.1) _ x (hx i.1 i.2)
  have he : Epi (factorThruImage (genSubDesc ψ n k)) := inferInstance
  have hepi : Epi ((stalkFunctor AddCommGrpCat.{u} x).map (factorThruImage (genSubDesc ψ n k)).hom) :=
    @CategoryTheory.Functor.map_epi _ _ _ _
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalkFunctor AddCommGrpCat.{u} x) inferInstance _ _
      (factorThruImage (genSubDesc ψ n k)) he
  exact IsZero.of_epi ((stalkFunctor AddCommGrpCat.{u} x).map (factorThruImage (genSubDesc ψ n k)).hom) hsrc

end Biproduct

end TopCat.Sheaf

end
