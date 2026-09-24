import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC

/-! # The four standard functors on abelian sheaves over a topological space

The four standard functors on abelian sheaves over a topological space `X` (`j : U ↪ X` an open
embedding, `i : Z ↪ X` a subspace embedding): `restrict F U = j^{-1}F = F|_U` (Mathlib
`TopCat.Sheaf.pullback` along the inclusion, equivalent to `IsOpenEmbedding.sheafPullback`);
`extendByZero U G = j_!G` (extension by zero: the presheaf `V ↦ G(V)` if `V ⊆ U`, else `0`, then
sheafified; its stalks are `G_x` inside `U` and `0` outside); `restrictClosed F Z = i^{-1}F`
(`TopCat.Sheaf.pullback` along the inclusion `Z ↪ X`); `pushforwardClosed Z G = i_*G`
(`TopCat.Sheaf.pushforward` along the inclusion). Mathlib has the general pullback/pushforward but not
the extension by zero.

Source: the constructions preceding Stacks 02UT (Cohomology, extension by zero); Stacks 00A4, 008M.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `j^{-1}F = F|_U`: the naive pullback along the open embedding `U ↪ X` (Mathlib
`IsOpenEmbedding.sheafPullback`, canonically isomorphic to `TopCat.Sheaf.pullback`). -/

noncomputable def TopCat.Sheaf.restrict {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (U : TopologicalSpace.Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} :=
  ((TopologicalSpace.Opens.isOpenEmbedding U).sheafPullback AddCommGrpCat.{u}).obj F

/-- Extension by zero `j_!`: the subpresheaf `V ↦ G(V)` if `V ⊆ U`, else `0`, of `j_*G`, then sheafified. -/

noncomputable def TopCat.Sheaf.extendByZero {X : TopCat.{u}} (U : TopologicalSpace.Opens X)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  open Classical in
  let J := ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (TopologicalSpace.Opens.inclusion' U)).obj G).val
  let S : ∀ V : (TopologicalSpace.Opens X)ᵒᵖ, AddSubgroup (J.obj V) := fun V =>
    if V.unop ≤ U then ⊤ else ⊥
  have hmem : ∀ {V W : (TopologicalSpace.Opens X)ᵒᵖ} (f : V ⟶ W) (x : S V),
      (J.map f).hom ((S V).subtype x) ∈ S W := by
    intro V W f x
    by_cases hW : W.unop ≤ U
    · simp only [S, if_pos hW, AddSubgroup.mem_top]
    · have hV : ¬ V.unop ≤ U := fun h => hW (le_trans (leOfHom f.unop) h)
      have hx : ((S V).subtype x : J.obj V) = 0 := by
        have hx' := x.2
        simp only [S, if_neg hV, AddSubgroup.mem_bot] at hx'
        simpa using hx'
      simp only [hx, map_zero]
      exact zero_mem _
  let P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    { obj := fun V => AddCommGrpCat.of (S V)
      map := fun {V W} f => AddCommGrpCat.ofHom
        (((J.map f).hom.comp (S V).subtype).codRestrict (S W) (hmem f))
      map_id := by
        intro V
        ext x
        show (J.map (𝟙 V)).hom (x : J.obj V) = (x : J.obj V)
        rw [J.map_id]
        rfl
      map_comp := by
        intro V W Z f g
        ext x
        show (J.map (f ≫ g)).hom (x : J.obj V) = (J.map g).hom ((J.map f).hom (x : J.obj V))
        rw [J.map_comp]
        rfl }
  (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P

/-- Restriction to a subspace `i^{-1}`: sheaf pullback along the inclusion `Z ↪ X` (Mathlib
`TopCat.Sheaf.pullback`). -/

noncomputable def TopCat.Sheaf.restrictClosed {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (Z : Set X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u}
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X)).obj F

/-- Pushforward `i_*` along the inclusion of a subspace (Mathlib `TopCat.Sheaf.pushforward`). -/

noncomputable def TopCat.Sheaf.pushforwardClosed {X : TopCat.{u}} (Z : Set X)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X)).obj G

end
