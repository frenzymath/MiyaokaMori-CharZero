import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.Stacks00an

/-! # Constructive gluing of sheaves of modules

Two constructions, neither of which chooses a witness of an existence theorem:
1. gluing morphisms `f_i : M|_{U_i} ⟶ N|_{U_i}` along an open cover `{U_i}` (`glueHom`: take the
   section maps on the basis of opens contained in some `U_i` and extend from the dense
   subsite to a morphism `M ⟶ N`);
2. the sheaf of modules built from gluing data `(F_i, φ_ij)`
   (`GlueData.glued = ker(∏ ι_{i*}F_i ⇉ ∏ ι_{ij*}F_j|_{U_ij})`, the construction of Stacks 00AL).

References: Stacks 00AL, 00AN; Mathlib `TopCat.Sheaf.restrictHomEquivHom`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The section map `Γ(M, V) ⟶ Γ(N, V)` induced on `V ≤ W` by `φ : M|_W ⟶ N|_W`:
`Γ(M, V) → Γ(M, W.ι ''ᵁ W.ι ⁻¹ᵁ V) = Γ(M|_W, W.ι ⁻¹ᵁ V) →φ Γ(N|_W, W.ι ⁻¹ᵁ V) = Γ(N, W.ι ''ᵁ W.ι ⁻¹ᵁ V) → Γ(N, V)`
(the first and last steps are restriction maps; `W.ι ''ᵁ W.ι ⁻¹ᵁ V = W ⊓ V = V`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.restrictSectionMap {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} {W : X.Opens} (φ : M.restrict W.ι ⟶ N.restrict W.ι) (V : X.Opens) (hV : V ≤ W) :
    Γ(M, V) ⟶ Γ(N, V) :=
  M.presheaf.map (CategoryTheory.homOfLE (W.ι.image_preimage_le V)).op ≫
    φ.app (W.ι ⁻¹ᵁ V) ≫
    N.presheaf.map (CategoryTheory.homOfLE (by
      rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
        AlgebraicGeometry.Scheme.Opens.opensRange_ι]
      exact le_inf hV le_rfl : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V)).op

/-- The opens contained in some `U_i` (with the witness `i`) form a basis of `X` when `⨆ U_i = ⊤`. -/
theorem AlgebraicGeometry.Scheme.Modules.glueHom_isBasis {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun p : { p : ι × X.Opens // p.2 ≤ U p.1 } => p.1.2)) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro V x hx
  have hx' : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  exact ⟨V ⊓ U i, ⟨⟨(i, V ⊓ U i), inf_le_right⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩

/-- Gluing morphisms of sheaves of modules along an open cover (constructively): the
`f_i : M|_{U_i} ⟶ N|_{U_i}` give section maps on the basis `{V | ∃ i, V ≤ U_i}` (with witness
`i`); `TopCat.Sheaf.restrictHomEquivHom` (a morphism on a dense subsite extends uniquely to the
sheaves) extends them to a morphism `M ⟶ N` of sheaves of abelian groups, which is then shown to
be `O_X`-linear. The hypothesis `hf` (the section maps of `f_i`, `f_j` agree on all
`V ≤ U_i`, `V ≤ U_j`) is necessary: naturality on the basis and `O_X`-linearity are deduced from
it (as in `exists_hom_of_sectionMap_agree`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.glueHom {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M N : X.Modules)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap (f i) V hi
        = AlgebraicGeometry.Scheme.Modules.restrictSectionMap (f j) V hj) : M ⟶ N :=
  let B : { p : ι × X.Opens // p.2 ≤ U p.1 } → X.Opens := fun p => p.1.2
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) :=
    AlgebraicGeometry.Scheme.Modules.glueHom_isBasis U hU
  let α : (CategoryTheory.inducedFunctor B).op ⋙ M.presheaf ⟶
      (CategoryTheory.inducedFunctor B).op ⋙ N.presheaf :=
    { app := fun p => AlgebraicGeometry.Scheme.Modules.restrictSectionMap (f p.unop.1.1) p.unop.1.2 p.unop.2
      naturality := by
        intro p q h
        have hle : q.unop.1.2 ≤ p.unop.1.2 := leOfHom h.unop.hom
        have := AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_nat (f p.unop.1.1)
          p.unop.1.2 q.unop.1.2 p.unop.2 hle
        rw [show AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (f p.unop.1.1) q.unop.1.2
            (hle.trans p.unop.2) = AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom
              (f q.unop.1.1) q.unop.1.2 q.unop.2 from
          hf p.unop.1.1 q.unop.1.1 q.unop.1.2 (hle.trans p.unop.2) q.unop.2] at this
        exact this }
  let φ : M.presheaf ⟶ N.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB α
  have hφ : ∀ i (V : X.Opens) (hV : V ≤ U i), φ.app (op V) =
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (f i) V hV := fun i V hV =>
    TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB α ⟨(i, V), hV⟩
  have hlin : ∀ (V : X.Opens) (r : Γ(X, V)) (m : Γ(M, V)), φ.app (op V) (r • m) = r • φ.app (op V) m := by
    intro V r m
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun i => V ⊓ U i) V
      (fun i => homOfLE inf_le_left) ?_ _ _ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
    · intro i
      have nat := fun y => ConcreteCategory.congr_hom (φ.naturality (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) y
      simp only [ConcreteCategory.comp_apply] at nat
      change N.presheaf.map _ (φ.app (op V) (r • m)) = N.presheaf.map _ (r • φ.app (op V) m)
      rw [← nat, AlgebraicGeometry.Scheme.Modules.map_smul, AlgebraicGeometry.Scheme.Modules.map_smul,
        ← nat, hφ i (V ⊓ U i) inf_le_right,
        AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_smul]
  SheafOfModules.Hom.mk (PresheafOfModules.homMk φ (fun V r m => hlin V.unop r m))

/-- The section map of `glueHom` on `V ≤ U_i` is the section map of `f_i`. -/
theorem AlgebraicGeometry.Scheme.Modules.glueHom_app {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M N : X.Modules)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap (f i) V hi
        = AlgebraicGeometry.Scheme.Modules.restrictSectionMap (f j) V hj)
    (i : ι) (V : X.Opens) (hV : V ≤ U i) :
    (AlgebraicGeometry.Scheme.Modules.glueHom U hU M N f hf).app V =
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap (f i) V hV := by
  unfold AlgebraicGeometry.Scheme.Modules.glueHom
  exact TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩
    (AlgebraicGeometry.Scheme.Modules.glueHom_isBasis U hU) _ ⟨(i, V), hV⟩

/-- Restriction: for `F` on `W` and `V ≤ W`, the morphism `W.ι_* F ⟶ V.ι_*(F|_V)` (the unit of
`restrict ⊣ pushforward`, then `homOfLE ≫ W.ι = V.ι`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap {X : AlgebraicGeometry.Scheme.{u}}
    {V W : X.Opens} (h : V ≤ W) (F : W.toScheme.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pushforward W.ι).obj F ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward V.ι).obj (F.restrict (X.homOfLE h)) :=
  (AlgebraicGeometry.Scheme.Modules.pushforward W.ι).map
      ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction (X.homOfLE h)).unit.app F) ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp (X.homOfLE h) W.ι).inv.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (X.homOfLE_ι h)).hom.app _

/-- The sheaf of modules built from gluing data (the construction of Stacks 00AL):
`M := ker(∏_i ι_{i*}F_i ⇉ ∏_{(i,j)} ι_{ij*}(F_j|_{U_ij}))`, the two branches being "restrict the
`j`-th component to `U_ij`" and "restrict the `i`-th component to `U_ij`, then apply `φ_ij`". The
cocycle condition and `⨆ U_i = ⊤` are used only to prove `M|_{U_i} ≅ F_i`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.GlueData.glued {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} {U : ι → X.Opens} (D : AlgebraicGeometry.Scheme.Modules.GlueData U) : X.Modules :=
  let P : ι → X.Modules := fun i => (AlgebraicGeometry.Scheme.Modules.pushforward (U i).ι).obj (D.F i)
  let Q : ι × ι → X.Modules := fun p =>
    (AlgebraicGeometry.Scheme.Modules.pushforward (U p.1 ⊓ U p.2).ι).obj
      ((D.F p.2).restrict (X.homOfLE (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2)))
  let a : CategoryTheory.Limits.piObj P ⟶ CategoryTheory.Limits.piObj Q :=
    CategoryTheory.Limits.Pi.lift fun p =>
      CategoryTheory.Limits.Pi.π P p.2 ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2) (D.F p.2)
  let b : CategoryTheory.Limits.piObj P ⟶ CategoryTheory.Limits.piObj Q :=
    CategoryTheory.Limits.Pi.lift fun p =>
      CategoryTheory.Limits.Pi.π P p.1 ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1) (D.F p.1) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (U p.1 ⊓ U p.2).ι).map (D.φ p.1 p.2).hom
  CategoryTheory.Limits.kernel (a - b)

end
