import MiyaokaMori.Prelude
import Mathlib.Topology.Sheaves.Skyscraper

/-! # Sections of a filtered colimit over a quasi-compact open

Sections of a filtered colimit of abelian sheaves over a quasi-compact open: on a quasi-separated space with a
basis of quasi-compact opens, `colim_j F_j(U) → (colim_j F_j)(U)` is bijective for every quasi-compact open `U`
(stated elementwise: surjective, and every element of the kernel dies at a later stage).

This is Stacks 009F (sheaves-lemma-directed-colimits-sections) (4) combined with Stacks 0069
(topology-lemma-topology-quasi-separated-scheme) (3); it is the `q = 0` case of Stacks 01FF
(cohomology-lemma-quasi-separated-cohomology-colimit) and the input to the acyclicity of filtered colimits
of injectives. Used for Stacks 01FF with `U = X`.

Route: `TopCat.Sheaf.SectionsColimit.exists_germ_eq` /
`stalk_map_ι_eq_iff` (stalks commute with the colimit, elementwise), `exists_map_eq_zero_of_ι_eq_zero` (kernel dies;
needs only the basis of quasi-compact opens) and `exists_ι_eq` (surjectivity; needs `QuasiSeparatedSpace`).
The finite "common stage" bookkeeping is `CategoryTheory.IsFiltered.exists_hom_forall_mem_finset`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

/-- Common stage for finitely many "eventually true" predicates on morphisms out of `j` in a
filtered category. -/
theorem CategoryTheory.IsFiltered.exists_hom_forall_mem_finset {J : Type u} [Category.{v} J]
    [IsFiltered J] {ι : Type*} (T : Finset ι) (j : J) (P : ι → ∀ k : J, (j ⟶ k) → Prop)
    (hP : ∀ i k k' (b : j ⟶ k) (c : k ⟶ k'), P i k b → P i k' (b ≫ c))
    (h : ∀ i ∈ T, ∃ (k : J) (a : j ⟶ k), P i k a) :
    ∃ (k : J) (b : j ⟶ k), ∀ i ∈ T, P i k b := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert i T hi ih =>
    obtain ⟨k, b, hb⟩ := ih (fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
    obtain ⟨k', a, ha⟩ := h i (Finset.mem_insert_self i T)
    refine ⟨IsFiltered.coeq (b ≫ IsFiltered.leftToMax k k') (a ≫ IsFiltered.rightToMax k k'),
      (b ≫ IsFiltered.leftToMax k k') ≫ IsFiltered.coeqHom _ _, ?_⟩
    intro i' hi'
    rcases Finset.mem_insert.1 hi' with rfl | hi'
    · rw [IsFiltered.coeq_condition, Category.assoc]
      exact hP _ _ _ _ _ ha
    · rw [Category.assoc]
      exact hP _ _ _ _ _ (hb i' hi')

namespace TopCat.Sheaf.SectionsColimit

variable {X : TopCat.{u}} {J : Type u} [SmallCategory J]
  (F : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Restriction commutes with the transition maps `F.map a` (naturality, elementwise). -/
theorem map_res {j k : J} (a : j ⟶ k) {U V : Opens X} (i : V ⟶ U) (s : (F.obj j).obj.obj (op U)) :
    (F.map a).hom.app (op V) ((F.obj j).obj.map i.op s) =
      (F.obj k).obj.map i.op ((F.map a).hom.app (op U) s) := by
  have := ConcreteCategory.congr_hom ((F.map a).hom.naturality i.op) s
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this

/-- Restriction commutes with the colimit injections (naturality, elementwise). -/
theorem ι_res (j : J) {U V : Opens X} (i : V ⟶ U) (s : (F.obj j).obj.obj (op U)) :
    (colimit.ι F j).hom.app (op V) ((F.obj j).obj.map i.op s) =
      (colimit F).obj.map i.op ((colimit.ι F j).hom.app (op U) s) := by
  have := ConcreteCategory.congr_hom ((colimit.ι F j).hom.naturality i.op) s
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this

/-- `F.map (b ≫ c)` on sections is the composite. -/
theorem map_comp_app {j k l : J} (b : j ⟶ k) (c : k ⟶ l) (U : Opens X) (s : (F.obj j).obj.obj (op U)) :
    (F.map (b ≫ c)).hom.app (op U) s = (F.map c).hom.app (op U) ((F.map b).hom.app (op U) s) := by
  rw [Functor.map_comp]
  rfl

/-- `colimit.ι F k ∘ F.map a = colimit.ι F j` on sections. -/
theorem ι_map {j k : J} (a : j ⟶ k) (U : Opens X) (s : (F.obj j).obj.obj (op U)) :
    (colimit.ι F k).hom.app (op U) ((F.map a).hom.app (op U) s) = (colimit.ι F j).hom.app (op U) s := by
  have := ConcreteCategory.congr_hom (congrArg (fun f => f.hom.app (op U)) (colimit.w F a)) s
  exact this

variable [IsFiltered J] (x : X)

/-- The Types-level cocone on the stalks at `x` of the `F.obj j`, with point the stalk of `colimit F`. -/
abbrev stalkTypesCocone :
    Cocone (F ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) ⋙
      CategoryTheory.forget AddCommGrpCat.{u}) :=
  (CategoryTheory.forget AddCommGrpCat.{u}).mapCocone
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapCocone
      (colimit.cocone F))

/-- Stalks commute with colimits of sheaves (the stalk functor is a left adjoint, Mathlib
`stalkSkyscraperSheafAdjunction`), and `forget AddCommGrpCat` preserves filtered colimits. -/
def isColimit_stalkTypesCocone : IsColimit (stalkTypesCocone F x) :=
  have hG : PreservesColimitsOfShape J
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    inferInstance
  have h1 : PreservesColimit (C := TopCat.Sheaf AddCommGrpCat.{u} X) F
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    hG.preservesColimit
  isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u}) (h1.preserves (colimit.isColimit F)).some

/-- Every germ of `colimit F` at `x` is the germ of `(colimit.ι F j) s` for some local section `s` of
some `F.obj j`. -/
theorem exists_germ_eq (g : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (colimit F).obj x) :
    ∃ (j : J) (U : Opens X) (hx : x ∈ U) (s : (F.obj j).obj.obj (op U)),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (colimit F).obj U x hx
        ((colimit.ι F j).hom.app (op U) s) = g := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (isColimit_stalkTypesCocone F x) g
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X) (F.obj j).obj y
  refine ⟨j, U, hx, s, ?_⟩
  rw [← hy]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (colimit.ι F j).hom s).symm

/-- Two germs of `F.obj j` at `x` that become equal in `colimit F` become equal at some later stage. -/
theorem stalk_map_ι_eq_iff {j : J} (y y' : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (F.obj j).obj x) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (colimit.ι F j).hom y =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (colimit.ι F j).hom y' ↔
    ∃ (k : J) (a : j ⟶ k),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (F.map a).hom y =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (F.map a).hom y' :=
  Types.FilteredColimit.isColimit_eq_iff' (isColimit_stalkTypesCocone F x) y y'

variable {x}

/-- **Kernel dies** (Stacks 009F (2)): a section of `F.obj j` over a quasi-compact open `U` that
dies in `colimit F` dies at some later stage. Only needs a basis of quasi-compact opens. -/
theorem exists_map_eq_zero_of_ι_eq_zero
    (hB : Opens.IsBasis {U : Opens X | IsCompact (U : Set X)})
    (U : Opens X) (hU : IsCompact (U : Set X)) (j : J) (s : (F.obj j).obj.obj (op U))
    (hs : (colimit.ι F j).hom.app (op U) s = 0) :
    ∃ (k : J) (a : j ⟶ k), (F.map a).hom.app (op U) s = 0 := by
  -- for each `x ∈ U`: a stage and a basic quasi-compact open neighbourhood on which `s` dies
  have key : ∀ x : U, ∃ (V : Opens X) (hxV : (x : X) ∈ V) (hVU : V ≤ U) (_ : IsCompact (V : Set X))
      (k : J) (a : j ⟶ k), (F.obj k).obj.map (homOfLE hVU).op ((F.map a).hom.app (op U) s) = 0 := by
    rintro ⟨x, hx⟩
    have h1 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (colimit.ι F j).hom
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (F.obj j).obj U x hx s) =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (colimit.ι F j).hom 0 := by
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hs, map_zero, map_zero]
      rfl
    obtain ⟨k, a, ha⟩ := (stalk_map_ι_eq_iff F x _ _).1 h1
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, map_zero] at ha
    have ha' : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (F.obj k).obj U x hx
          ((F.map a).hom.app (op U) s) =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (F.obj k).obj U x hx 0 := by
      rw [ha, map_zero]
      rfl
    obtain ⟨W, hxW, iU, _, hW⟩ := TopCat.Presheaf.germ_eq (F.obj k).obj x hx hx _ _ ha'
    rw [map_zero] at hW
    obtain ⟨V, hVc, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.1 hB hxW
    refine ⟨V, hxV, hVW.trans iU.le, hVc, k, a, ?_⟩
    rw [show (homOfLE (hVW.trans iU.le) : V ⟶ U) = homOfLE hVW ≫ iU from rfl, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, hW, map_zero]
  choose V hxV hVU hVc k a hV using key
  -- finite subcover of `U` by the `V x`
  obtain ⟨T, hT⟩ := hU.elim_finite_subcover (fun x : U => (V x : Set X)) (fun x => (V x).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  -- common stage
  obtain ⟨k', b, hb⟩ := IsFiltered.exists_hom_forall_mem_finset T j
    (fun x k' (b : j ⟶ k') => (F.obj k').obj.map (homOfLE (hVU x)).op ((F.map b).hom.app (op U) s) = 0)
    (fun x k₁ k₂ b c hb => by
      dsimp only at hb ⊢
      rw [map_comp_app, ← map_res, hb, map_zero])
    (fun x _ => ⟨k x, a x, hV x⟩)
  refine ⟨k', b, ?_⟩
  -- locality
  have hcover : U ≤ iSup (fun x : T => V x) := by
    intro y hy
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.1 (hT hy)
    exact Opens.mem_iSup.2 ⟨⟨x, hxT⟩, hyx⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (F.obj k') (fun x : T => V x) U (fun x => homOfLE (hVU x)) hcover _ _
    (fun x => ?_)
  rw [hb x x.2, map_zero]

/-- **Surjectivity** (Stacks 009F (4)): on a quasi-separated space with a basis of quasi-compact
opens, every section of `colimit F` over a quasi-compact open comes from some `F.obj j`. -/
theorem exists_ι_eq [QuasiSeparatedSpace X]
    (hB : Opens.IsBasis {U : Opens X | IsCompact (U : Set X)})
    (U : Opens X) (hU : IsCompact (U : Set X)) (t : (colimit F).obj.obj (op U)) :
    ∃ (j : J) (s : (F.obj j).obj.obj (op U)), (colimit.ι F j).hom.app (op U) s = t := by
  classical
  -- locally, `t` comes from some `F.obj j`
  have key : ∀ x : U, ∃ (V : Opens X) (hxV : (x : X) ∈ V) (hVU : V ≤ U) (_ : IsCompact (V : Set X))
      (j : J) (s : (F.obj j).obj.obj (op V)),
      (colimit.ι F j).hom.app (op V) s = (colimit F).obj.map (homOfLE hVU).op t := by
    rintro ⟨x, hx⟩
    obtain ⟨j, W, hxW, s, hs⟩ := exists_germ_eq F x
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (colimit F).obj U x hx t)
    obtain ⟨W', hxW', iW, iU, hW'⟩ := TopCat.Presheaf.germ_eq (colimit F).obj x hxW hx _ _ hs
    obtain ⟨V, hVc, hxV, hVW'⟩ := Opens.isBasis_iff_nbhd.1 hB hxW'
    refine ⟨V, hxV, hVW'.trans iU.le, hVc, j, (F.obj j).obj.map (homOfLE hVW' ≫ iW).op s, ?_⟩
    rw [ι_res, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hW', ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp]
    rfl
  choose V hxV hVU hVc j s hs using key
  -- finite subcover
  obtain ⟨T, hT⟩ := hU.elim_finite_subcover (fun x : U => (V x : Set X)) (fun x => (V x).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  have hcover : U ≤ iSup (fun x : T => V x) := by
    intro y hy
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.1 (hT hy)
    exact Opens.mem_iSup.2 ⟨⟨x, hxT⟩, hyx⟩
  -- push all local sections to a common stage `k`
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (T.image j)
  have hk' : ∀ x : T, Nonempty (j x ⟶ k) := fun x => hk (Finset.mem_image_of_mem j x.2)
  let s' : ∀ x : T, (F.obj k).obj.obj (op (V x)) := fun x => (F.map (hk' x).some).hom.app (op (V x)) (s x)
  have hs' : ∀ x : T, (colimit.ι F k).hom.app (op (V x)) (s' x) = (colimit F).obj.map (homOfLE (hVU x)).op t :=
    fun x => by rw [← hs x]; exact ι_map F _ _ _
  -- the differences on overlaps die in `colimit F`, hence at a further stage (kernel statement)
  let d : ∀ p : T × T, (F.obj k).obj.obj (op (V p.1 ⊓ V p.2)) := fun p =>
    (F.obj k).obj.map (Opens.infLELeft (V p.1) (V p.2)).op (s' p.1) -
      (F.obj k).obj.map (Opens.infLERight (V p.1) (V p.2)).op (s' p.2)
  have hd : ∀ p : T × T, ∃ (k' : J) (b : k ⟶ k'), (F.map b).hom.app (op (V p.1 ⊓ V p.2)) (d p) = 0 := by
    intro p
    refine exists_map_eq_zero_of_ι_eq_zero F hB _ ?_ k (d p) ?_
    · rw [Opens.coe_inf]
      exact (hVc p.1).inter_of_isOpen (hVc p.2) (V p.1).isOpen (V p.2).isOpen
    · simp only [d]
      rw [map_sub, ι_res, ι_res, hs', hs', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
      rw [show (Opens.infLELeft (V p.1) (V p.2) ≫ homOfLE (hVU p.1) : V p.1 ⊓ V p.2 ⟶ U) =
        Opens.infLERight (V p.1) (V p.2) ≫ homOfLE (hVU p.2) from rfl]
      exact sub_self _
  obtain ⟨k', b, hb⟩ := IsFiltered.exists_hom_forall_mem_finset (Finset.univ : Finset (T × T)) k
    (fun p k' (b : k ⟶ k') => (F.map b).hom.app (op (V p.1 ⊓ V p.2)) (d p) = 0)
    (fun p k₁ k₂ b c hb => by
      dsimp only at hb ⊢
      rw [map_comp_app, hb, map_zero])
    (fun p _ => hd p)
  -- glue at stage `k'`
  let u : ∀ x : T, (F.obj k').obj.obj (op (V x)) := fun x => (F.map b).hom.app (op (V x)) (s' x)
  have hu : TopCat.Presheaf.IsCompatible (F.obj k').obj (fun x : T => V x) u := by
    intro p q
    have := hb (p, q) (Finset.mem_univ _)
    simp only [d, map_sub, map_res] at this
    exact sub_eq_zero.1 this
  obtain ⟨sg, hsg, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F.obj k') (fun x : T => V x) U
    (fun x => homOfLE (hVU x)) hcover u hu
  refine ⟨k', sg, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    (colimit F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (fun x : T => V x) U (fun x => homOfLE (hVU x)) hcover _ _
    (fun x => ?_)
  rw [← ι_res, hsg x]
  simp only [u]
  rw [ι_map, hs']

end TopCat.Sheaf.SectionsColimit

/-- (Stacks 009F (4) + 0069 (3); `q = 0` case of Stacks 01FF.) Let `X` be a quasi-separated space
(the intersection of two quasi-compact opens is quasi-compact) with a basis `hB` of quasi-compact opens, `J` a
small filtered category, `F : J ⥤ Sh(X, Ab)`, and `U` a quasi-compact open. Then every section of `colim F`
over `U` comes from some `F.obj j`, and a section of `F.obj j` over `U` that dies in `colim F` dies in some
`F.obj k`, `a : j ⟶ k`.

**Natural-language proof (self-contained; Stacks 009F, proof of (4), written via stalks).**
Write `G := colim F` (colimit in the category of sheaves) and `ι_j : F_j ⟶ G`.
Library facts used: (i) *stalks commute with colimits of sheaves*: `Sheaf.forget ⋙ Presheaf.stalkFunctor _ x`
is a left adjoint (`TopCat.stalkSkyscraperSheafAdjunction`), hence preserves colimits, so
`G_x ≅ colim_j (F_j)_x` compatibly with the `ι_j`; (ii) *elementwise description of filtered colimits in
`AddCommGrpCat`* (the forgetful functor preserves filtered colimits: every element of `colim_j A_j` is the image
of an element of some `A_j`, and an element of `A_j` mapping to `0` in the colimit maps to `0` in some `A_k`,
`a : j ⟶ k`; `Types.FilteredColimit.isColimit_eq_iff`, `Types.jointly_surjective`); (iii) *sheaf axioms
elementwise*: a section that restricts to `0` on each member of an open cover is `0`
(`TopCat.Sheaf.eq_of_locally_eq`), and compatible sections on a cover glue (`TopCat.Sheaf.existsUnique_gluing`);
(iv) *germs*: two sections with the same germ at `x` agree on a neighbourhood of `x` (`TopCat.Presheaf.germ_eq`),
and a section of a sheaf all of whose germs vanish is `0` (`TopCat.Presheaf.section_ext`); (v) *topology*: a
quasi-compact open covered by basic opens is covered by finitely many of them
(`IsCompact.elim_finite_subcover`), and `V ∩ V'` is quasi-compact for quasi-compact opens `V, V'`
(`QuasiSeparatedSpace`). Finitely many objects/morphisms of the filtered `J` have a common upper bound
(`IsFiltered.sup_exists`).

*Kernel dies (second conjunct).* Let `s ∈ F_j(U)` with `ι_j(s) = 0` in `G(U)`. For `x ∈ U`, the germ
`(ι_j s)_x = 0` in `G_x = colim_i (F_i)_x` is the image of `s_x`, so by (ii) there is `a_x : j ⟶ i_x` with
`(F(a_x) s)_x = 0`; by (iv) `F(a_x) s` vanishes on a neighbourhood of `x`, which we shrink to a basic
quasi-compact open `V_x ⊆ U` containing `x` (`hB`). By (v) finitely many `V_{x_1}, …, V_{x_n}` cover `U`;
choose `k` with morphisms `i_{x_r} ⟶ k` compatible with `j ⟶ i_{x_r}` (filteredness). Then `t := F(j ⟶ k) s`
restricts to `0` on each `V_{x_r}`, hence `t = 0` by (iii).

*Surjectivity (first conjunct).* Let `t ∈ G(U)`. For `x ∈ U`, by (i), (ii) and the description of germs
(`TopCat.Presheaf.germ_exist`) there are `i_x`, an open `W_x ∋ x` and `s_x ∈ F_{i_x}(W_x)` with
`(ι_{i_x} s_x)_x = t_x`; by (iv) `ι_{i_x} s_x` and `t` agree on a neighbourhood of `x`, which we shrink to a basic
quasi-compact open `V_x ⊆ W_x ∩ U` containing `x`. By (v) finitely many `V_1, …, V_n` cover `U`; push all
`s_r` to a common stage `k`. For each pair `(r, r')` the section `s_r|_{V_r ∩ V_{r'}} - s_{r'}|_{V_r ∩ V_{r'}}`
maps to `t - t = 0` in `G(V_r ∩ V_{r'})`; `V_r ∩ V_{r'}` is quasi-compact by (v), so by the kernel statement
(already proved, applied to `V_r ∩ V_{r'}`) it dies at some stage `k_{r r'} ≥ k`; take a common stage
`k' ≥ k_{r r'}` for the finitely many pairs. Now the images of the `s_r` in `F_{k'}(V_r)` agree on overlaps and
glue (iii) to `s ∈ F_{k'}(U)` with `s|_{V_r} = s_r`; then `ι_{k'}(s)|_{V_r} = t|_{V_r}` for all `r`, so
`ι_{k'}(s) = t` by (iii).

*Edge cases.* `U = ∅`: both `G(∅)` and `F_j(∅)` are `0` (sheaves), and `J` is nonempty (filtered), so both
conjuncts hold. `X` need not be compact for this statement.

Formalized exactly along these lines: (i)+(ii) are `TopCat.Sheaf.SectionsColimit.exists_germ_eq` and
`TopCat.Sheaf.SectionsColimit.stalk_map_ι_eq_iff` (via `TopCat.Sheaf.SectionsColimit.isColimit_stalkTypesCocone`:
`Sheaf.forget ⋙ stalkFunctor` is a left adjoint (`Mathlib.Topology.Sheaves.Skyscraper`) and
`forget AddCommGrpCat` preserves filtered colimits); the kernel conjunct is
`TopCat.Sheaf.SectionsColimit.exists_map_eq_zero_of_ι_eq_zero`, the surjectivity conjunct is
`TopCat.Sheaf.SectionsColimit.exists_ι_eq`. -/
theorem TopCat.Sheaf.sections_colimit_bijective_of_isCompact {X : TopCat.{u}} [QuasiSeparatedSpace X]
    (hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    {J : Type u} [CategoryTheory.SmallCategory J] [CategoryTheory.IsFiltered J]
    (F : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (U : TopologicalSpace.Opens X) (hU : IsCompact (U : Set X)) :
    (∀ t : (CategoryTheory.Limits.colimit F).obj.obj (op U),
      ∃ (j : J) (s : (F.obj j).obj.obj (op U)),
        (CategoryTheory.Limits.colimit.ι F j).hom.app (op U) s = t) ∧
    (∀ (j : J) (s : (F.obj j).obj.obj (op U)),
      (CategoryTheory.Limits.colimit.ι F j).hom.app (op U) s = 0 →
        ∃ (k : J) (a : j ⟶ k), (F.map a).hom.app (op U) s = 0) :=
  ⟨fun t => TopCat.Sheaf.SectionsColimit.exists_ι_eq F hB U hU t,
    fun j s hs => TopCat.Sheaf.SectionsColimit.exists_map_eq_zero_of_ι_eq_zero F hB U hU j s hs⟩

end
