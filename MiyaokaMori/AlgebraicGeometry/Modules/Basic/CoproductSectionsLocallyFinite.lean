import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPreservesColimits

/-! # Sections of a coproduct of sheaves of modules are locally finite sums

**Sections of a coproduct of sheaves of modules are locally finite sums** (Stacks 01AI type statement;
"Γ commutes with direct sums on a quasi-compact space").

For a colimit cocone `c` of a discrete diagram `F : Discrete ι ⥤ X.Modules` (a coproduct `∐ F_i` together
with its injections `c.ι.app ⟨i⟩`):

* `exists_locally_finite_sum_of_isColimit`: every section `t` of `c.pt` over `U` is, near each point of `U`,
  a finite sum `Σ_{i∈s} (c.ι.app ⟨i⟩)(z i)` of images of sections of the pieces.
* `exists_finset_sum_eq_of_isColimit` (`X` quasi-compact): given "projections" `p q : c.pt ⟶ F_q` with
  `ι_m ≫ p q = 0` for `m ≠ q` and `ι_q ≫ p q = 𝟙`, a global section `t` has only finitely many nonzero
  components `(p q) t`, and `t = Σ_q ι_q ((p q) t)` over a finite set containing the support.

Route:
1. Coproducts in `X.Modules` are the sheafification `L` of the presheaf coproduct `Q := ∐ (forget F_i)`:
   `L` is a left adjoint (`PresheafOfModules.sheafificationAdjunction`), hence preserves colimits, and the
   counit `L (forget F_i) ≅ F_i` is an iso; so `L Q ≅ c.pt` compatibly with the injections
   (`IsColimit.coconePointUniqueUpToIso`). Writing `ψ` for this iso, `ι_i^Q ≫ η_Q ≫ forget ψ = forget ι_i`
   (unit naturality + the triangle identity).
2. Sections of `L Q` are locally in the image of the unit `η_Q` (`isLocallySurjective_toSheafify`,
   read on the site `Opens X`).
3. Sections of the presheaf coproduct over `V` form the coproduct of the `ModuleCat` pieces
   (`PresheafOfModules.evaluation` preserves colimits), and every element of a coproduct in `ModuleCat` is a
   finite sum of images of the injections (the joint image spans, by uniqueness of the induced map to the
   quotient by the span).
4. Quasi-compact case: choose a finite subcover of the local presentations; separatedness of the sheaves
   (`TopCat.Sheaf.eq_of_locally_eq'`) identifies the global section with the finite sum and kills the
   components outside the union of the finite index sets.

Reference: Stacks 01AI (sections of a direct sum of sheaves on a quasi-compact space). Used for the
decomposition `Γ(Tot L, p^*M) = ⊕_q H^0(M ⊗ L^{-q})` of the sections on a total space
(`GradedQCAlgebra.tensorComponent_finite` / `sum_tensorComponent`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **Elements of a coproduct in `ModuleCat` are finite sums of images of the injections.**
Proof: the joint range `W = ⨆ i, range (ι_i)` is `⊤`, because the quotient map `c.pt → c.pt ⧸ W` and `0`
agree after every `ι_i`, hence coincide by the uniqueness part of the colimit property; then unwind
`Submodule.mem_iSup_iff_exists_finset` and `Submodule.mem_iSup_finset_iff_exists_sum`. -/
theorem ModuleCat.exists_finset_sum_of_isColimit {R : Type u} [Ring R] {ι : Type}
    {F : Discrete ι ⥤ ModuleCat.{u} R} {c : Cocone F} (hc : IsColimit c) (y : c.pt) :
    ∃ (s : Finset ι) (z : ∀ i, F.obj ⟨i⟩), y = ∑ i ∈ s, (c.ι.app ⟨i⟩).hom (z i) := by
  let W : Submodule R c.pt := ⨆ i : ι, LinearMap.range (c.ι.app ⟨i⟩).hom
  have hW_top : W = ⊤ := by
    have h0 : (ModuleCat.ofHom W.mkQ : c.pt ⟶ ModuleCat.of R (c.pt ⧸ W)) = 0 := by
      refine hc.hom_ext ?_
      rintro ⟨i⟩
      ext v
      show W.mkQ ((c.ι.app ⟨i⟩).hom v) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ v)
    refine Submodule.eq_top_iff'.mpr fun y => ?_
    have h1 := congrArg (fun f : c.pt ⟶ ModuleCat.of R (c.pt ⧸ W) => f.hom y) h0
    have h2 : W.mkQ y = 0 := h1
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  have hy : y ∈ W := hW_top ▸ Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hy
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).mp hs
  choose z hz using fun i => LinearMap.mem_range.mp (μ i).2
  exact ⟨s, z, hμ.symm.trans (Finset.sum_congr rfl fun i _ => (hz i).symm)⟩

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Sections of a sheafification are locally in the image of the unit
(`Presheaf.isLocallySurjective_toSheafify`, read on the site `Opens X`). -/
theorem exists_sheafification_unit_app_eq_map
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) (U : X.Opens)
    (s : ((((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).val.obj (op U)) : Type u))
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ t : P.obj (op V),
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op V) t =
        ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).val.map (homOfLE hVU).op s := by
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf) s
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := hmem x hx
  exact ⟨V, leOfHom i, hxV, t, ht⟩

/-- The sheafification adjunction of `X.Modules`, written with the abbreviations `sheafificationToModules` /
`forgetToPresheafModules` of `ModulesTensorPreservesColimits` (an `abbrev`, so that instance search can
see through it; a `let` inside a proof cannot be unfolded by instance search). -/
abbrev sheafificationAdjToModules (X : AlgebraicGeometry.Scheme.{u}) :
    _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⊣
      SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj) :=
  _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)

set_option backward.isDefEq.respectTransparency false in
/-- **Sections of a coproduct of sheaves of modules are locally finite sums of images of the injections.**
`c` is any colimit cocone of a discrete diagram `F : Discrete ι ⥤ X.Modules`. -/
theorem exists_locally_finite_sum_of_isColimit {ι : Type}
    {F : Discrete ι ⥤ X.Modules} {c : Cocone F} (hc : IsColimit c) (U : X.Opens)
    (t : (c.pt.val.obj (op U) : Type u)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ (s : Finset ι) (z : ∀ i, ((F.obj ⟨i⟩).val.obj (op V) : Type u)),
        c.pt.val.map (homOfLE hVU).op t = ∑ i ∈ s, ((c.ι.app ⟨i⟩).val.app (op V)).hom (z i) := by
  -- P : the presheaf diagram; its colimit is the presheaf coproduct
  let P : Discrete ι ⥤ _root_.PresheafOfModules.{u} X.ringCatSheaf.obj := F ⋙ forgetToPresheafModules X
  have : PreservesColimitsOfSize.{0, 0} (sheafificationToModules X) :=
    (sheafificationAdjToModules X).leftAdjoint_preservesColimits
  have hcL : IsColimit ((sheafificationToModules X).mapCocone (colimit.cocone P)) :=
    isColimitOfPreserves (sheafificationToModules X) (colimit.isColimit P)
  let ci := asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  let e0 := Functor.isoWhiskerLeft F ci
  let e : P ⋙ sheafificationToModules X ≅ F := e0
  have hc₂ : IsColimit ((Cocone.precompose e.hom).obj c) := (IsColimit.precomposeHomEquiv e c).symm hc
  let ψ : (sheafificationToModules X).obj (colimit P) ≅ c.pt := hcL.coconePointUniqueUpToIso hc₂
  have hψ : ∀ i : ι, (sheafificationToModules X).map (colimit.ι P ⟨i⟩) ≫ ψ.hom =
      (sheafificationAdjToModules X).counit.app (F.obj ⟨i⟩) ≫ c.ι.app ⟨i⟩ :=
    fun i => hcL.comp_coconePointUniqueUpToIso_hom hc₂ ⟨i⟩
  -- the key composite identity `ι_i ≫ η ≫ fgR ψ = fgR ι_i`
  have hcomp : ∀ i : ι, colimit.ι P ⟨i⟩ ≫ (sheafificationAdjToModules X).unit.app (colimit P) ≫
      (forgetToPresheafModules X).map ψ.hom = (forgetToPresheafModules X).map (c.ι.app ⟨i⟩) := by
    intro i
    have h1 : colimit.ι P ⟨i⟩ ≫ (sheafificationAdjToModules X).unit.app (colimit P) ≫
        (forgetToPresheafModules X).map ψ.hom =
        ((sheafificationAdjToModules X).unit.app (P.obj ⟨i⟩) ≫
          (forgetToPresheafModules X).map ((sheafificationToModules X).map (colimit.ι P ⟨i⟩))) ≫
          (forgetToPresheafModules X).map ψ.hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun g => g ≫ (forgetToPresheafModules X).map ψ.hom)
          ((sheafificationAdjToModules X).unit_naturality (colimit.ι P ⟨i⟩)).symm)
    have h2 : ((sheafificationAdjToModules X).unit.app (P.obj ⟨i⟩) ≫
          (forgetToPresheafModules X).map ((sheafificationToModules X).map (colimit.ι P ⟨i⟩))) ≫
          (forgetToPresheafModules X).map ψ.hom =
        (sheafificationAdjToModules X).unit.app (P.obj ⟨i⟩) ≫
          (forgetToPresheafModules X).map ((sheafificationAdjToModules X).counit.app (F.obj ⟨i⟩) ≫
            c.ι.app ⟨i⟩) :=
      (Category.assoc _ _ _).trans (congrArg (fun g => (sheafificationAdjToModules X).unit.app (P.obj ⟨i⟩) ≫ g)
        (((forgetToPresheafModules X).map_comp _ _).symm.trans (congrArg _ (hψ i))))
    have h3 : (sheafificationAdjToModules X).unit.app (P.obj ⟨i⟩) ≫
          (forgetToPresheafModules X).map ((sheafificationAdjToModules X).counit.app (F.obj ⟨i⟩) ≫
            c.ι.app ⟨i⟩) =
        ((sheafificationAdjToModules X).unit.app ((forgetToPresheafModules X).obj (F.obj ⟨i⟩)) ≫
          (forgetToPresheafModules X).map ((sheafificationAdjToModules X).counit.app (F.obj ⟨i⟩))) ≫
          (forgetToPresheafModules X).map (c.ι.app ⟨i⟩) :=
      (congrArg (fun g => (sheafificationAdjToModules X).unit.app (P.obj ⟨i⟩) ≫ g)
        ((forgetToPresheafModules X).map_comp _ _)).trans (Category.assoc _ _ _).symm
    have h4 : ((sheafificationAdjToModules X).unit.app ((forgetToPresheafModules X).obj (F.obj ⟨i⟩)) ≫
          (forgetToPresheafModules X).map ((sheafificationAdjToModules X).counit.app (F.obj ⟨i⟩))) ≫
          (forgetToPresheafModules X).map (c.ι.app ⟨i⟩) =
        (forgetToPresheafModules X).map (c.ι.app ⟨i⟩) :=
      (congrArg (fun g => g ≫ (forgetToPresheafModules X).map (c.ι.app ⟨i⟩))
        ((sheafificationAdjToModules X).right_triangle_components (F.obj ⟨i⟩))).trans (Category.id_comp _)
    exact h1.trans (h2.trans (h3.trans h4))
  -- local presentation of t₀ := ψ⁻¹ t through the unit
  let t₀ : (((sheafificationToModules X).obj (colimit P)).val.obj (op U) : Type u) :=
    (ψ.inv.val.app (op U)).hom t
  obtain ⟨V, hVU, hxV, y, hy⟩ := exists_sheafification_unit_app_eq_map (colimit P) U t₀ x hx
  -- decompose y in the ModuleCat coproduct (evaluation at V preserves colimits)
  have hcV : IsColimit ((_root_.PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)).mapCocone
      (colimit.cocone P)) :=
    isColimitOfPreserves (_root_.PresheafOfModules.evaluation X.ringCatSheaf.obj (op V))
      (colimit.isColimit P)
  obtain ⟨s, z, hz⟩ := ModuleCat.exists_finset_sum_of_isColimit hcV y
  refine ⟨V, hVU, hxV, s, z, ?_⟩
  -- t = ψ t₀
  have ht : t = (ψ.hom.val.app (op U)).hom t₀ := by
    show t = ((ψ.inv ≫ ψ.hom).val.app (op U)).hom t
    rw [ψ.inv_hom_id]
    rfl
  -- restriction commutes with ψ
  have hnat : c.pt.val.map (homOfLE hVU).op ((ψ.hom.val.app (op U)).hom t₀) =
      (ψ.hom.val.app (op V)).hom (((sheafificationToModules X).obj (colimit P)).val.map (homOfLE hVU).op t₀) :=
    (_root_.PresheafOfModules.naturality_apply ψ.hom.val (homOfLE hVU).op t₀).symm
  have h4 : ∀ i : ι, (ψ.hom.val.app (op V)).hom (((sheafificationAdjToModules X).unit.app (colimit P)).app (op V)
      ((((_root_.PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)).mapCocone
        (colimit.cocone P)).ι.app ⟨i⟩).hom (z i))) = ((c.ι.app ⟨i⟩).val.app (op V)).hom (z i) := by
    intro i
    have h5 := congrArg (fun g : P.obj ⟨i⟩ ⟶ (forgetToPresheafModules X).obj c.pt => (g.app (op V)).hom (z i))
      (hcomp i)
    exact h5
  have e1 : c.pt.val.map (homOfLE hVU).op t =
      (ψ.hom.val.app (op V)).hom (((sheafificationAdjToModules X).unit.app (colimit P)).app (op V) y) :=
    (congrArg _ ht).trans (hnat.trans (congrArg _ hy.symm))
  have e2 : (ψ.hom.val.app (op V)).hom (((sheafificationAdjToModules X).unit.app (colimit P)).app (op V) y) =
      ∑ i ∈ s, (ψ.hom.val.app (op V)).hom (((sheafificationAdjToModules X).unit.app (colimit P)).app (op V)
        ((((_root_.PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)).mapCocone
          (colimit.cocone P)).ι.app ⟨i⟩).hom (z i))) :=
    (congrArg _ (congrArg _ hz)).trans
      ((congrArg _ (map_sum (((sheafificationAdjToModules X).unit.app (colimit P)).app (op V)).hom
        (fun i => (((_root_.PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)).mapCocone
          (colimit.cocone P)).ι.app ⟨i⟩).hom (z i)) s)).trans
        (map_sum (ψ.hom.val.app (op V)).hom _ s))
  exact e1.trans (e2.trans (Finset.sum_congr rfl fun i _ => h4 i))

/-- **Γ commutes with direct sums on a quasi-compact scheme** (Stacks 01AI), in the form needed for graded
components. `c` is a colimit cocone of a discrete diagram in `X.Modules` with legs `ι_m := c.ι.app ⟨m⟩`;
`p q : c.pt ⟶ F_q` are projections with `ι_m ≫ p q = 0` (`m ≠ q`) and `ι_q ≫ p q = 𝟙`. For a global section
`t` there is a finite `Fs` outside of which all components `(p q) t` vanish, and `t = Σ_{q ∈ Fs} ι_q ((p q) t)`.

Proof: cover `X` by the opens `V x` of `exists_locally_finite_sum_of_isColimit` (`t|_{V x} = Σ_{m ∈ s x} ι_m (z x m)`),
take a finite subcover `T` (`isCompact_univ.elim_nhds_subcover`) and `Fs := ⋃_{x ∈ T} s x`. On `V x`,
`(p q)(t|_{V x}) = if q ∈ s x then z x q else 0` by the orthogonality relations, so both claims hold after
restriction to every `V x`; conclude by separatedness of the sheaves (`TopCat.Sheaf.eq_of_locally_eq'`). -/
theorem exists_finset_sum_eq_of_isColimit [CompactSpace X] {ι : Type}
    {F : Discrete ι ⥤ X.Modules} {c : Cocone F} (hc : IsColimit c)
    (p : ∀ q : ι, c.pt ⟶ F.obj ⟨q⟩)
    (hp0 : ∀ m q, m ≠ q → c.ι.app ⟨m⟩ ≫ p q = 0)
    (hp1 : ∀ m, c.ι.app ⟨m⟩ ≫ p m = 𝟙 _)
    (t : (c.pt.val.obj (op ⊤) : Type u)) :
    ∃ Fs : Finset ι, (∀ q, q ∉ Fs → ((p q).val.app (op ⊤)).hom t = 0) ∧
      ∑ q ∈ Fs, ((c.ι.app ⟨q⟩).val.app (op ⊤)).hom (((p q).val.app (op ⊤)).hom t) = t := by
  classical
  have hloc : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      ∃ (s : Finset ι) (z : ∀ i, ((F.obj ⟨i⟩).val.obj (op V) : Type u)),
        c.pt.val.map (homOfLE (le_top : V ≤ ⊤)).op t =
          ∑ i ∈ s, ((c.ι.app ⟨i⟩).val.app (op V)).hom (z i) := by
    intro x
    obtain ⟨V, hVU, hxV, s, z, hz⟩ := exists_locally_finite_sum_of_isColimit hc ⊤ t x trivial
    exact ⟨V, hxV, s, z, hz⟩
  choose V hxV s z hz using hloc
  obtain ⟨T, -, hT⟩ := isCompact_univ.elim_nhds_subcover (fun x => ((V x : X.Opens) : Set X))
    (fun x _ => (V x).isOpen.mem_nhds (hxV x))
  -- separatedness on the finite cover
  have hsep : ∀ (M : X.Modules) (a b : (M.val.obj (op ⊤) : Type u)),
      (∀ x ∈ T, M.val.map (homOfLE (le_top : V x ≤ ⊤)).op a =
        M.val.map (homOfLE (le_top : V x ≤ ⊤)).op b) → a = b := by
    intro M a b h
    let Sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
    refine Sh.eq_of_locally_eq' (fun x : T => V x) ⊤ (fun x => homOfLE le_top) ?_ a b
      (fun x => h x.1 x.2)
    intro y _
    have hy := hT (Set.mem_univ y)
    rw [Set.mem_iUnion₂] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hyx⟩
  -- components of the restrictions
  have hcompo : ∀ (x : X) (q : ι),
      ((p q).val.app (op (V x))).hom (c.pt.val.map (homOfLE (le_top : V x ≤ ⊤)).op t) =
        if q ∈ s x then z x q else 0 := by
    intro x q
    have hterm : ∀ m ∈ s x,
        ((p q).val.app (op (V x))).hom (((c.ι.app ⟨m⟩).val.app (op (V x))).hom (z x m)) =
          if m = q then (if q ∈ s x then z x q else 0) else 0 := by
      intro m hm
      have h5 : ((p q).val.app (op (V x))).hom (((c.ι.app ⟨m⟩).val.app (op (V x))).hom (z x m)) =
          (((c.ι.app ⟨m⟩ ≫ p q).val.app (op (V x))).hom (z x m)) := rfl
      by_cases hmq : m = q
      · subst hmq
        refine h5.trans ?_
        refine (congrArg (fun g : F.obj ⟨m⟩ ⟶ F.obj ⟨m⟩ => (g.val.app (op (V x))).hom (z x m))
          (hp1 m)).trans ?_
        rw [if_pos rfl, if_pos hm]
        rfl
      · refine h5.trans ?_
        refine (congrArg (fun g : F.obj ⟨m⟩ ⟶ F.obj ⟨q⟩ => (g.val.app (op (V x))).hom (z x m))
          (hp0 m q hmq)).trans ?_
        rw [if_neg hmq]
        rfl
    refine (congrArg (((p q).val.app (op (V x))).hom) (hz x)).trans ?_
    refine (map_sum ((p q).val.app (op (V x))).hom
      (fun i => ((c.ι.app ⟨i⟩).val.app (op (V x))).hom (z x i)) (s x)).trans ?_
    refine (Finset.sum_congr rfl hterm).trans ?_
    refine (Finset.sum_ite_eq' (s x) q (fun _ => if q ∈ s x then z x q else 0)).trans ?_
    by_cases hq : q ∈ s x
    · rw [if_pos hq]
    · rw [if_neg hq, if_neg hq]
  refine ⟨T.biUnion s, ?_, ?_⟩
  · intro q hq
    refine hsep (F.obj ⟨q⟩) _ 0 fun x hx => ?_
    have hqx : q ∉ s x := fun h => hq (Finset.mem_biUnion.mpr ⟨x, hx, h⟩)
    have hn : (F.obj ⟨q⟩).val.map (homOfLE (le_top : V x ≤ ⊤)).op (((p q).val.app (op ⊤)).hom t) =
        ((p q).val.app (op (V x))).hom (c.pt.val.map (homOfLE (le_top : V x ≤ ⊤)).op t) :=
      (_root_.PresheafOfModules.naturality_apply (p q).val (homOfLE (le_top : V x ≤ ⊤)).op t).symm
    refine (hn.trans ((hcompo x q).trans (if_neg hqx))).trans ?_
    exact (map_zero _).symm
  · refine hsep c.pt _ t fun x hx => ?_
    have hsub : s x ⊆ T.biUnion s := fun q hq => Finset.mem_biUnion.mpr ⟨x, hx, hq⟩
    have hterm : ∀ q ∈ T.biUnion s,
        c.pt.val.map (homOfLE (le_top : V x ≤ ⊤)).op
            (((c.ι.app ⟨q⟩).val.app (op ⊤)).hom (((p q).val.app (op ⊤)).hom t)) =
          if q ∈ s x then ((c.ι.app ⟨q⟩).val.app (op (V x))).hom (z x q) else 0 := by
      intro q _
      have hn1 : c.pt.val.map (homOfLE (le_top : V x ≤ ⊤)).op
            (((c.ι.app ⟨q⟩).val.app (op ⊤)).hom (((p q).val.app (op ⊤)).hom t)) =
          ((c.ι.app ⟨q⟩).val.app (op (V x))).hom
            ((F.obj ⟨q⟩).val.map (homOfLE (le_top : V x ≤ ⊤)).op (((p q).val.app (op ⊤)).hom t)) :=
        (_root_.PresheafOfModules.naturality_apply (c.ι.app ⟨q⟩).val (homOfLE (le_top : V x ≤ ⊤)).op
          (((p q).val.app (op ⊤)).hom t)).symm
      have hn2 : (F.obj ⟨q⟩).val.map (homOfLE (le_top : V x ≤ ⊤)).op (((p q).val.app (op ⊤)).hom t) =
          ((p q).val.app (op (V x))).hom (c.pt.val.map (homOfLE (le_top : V x ≤ ⊤)).op t) :=
        (_root_.PresheafOfModules.naturality_apply (p q).val (homOfLE (le_top : V x ≤ ⊤)).op t).symm
      refine hn1.trans ((congrArg _ (hn2.trans (hcompo x q))).trans ?_)
      by_cases hq : q ∈ s x
      · rw [if_pos hq, if_pos hq]
      · rw [if_neg hq, if_neg hq]
        exact map_zero _
    refine (map_sum (c.pt.val.map (homOfLE (le_top : V x ≤ ⊤)).op).hom _ _).trans ?_
    refine (Finset.sum_congr rfl hterm).trans ?_
    refine (Finset.sum_ite_mem (T.biUnion s) (s x) _).trans ?_
    rw [Finset.inter_eq_right.mpr hsub]
    exact (hz x).symm

end AlgebraicGeometry.Scheme.Modules

end
