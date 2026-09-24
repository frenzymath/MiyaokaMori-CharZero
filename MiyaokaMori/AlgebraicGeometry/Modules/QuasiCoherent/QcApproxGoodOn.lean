import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfAffineLocalizing
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections

/-! # The induction invariant for finite type approximation

Support module for `QcFiniteTypeApproxFiniteSections` (Stacks 01PD–01PE).

A sub-presheaf `G ⊆ F` of a quasi-coherent module `F` on a scheme `S` is **good on an open `U`**
(`QcApprox.GoodOn F G U`) if, on the opens contained in `U`, it behaves like a finite type quasi-coherent
submodule:
1. membership is local (`mem_of_locally`: `G` is a subsheaf on `U`);
2. on an affine `U'' ≤ U`, sections of `G` over a basic open `D(h)` are, after multiplying by a power of
   `h`, restrictions of sections of `G` over `U''` (`exists_pow_smul_eq_map`: the localization property that
   makes `G` quasi-coherent, cf. `isQuasicoherent_of_affine_localizing`);
3. `G` is **saturated** in `F` on affines `U'' ≤ U`: if a section `t` of `F` over `U''` restricts into `G`
   on `D(h)`, then `h ^ m • t ∈ G(U'')` for some `m` (`exists_pow_smul_mem`);
4. every point of `U` has an affine neighbourhood `U'' ≤ U` on which `G(U'')` is spanned by finitely many
   sections (`exists_affine_fg`: finite type).

This file proves:
* `GoodOn.exists_pow_smul_map_inf_mem`: saturation over the quasi-compact intersection `U'' ⊓ U` for an
  arbitrary affine `U''` (finitely many basic opens of `U''` inside `U'' ⊓ U`, saturation on each, then
  locality). It is the engine of both the gluing step and the extension step.
* `toModules`: a sub-presheaf good on `⊤` is a sheaf of modules (`GoodOn.isSheaf`), quasi-coherent
  (`toModules_isQuasicoherent`) and of finite type (`toModules_isFiniteType`), with inclusion
  `toModules.ι` whose components are the subtype inclusions.

Sources: Stacks 01PC/01PD (the extension argument), 01IB (affine-local criterion of quasi-coherence),
01PB (finite type on affines).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.QcApprox

variable {S : AlgebraicGeometry.Scheme.{u}} (F : S.Modules)

/-- The sections of the sub-presheaf `G ⊆ F` over `U`, as a submodule of `Γ(F, U)` over `Γ(S, U)` (this is
`objΓ G (U)` with the ring and module spelled through the `Γ(-, U)` notation, so that the standard
`Submodule` API applies; the two spellings are definitionally equal). -/
abbrev objΓ {F : S.Modules} (G : F.val.Submodule) (U : S.Opens) : Submodule Γ(S, U) Γ(F, U) := G.obj (op U)

/-- The induction invariant of Stacks 01PD in sub-presheaf form: `G ⊆ F` is a subsheaf on the opens
contained in `U`, quasi-coherent there (localization property on affines), saturated in `F` on affines, and
of finite type at every point of `U`. See the module docstring. -/
structure GoodOn (G : F.val.Submodule) (U : S.Opens) : Prop where
  mem_of_locally : ∀ (U' : S.Opens), U' ≤ U → ∀ t : Γ(F, U'),
    (∀ x ∈ U', ∃ (U₀ : S.Opens) (h₀ : U₀ ≤ U'), x ∈ U₀ ∧
      F.presheaf.map (homOfLE h₀).op t ∈ objΓ G (U₀)) → t ∈ objΓ G (U')
  exists_pow_smul_eq_map : ∀ (U'' : S.Opens), U'' ≤ U → AlgebraicGeometry.IsAffineOpen U'' →
    ∀ (h : Γ(S, U'')) (s : Γ(F, S.basicOpen h)), s ∈ objΓ G ((S.basicOpen h)) →
    ∃ (n : ℕ) (t : Γ(F, U'')), t ∈ objΓ G (U'') ∧
      F.presheaf.map (homOfLE (S.basicOpen_le h)).op t =
        (S.presheaf.map (homOfLE (S.basicOpen_le h)).op h) ^ n • s
  exists_pow_smul_mem : ∀ (U'' : S.Opens), U'' ≤ U → AlgebraicGeometry.IsAffineOpen U'' →
    ∀ (h : Γ(S, U'')) (t : Γ(F, U'')),
    F.presheaf.map (homOfLE (S.basicOpen_le h)).op t ∈ objΓ G ((S.basicOpen h)) →
    ∃ m : ℕ, h ^ m • t ∈ objΓ G (U'')
  exists_affine_fg : ∀ x ∈ U, ∃ (U'' : S.Opens), AlgebraicGeometry.IsAffineOpen U'' ∧ x ∈ U'' ∧
    U'' ≤ U ∧ ∃ (p : ℕ) (g : Fin p → Γ(F, U'')), objΓ G (U'') = Submodule.span Γ(S, U'') (Set.range g)

variable {F}

/-- Restriction of sections of `G` stays in `G`. -/
theorem mem_map_of_mem (G : F.val.Submodule) {U V : S.Opens} (h : V ≤ U) {t : Γ(F, U)}
    (ht : t ∈ objΓ G (U)) : F.presheaf.map (homOfLE h).op t ∈ objΓ G (V) :=
  G.map_mem (homOfLE h).op ht

/-- Two successive restrictions are one restriction. -/
theorem map_map {U V W : S.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (t : Γ(F, U)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op t) =
      F.presheaf.map (homOfLE (h₂.trans h₁)).op t := by
  rw [← F.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]

/-- Restriction along `U ≤ U` is the identity. -/
theorem map_self {U : S.Opens} (h : U ≤ U) (t : Γ(F, U)) :
    F.presheaf.map (homOfLE h).op t = t := by
  have : homOfLE h = 𝟙 U := rfl
  rw [this, op_id, F.presheaf.map_id]
  rfl

/-- Membership in `G` is invariant under restriction along an equality of opens (given as two
inequalities). -/
theorem mem_iff_map_mem_of_le_of_le (G : F.val.Submodule) {U V : S.Opens} (h₁ : V ≤ U) (h₂ : U ≤ V)
    (t : Γ(F, U)) : t ∈ objΓ G (U) ↔ F.presheaf.map (homOfLE h₁).op t ∈ objΓ G (V) := by
  constructor
  · exact mem_map_of_mem G h₁
  · intro ht
    have := mem_map_of_mem G h₂ ht
    rwa [map_map, map_self] at this

/-- **Generators localize.** If `G` is good on `U`, `U'' ≤ U` is affine and `G(U'')` is spanned by
`g : Fin p → Γ(F, U'')`, then on a basic open `D(a)` of `U''` the module `G(D(a))` is spanned by the
restrictions of the `g i` (Stacks 01PB, via the localization property `exists_pow_smul_eq_map` and the
invertibility of `a` on `D(a)`). -/
theorem GoodOn.obj_basicOpen_eq_span {G : F.val.Submodule} {U : S.Opens} (hG : GoodOn F G U)
    {U'' : S.Opens} (hle : U'' ≤ U) (hU'' : AlgebraicGeometry.IsAffineOpen U'') (a : Γ(S, U''))
    {p : ℕ} (g : Fin p → Γ(F, U'')) (hg : objΓ G (U'') = Submodule.span Γ(S, U'') (Set.range g)) :
    objΓ G ((S.basicOpen a)) = Submodule.span Γ(S, S.basicOpen a)
      (Set.range fun i => F.presheaf.map (homOfLE (S.basicOpen_le a)).op (g i)) := by
  apply le_antisymm
  · intro s hs
    obtain ⟨n, t, htG, ht⟩ := hG.exists_pow_smul_eq_map U'' hle hU'' a s hs
    have hunit : IsUnit (S.presheaf.map (homOfLE (S.basicOpen_le a)).op a) :=
      S.toRingedSpace.isUnit_res_basicOpen a
    obtain ⟨w, hw⟩ := hunit
    have hone : ((↑(w⁻¹ ^ n) : Γ(S, S.basicOpen a)) * (S.presheaf.map (homOfLE (S.basicOpen_le a)).op a) ^ n) = 1 := by
      rw [← hw, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    have hs' : s = (↑(w⁻¹ ^ n) : Γ(S, S.basicOpen a)) • F.presheaf.map (homOfLE (S.basicOpen_le a)).op t :=
      calc s = (1 : Γ(S, S.basicOpen a)) • s := (one_smul _ _).symm
        _ = ((↑(w⁻¹ ^ n) : Γ(S, S.basicOpen a)) * (S.presheaf.map (homOfLE (S.basicOpen_le a)).op a) ^ n) • s := by
            rw [hone]
        _ = (↑(w⁻¹ ^ n) : Γ(S, S.basicOpen a)) • ((S.presheaf.map (homOfLE (S.basicOpen_le a)).op a) ^ n • s) :=
            mul_smul _ _ _
        _ = _ := by rw [ht]
    rw [hs']
    apply Submodule.smul_mem
    have htG' : t ∈ Submodule.span Γ(S, U'') (Set.range g) := hg ▸ htG
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(S, U'')).mp htG'
    rw [← hc, map_sum]
    apply Submodule.sum_mem
    intro i _
    have := AlgebraicGeometry.Scheme.Modules.map_smul F (homOfLE (S.basicOpen_le a)) (c i) (g i)
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : g i ∈ objΓ G (U'') := hg ▸ Submodule.subset_span ⟨i, rfl⟩
    exact mem_map_of_mem G (S.basicOpen_le a) this

/-- On a basic open of an affine `U'' ≤ U` with `G(U'')` finitely generated, `G(D(a))` is spanned by
finitely many sections. -/
theorem GoodOn.exists_span_basicOpen {G : F.val.Submodule} {U : S.Opens} (hG : GoodOn F G U)
    {U'' : S.Opens} (hle : U'' ≤ U) (hU'' : AlgebraicGeometry.IsAffineOpen U'')
    (hfg : ∃ (p : ℕ) (g : Fin p → Γ(F, U'')), objΓ G (U'') = Submodule.span Γ(S, U'') (Set.range g))
    (a : Γ(S, U'')) : ∃ (p : ℕ) (g : Fin p → Γ(F, S.basicOpen a)),
      objΓ G ((S.basicOpen a)) = Submodule.span Γ(S, S.basicOpen a) (Set.range g) := by
  obtain ⟨p, g, hg⟩ := hfg
  exact ⟨p, _, hG.obj_basicOpen_eq_span hle hU'' a g hg⟩

/-- Goodness is monotone in the open (for the finite type clause, shrink the affine neighbourhood to a
basic open contained in the smaller open and use `exists_span_basicOpen`). -/
theorem GoodOn.mono {G : F.val.Submodule} {U U' : S.Opens} (hG : GoodOn F G U) (h : U' ≤ U) :
    GoodOn F G U' where
  mem_of_locally V hV := hG.mem_of_locally V (hV.trans h)
  exists_pow_smul_eq_map V hV := hG.exists_pow_smul_eq_map V (hV.trans h)
  exists_pow_smul_mem V hV := hG.exists_pow_smul_mem V (hV.trans h)
  exists_affine_fg x hx := by
    obtain ⟨U'', hU'', hxU'', hle, hfg⟩ := hG.exists_affine_fg x (h hx)
    obtain ⟨a, ha, hxa⟩ := hU''.exists_basicOpen_le (V := U'' ⊓ U') ⟨x, ⟨hxU'', hx⟩⟩ hxU''
    exact ⟨S.basicOpen a, hU''.basicOpen a, hxa, ha.trans inf_le_right,
      hG.exists_span_basicOpen hle hU'' hfg a⟩

/-- **Saturation over a quasi-compact intersection.** Let `G` be good on the quasi-compact open `U` of the
quasi-separated scheme `S`, `U''` an affine open and `h ∈ Γ(U'', O)`. If `t ∈ F(U'')` restricts into `G`
on `D(h) ⊓ U`, then `h ^ m • t` restricts into `G` on `U'' ⊓ U` for some `m`.

Proof. `U'' ⊓ U` is quasi-compact (`S` quasi-separated), so it is covered by finitely many basic opens
`D(a_x)` of `U''` contained in `U'' ⊓ U`. On each `D(a_x)` (affine, `≤ U`) the section `t|_{D(a_x)}`
restricts into `G` on `D(a_x) ⊓ D(h) = D(h|_{D(a_x)})`, so saturation (`exists_pow_smul_mem`) gives `m_x`
with `(h ^ m_x • t)|_{D(a_x)} ∈ G`. With `m := max m_x`, `(h ^ m • t)|_{D(a_x)} ∈ G` for all `x`, and
locality (`mem_of_locally` on `U'' ⊓ U ≤ U`) gives the claim. -/
theorem GoodOn.exists_pow_smul_map_inf_mem [QuasiSeparatedSpace S] {G : F.val.Submodule}
    {U : S.Opens} (hG : GoodOn F G U) (hU : IsCompact (U : Set S)) {U'' : S.Opens}
    (hU'' : AlgebraicGeometry.IsAffineOpen U'') (h : Γ(S, U'')) (t : Γ(F, U''))
    (ht : F.presheaf.map (homOfLE (inf_le_left.trans (S.basicOpen_le h) :
      S.basicOpen h ⊓ U ≤ U'')).op t ∈ objΓ G ((S.basicOpen h ⊓ U))) :
    ∃ m : ℕ, F.presheaf.map (homOfLE (inf_le_left : U'' ⊓ U ≤ U'')).op (h ^ m • t) ∈
      objΓ G ((U'' ⊓ U)) := by
  classical
  have hcomp : IsCompact ((U'' ⊓ U : S.Opens) : Set S) :=
    hU''.isCompact.inter_of_isOpen hU U''.2 U.2
  have hpt : ∀ x : S, x ∈ U'' ⊓ U →
      ∃ a : Γ(S, U''), S.basicOpen a ≤ U'' ⊓ U ∧ x ∈ S.basicOpen a := fun x hx =>
    hU''.exists_basicOpen_le ⟨x, hx⟩ hx.1
  choose! a ha using hpt
  obtain ⟨T, hT⟩ := hcomp.elim_finite_subcover
    (fun x : (U'' ⊓ U : S.Opens) => (S.basicOpen (a x) : Set S))
    (fun x => (S.basicOpen (a x)).2)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (ha x hx).2⟩)
  have hsat : ∀ x : (U'' ⊓ U : S.Opens), ∃ m : ℕ,
      F.presheaf.map (homOfLE ((ha x x.2).1.trans inf_le_left)).op (h ^ m • t) ∈
        objΓ G ((S.basicOpen (a x))) := by
    intro x
    have hxU : S.basicOpen (a x) ≤ U := (ha x x.2).1.trans inf_le_right
    have hle : S.basicOpen (a x) ≤ U'' := (ha x x.2).1.trans inf_le_left
    set h' : Γ(S, S.basicOpen (a x)) := S.presheaf.map (homOfLE hle).op h with hh'
    have hbo : S.basicOpen h' = S.basicOpen (a x) ⊓ S.basicOpen h := S.basicOpen_res _ _
    have hle2 : S.basicOpen h' ≤ S.basicOpen h ⊓ U := by
      rw [hbo]
      exact le_inf inf_le_right (inf_le_left.trans hxU)
    obtain ⟨m, hm⟩ := hG.exists_pow_smul_mem _ hxU (hU''.basicOpen (a x)) h'
      (F.presheaf.map (homOfLE hle).op t) (by
        rw [map_map]
        have := mem_map_of_mem G hle2 ht
        rwa [map_map] at this)
    refine ⟨m, ?_⟩
    rw [Scheme.Modules.map_smul, map_pow]
    exact hm
  choose m hm using hsat
  refine ⟨T.sup m, ?_⟩
  apply hG.mem_of_locally _ inf_le_right
  intro y hy
  obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.mp (hT hy)
  refine ⟨S.basicOpen (a x), (ha x x.2).1, hyx, ?_⟩
  rw [map_map]
  have hle := Finset.le_sup (f := m) hxT
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, Scheme.Modules.map_smul]
  exact (G.obj _).smul_mem _ (hm x)

section ToModules

/-- A sub-presheaf good on `⊤` is a subsheaf: gluing happens in `F`, and membership is local
(`mem_of_locally`). -/
theorem GoodOn.isSheaf {G : F.val.Submodule} (hG : GoodOn F G ⊤) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology S) G.toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hsf
  have hcompat : F.presheaf.IsCompatible U (fun i ↦ (sf i).val) := fun i j =>
    congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hunique⟩ :=
    (show F.presheaf.IsSheaf from F.isSheaf).isSheafUniqueGluing U (fun i ↦ (sf i).val) hcompat
  have hsG : s ∈ objΓ G ((iSup U)) := by
    apply hG.mem_of_locally _ le_top
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨U i, le_iSup U i, hi, ?_⟩
    change F.presheaf.map (Opens.leSupr U i).op s ∈ _
    rw [hs i]
    exact (sf i).property
  exact ⟨⟨s, hsG⟩, fun i => Subtype.ext (hs i),
    fun t ht => Subtype.ext (hunique t.val fun i => congrArg Subtype.val (ht i))⟩

/-- The sheaf of modules attached to a sub-presheaf `G ⊆ F` good on `⊤`: its sections over `U` are the
elements of `objΓ G (U)`. -/
def toModules (G : F.val.Submodule) (hG : GoodOn F G ⊤) : S.Modules where
  val := G.toPresheafOfModules
  isSheaf := hG.isSheaf

/-- The inclusion `toModules G hG ⟶ F`. -/
def toModules.ι (G : F.val.Submodule) (hG : GoodOn F G ⊤) : toModules G hG ⟶ F := ⟨G.ι⟩

theorem toModules.ι_app_apply (G : F.val.Submodule) (hG : GoodOn F G ⊤) (U : S.Opens)
    (x : Γ(toModules G hG, U)) : ((toModules.ι G hG).val.app (op U)).hom x = x.val := rfl

/-- `toModules G hG` is quasi-coherent (affine-local criterion: the localization property is
`exists_pow_smul_eq_map`, uniqueness is inherited from the quasi-coherent `F`). -/
theorem toModules_isQuasicoherent [F.IsQuasicoherent] (G : F.val.Submodule) (hG : GoodOn F G ⊤) :
    (toModules G hG).IsQuasicoherent := by
  apply AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_affine_localizing
  · intro U hU h s
    obtain ⟨n, t, htG, ht⟩ := hG.exists_pow_smul_eq_map U le_top hU h s.val s.property
    exact ⟨n, ⟨t, htG⟩, Subtype.ext ht⟩
  · intro U hU h t ht
    obtain ⟨n, hn⟩ := F.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hU h t.val
      (congrArg Subtype.val ht)
    exact ⟨n, Subtype.ext hn⟩

/-- `toModules G hG` is of finite type (`exists_affine_fg` + Stacks 01PB in the form
`isFiniteType_of_finite_affine_sections`). -/
theorem toModules_isFiniteType [F.IsQuasicoherent] (G : F.val.Submodule) (hG : GoodOn F G ⊤) :
    (toModules G hG).IsFiniteType := by
  have := toModules_isQuasicoherent G hG
  apply AlgebraicGeometry.Scheme.Modules.isFiniteType_of_finite_affine_sections
  intro x
  obtain ⟨U'', hU'', hx, -, p, g, hg⟩ := hG.exists_affine_fg x trivial
  refine ⟨U'', hU'', hx, ?_⟩
  have hfg : (objΓ G U'').FG := hg ▸ Submodule.fg_span (Set.finite_range g)
  have hfin : Module.Finite Γ(S, U'') (objΓ G U'') := (Module.Finite.iff_fg (N := objΓ G U'')).mpr hfg
  exact hfin

end ToModules

end AlgebraicGeometry.Scheme.Modules.QcApprox

end
