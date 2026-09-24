import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02utExtendByZeroCounit
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.Stacks00ae

/-! # The short exact sequence `0 → j_!j^*F → F → i_*i^*F → 0` (Stacks 02UT)

Stacks 02UT: an open `U` (`j : U → X`) and its closed complement `Z` (`i : Z → X`) give a short exact
sequence of abelian sheaves `0 → j_!j^*F → F → i_*i^*F → 0`.

Source: Stacks 02UT (the first step of the proof of Grothendieck vanishing 02UZ).

The support statement of Stacks 02UT (`j_!j^*F` is of the form `i'_*F'` for `i' : closure U → X`) is not
part of the Lean statement; it is proved separately in `Stacks02uzExtendByZero.lean`
(`isZero_restrict_extendByZero_of_disjoint`).

**Proof (Stacks 02UT, "check on stalks").** Write `Z = X \ U`, `i : Z → X`, `j : U → X`.
* `X₁ = j_!j^*F` and the counit `ε : j_!j^*F ⟶ F` are taken from `Stacks02utExtendByZeroCounit.lean`
  (`extendByZeroCounit`): `j_!j^*F` is the sheafification of the subpresheaf `P ⊆ j_*j^*F` with
  `P(V) = F(V)` for `V ⊆ U` and `0` otherwise, and `ε` is induced by `P ⟶ F`.
* `X₃ = i_*(i^{-1}F)` with `i^{-1}F` written as the sheafification of Mathlib's presheaf pullback
  (`closedComplPush`); it is isomorphic to `pushforwardClosed Z (restrictClosed F Z)` by Mathlib's
  `TopCat.Sheaf.pullbackIso` (`closedComplPushIso`). The map `g : F ⟶ X₃` (`closedComplUnit`) is the
  presheaf unit followed by `i_*` of the sheafification map.
* `ε ≫ g = 0` (`extendByZeroCounit_comp_closedComplUnit`): it suffices to check `P ⟶ F ⟶ i_*i^{-1}F`
  is zero, and over `V ⊆ U` the target `(i^{-1}F)(i⁻¹V) = (i^{-1}F)(∅)` vanishes, while over `V ⊄ U` the
  source `P(V)` vanishes.
* Stalks: for `x ∈ U`, `ε_x` is an isomorphism (`isIso_stalkFunctor_map_extendByZeroCounit_hom_of_mem`)
  and `(X₃)_x = 0` (Stacks 00AE, `isZero_stalk_pushforward_of_notMem_range`); for `x ∉ U`, `(X₁)_x = 0`
  (`isZero_stalk_extendByZero_of_notMem`) and `g_x` is an isomorphism
  (`isIso_stalkFunctor_map_closedComplUnit_hom`: `stalkPullbackIso` for the presheaf pullback,
  sheafification does not change stalks, `stalkPushforward_iso_of_isInducing` for the closed embedding `i`).
* Hence the sequence is exact on every stalk, `ε` is a monomorphism on every stalk and `g` is an
  epimorphism on every stalk; by Mathlib's `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`,
  `TopCat.Presheaf.mono_iff_stalk_mono` and `locally_surjective_iff_surjective_on_stalks` +
  `Sheaf.isLocallySurjective_iff_epi'`, the short complex `j_!j^*F ⟶ F ⟶ i_*i^{-1}F` is short exact.

This direct argument on abelian sheaves over `TopCat` uses only Mathlib and the modules
`Stacks02uzExtendByZero`, `Stacks00ae`, `Stacks02utStalkAux`, `Stacks02utExtendByZeroCounit`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (U : Opens X)
  (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The closed complement `Z = X \ U` as a space. -/
abbrev closedCompl : TopCat.{u} := TopCat.of ((U : Set X)ᶜ : Set X)

/-- The inclusion `i : Z → X` (the same term as in `restrictClosed` / `pushforwardClosed`). -/
abbrev closedComplι : closedCompl U ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem closedComplι_isClosedEmbedding : Topology.IsClosedEmbedding (closedComplι U) :=
  U.isOpen.isClosed_compl.isClosedEmbedding_subtypeVal

theorem notMem_range_closedComplι {x : X} (hx : x ∈ U) : x ∉ Set.range (closedComplι U) := by
  rintro ⟨z, hz⟩
  have hzx : (z : X) = x := hz
  exact z.2 (by rw [hzx]; exact hx)

/-- `i^{-1}F` as a presheaf (Mathlib's `Presheaf.pullback`, before sheafification). -/
abbrev closedComplPre : TopCat.Presheaf AddCommGrpCat.{u} (closedCompl U) :=
  (TopCat.Presheaf.pullback AddCommGrpCat.{u} (closedComplι U)).obj F.obj

/-- `X₃ = i_*(i^{-1}F)`, with `i^{-1}F` spelled as the sheafification of the presheaf pullback. -/
abbrev closedComplPush : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedComplι U)).obj
    ((presheafToSheaf (Opens.grothendieckTopology (closedCompl U)) AddCommGrpCat.{u}).obj
      (closedComplPre U F))

/-- `X₃ ≅ i_*i^{-1}F` in the spelling of the target statement (Mathlib's `Sheaf.pullbackIso`). -/
def closedComplPushIso :
    closedComplPush U F ≅
      TopCat.Sheaf.pushforwardClosed ((U : Set X)ᶜ) (TopCat.Sheaf.restrictClosed F ((U : Set X)ᶜ)) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedComplι U)).mapIso
    ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} (closedComplι U)).app F).symm

/-- The unit `F ⟶ i_*i^{-1}F`: the presheaf-level unit followed by `i_*` of the sheafification map. -/
def closedComplUnit : F ⟶ closedComplPush U F :=
  ObjectProperty.homMk
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedComplι U)).unit.app F.obj ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (closedComplι U)).map
        (toSheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F)))

theorem closedComplUnit_hom :
    (closedComplUnit U F).hom =
      (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedComplι U)).unit.app F.obj ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (closedComplι U)).map
          (toSheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F)) := rfl

/-- At a point of `Z`, the unit `F ⟶ i_*i^{-1}F` is an isomorphism on stalks (Stacks 00AE for `i_*`,
`stalkPullbackIso` for `i^{-1}`, and sheafification does not change stalks). -/
theorem isIso_stalkFunctor_map_closedComplUnit_hom (z : closedCompl U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (closedComplι U z)).map
      (closedComplUnit U F).hom) := by
  have hsp : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (closedComplι U)
      (sheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F)) z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
      (closedComplι_isClosedEmbedding U).isInducing _ z
  have hpb : IsIso (TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} (closedComplι U) F.obj z) :=
    (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} (closedComplι U) F.obj z).isIso_hom
  have hts : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
      (toSheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z AddCommGrpCat.{u} _
  have key : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (closedComplι U z)).map
        (closedComplUnit U F).hom ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (closedComplι U)
        (sheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F)) z =
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} (closedComplι U) F.obj z ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
          (toSheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F)) := by
    have h1 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (closedComplι U z)).map
        (closedComplUnit U F).hom =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (closedComplι U z)).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedComplι U)).unit.app F.obj) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (closedComplι U z)).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (closedComplι U)).map
            (toSheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F))) :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (closedComplι U z)).map_comp _ _
    erw [h1, Category.assoc, TopCat.Presheaf.stalkFunctor_map_pushforward_stalkPushforward,
      ← Category.assoc]
  have hcomp : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (closedComplι U z)).map
        (closedComplUnit U F).hom ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (closedComplι U)
        (sheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F)) z) := by
    rw [key]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hpb hts
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (closedComplι U z)).map (closedComplUnit U F).hom)
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (closedComplι U)
        (sheafify (Opens.grothendieckTopology (closedCompl U)) (closedComplPre U F)) z) hsp hcomp

/-- At a point of `U`, the stalk of `i_*i^{-1}F` is zero (Stacks 00AE). -/
theorem isZero_stalk_closedComplPush_of_mem (x : X) (hx : x ∈ U) :
    IsZero (TopCat.Presheaf.stalk (closedComplPush U F).obj x) :=
  TopCat.Sheaf.isZero_stalk_pushforward_of_notMem_range (closedComplι U)
    (closedComplι_isClosedEmbedding U) _ x (notMem_range_closedComplι U hx)

/-- Over an open `V ≤ U`, the sections of `i_*i^{-1}F` vanish (`i⁻¹V = ∅`). -/
theorem isZero_closedComplPush_obj_of_le {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    IsZero ((closedComplPush U F).obj.obj V) := by
  have hbot : (Opens.map (closedComplι U)).obj V.unop = ⊥ := by
    ext z
    exact ⟨fun hz => (z.2 (hV hz)).elim, fun h => h.elim⟩
  exact (TopCat.Sheaf.isTerminalOfEqEmpty
    ((presheafToSheaf (Opens.grothendieckTopology (closedCompl U)) AddCommGrpCat.{u}).obj
      (closedComplPre U F)) hbot).isZero

/-- `P ⟶ F ⟶ i_*i^{-1}F` is zero at the presheaf level: over `V ≤ U` the target vanishes, over `V ⊄ U`
the source vanishes. -/
theorem extendByZeroCounitPresheaf_comp_closedComplUnit_hom :
    extendByZeroCounitPresheaf U F ≫ (closedComplUnit U F).hom = 0 := by
  apply NatTrans.ext
  funext V
  rw [NatTrans.comp_app, NatTrans.app_zero]
  by_cases hV : V.unop ≤ U
  · exact (isZero_closedComplPush_obj_of_le U F hV).eq_zero_of_tgt _
  · exact (isZero_extendByZeroPresheaf_obj_of_not_le U _ hV).eq_zero_of_src _

/-- `j_!j^*F ⟶ F ⟶ i_*i^{-1}F` is zero. -/
theorem extendByZeroCounit_comp_closedComplUnit :
    extendByZeroCounit U F ≫ closedComplUnit U F = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  change (extendByZeroCounit U F).hom ≫ (closedComplUnit U F).hom = 0
  refine CategoryTheory.sheafify_hom_ext (J := Opens.grothendieckTopology X)
    (P := extendByZeroPresheaf U (TopCat.Sheaf.restrict F U)) (Q := (closedComplPush U F).obj)
    ((extendByZeroCounit U F).hom ≫ (closedComplUnit U F).hom) 0 (closedComplPush U F).property ?_
  rw [comp_zero, ← Category.assoc, toSheafify_comp_extendByZeroCounit_hom]
  exact extendByZeroCounitPresheaf_comp_closedComplUnit_hom U F

end TopCat.Sheaf

theorem TopCat.Sheaf.shortExact_extendByZero_restrict {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (U : TopologicalSpace.Opens X) :
    ∃ S : CategoryTheory.ShortComplex
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      S.ShortExact ∧ Nonempty (S.X₂ ≅ F) ∧
      Nonempty (S.X₁ ≅ TopCat.Sheaf.extendByZero U (TopCat.Sheaf.restrict F U)) ∧
      Nonempty (S.X₃ ≅ TopCat.Sheaf.pushforwardClosed (Uᶜ : Set X) (TopCat.Sheaf.restrictClosed F (Uᶜ : Set X))) := by
  classical
  -- the short complex, in `TopCat.Sheaf Ab X` (so that Mathlib's stalk criteria apply verbatim)
  let S : CategoryTheory.ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
    CategoryTheory.ShortComplex.mk (TopCat.Sheaf.extendByZeroCounit U F)
      (TopCat.Sheaf.closedComplUnit U F) (TopCat.Sheaf.extendByZeroCounit_comp_closedComplUnit U F)
  -- stalk facts
  have hε_iso : ∀ x : X, x ∈ U → IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (TopCat.Sheaf.extendByZeroCounit U F).hom) :=
    fun x hx => TopCat.Sheaf.isIso_stalkFunctor_map_extendByZeroCounit_hom_of_mem U F x hx
  have hX₁_zero : ∀ x : X, x ∉ U → IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (TopCat.Sheaf.extendByZeroPresheaf U (TopCat.Sheaf.restrict F U))).obj) :=
    fun x hx => TopCat.Sheaf.isZero_stalk_extendByZero_of_notMem U (TopCat.Sheaf.restrict F U) x hx
  have hg_iso : ∀ x : X, x ∉ U → IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (TopCat.Sheaf.closedComplUnit U F).hom) :=
    fun x hx => TopCat.Sheaf.isIso_stalkFunctor_map_closedComplUnit_hom U F ⟨x, hx⟩
  have hX₃_zero : ∀ x : X, x ∈ U → IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (TopCat.Sheaf.closedComplPush U F).obj) :=
    fun x hx => TopCat.Sheaf.isZero_stalk_closedComplPush_of_mem U F x hx
  -- exactness on stalks
  have hexact : S.Exact := by
    refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mpr (fun x => ?_)
    by_cases hx : x ∈ U
    · have hg0 : (S.map (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).g = 0 :=
        (hX₃_zero x hx).eq_zero_of_tgt _
      refine (CategoryTheory.ShortComplex.exact_iff_epi _ hg0).mpr ?_
      exact @IsIso.epi_of_iso _ _ _ _ _ (hε_iso x hx)
    · have hf0 : (S.map (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).f = 0 :=
        (hX₁_zero x hx).eq_zero_of_src _
      refine (CategoryTheory.ShortComplex.exact_iff_mono _ hf0).mpr ?_
      exact @IsIso.mono_of_iso _ _ _ _ _ (hg_iso x hx)
  have hmono : Mono S.f := by
    refine (TopCat.Presheaf.mono_iff_stalk_mono S.f).mpr (fun x => ?_)
    by_cases hx : x ∈ U
    · exact @IsIso.mono_of_iso _ _ _ _ _ (hε_iso x hx)
    · exact ⟨fun a b _ => (hX₁_zero x hx).eq_of_tgt a b⟩
  have hepi : Epi S.g := by
    have hls : TopCat.Presheaf.IsLocallySurjective (TopCat.Sheaf.closedComplUnit U F).hom := by
      refine (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr (fun x => ?_)
      by_cases hx : x ∈ U
      · intro y
        exact ⟨0, (AddCommGrpCat.subsingleton_of_isZero (hX₃_zero x hx)).elim _ _⟩
      · exact (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ (hg_iso x hx)).2
    exact (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' _ (TopCat.Sheaf.closedComplUnit U F)).mp hls
  have hS : S.ShortExact := { exact := hexact, mono_f := hmono, epi_g := hepi }
  exact ⟨S, hS, ⟨Iso.refl F⟩,
    ⟨eqToIso (TopCat.Sheaf.extendByZero_eq_sheafify U (TopCat.Sheaf.restrict F U)).symm⟩,
    ⟨TopCat.Sheaf.closedComplPushIso U F⟩⟩

end
