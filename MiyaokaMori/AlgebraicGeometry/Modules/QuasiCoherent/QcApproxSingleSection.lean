import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcApproxGoodOn
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcApproxSpanSubpresheaf
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcApproxExtendAffine
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcApproxGlue

/-! # Finite type approximation of one section (Stacks 01PD–01PE)

Support module for `QcFiniteTypeApproxFiniteSections`.

`S` quasi-compact quasi-separated, `F` quasi-coherent, `V` affine open, `s ∈ Γ(F, V)`. Then there is a
finite type quasi-coherent module `E` with `φ : E ⟶ F` and `e ∈ Γ(E, V)` with `φ(e) = s`
(`exists_isFiniteType_hom_of_affine_section`). In fact `E ⊆ F` is a submodule with `s ∈ E(V)`.

Proof (`exists_goodOn_top`). Write `S = ⋃_{W ∈ T} W` with `T` a finite set of affine opens
(`isCompact_iff_finite_and_eq_biUnion_affineOpens`). By induction on `T' ⊆ T` produce a quasi-compact open
`U ⊇ V ∪ ⋃_{W ∈ T'} W` and a sub-presheaf `G` good on `U` (`QcApprox.GoodOn`) with `s ∈ G(V)`:
* start: `U := V`, `G := spanSub F V (fun _ => s)` (good on `V` by `goodOn_spanSub`; `s ∈ G(V)`);
* step `T' → insert W T'`: `GoodOn.exists_spanSub_agree` gives a good sub-presheaf on `W` agreeing with `G`
  on `U ⊓ W`; `GoodOn.glue` glues them to a good sub-presheaf on `U ⊔ W`, which still contains `s` over
  `V` (`glue_obj_eq_left`).
At the end `U = ⊤`, and `toModules` turns `G` into the quasi-coherent finite type module `E`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.QcApprox

variable {S : AlgebraicGeometry.Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent]

/-- The induction (Stacks 01PD): for every finite set `T'` of affine opens there are a quasi-compact open
`U ⊇ V ∪ ⋃ T'` and a sub-presheaf good on `U` containing `s` over `V`. -/
theorem exists_goodOn_of_finset [QuasiSeparatedSpace S] {V : S.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (s : Γ(F, V)) (T' : Finset S.affineOpens) :
    ∃ (U : S.Opens) (G : F.val.Submodule), (∀ W ∈ T', (W : S.Opens) ≤ U) ∧ V ≤ U ∧
      IsCompact (U : Set S) ∧ GoodOn F G U ∧ s ∈ objΓ G V := by
  classical
  induction T' using Finset.induction_on with
  | empty =>
    refine ⟨V, spanSub F V (fun _ : Fin 1 => s), fun W hW => absurd hW (Finset.notMem_empty W), le_rfl,
      hV.isCompact, goodOn_spanSub F hV _, ?_⟩
    rw [mem_spanSub_iff_mem_span F _ hV le_rfl]
    exact Submodule.subset_span ⟨0, map_self _ _⟩
  | insert W T' hW ih =>
    obtain ⟨U, G, hle, hVU, hUc, hG, hs⟩ := ih
    obtain ⟨ι, _, e, hagree⟩ := hG.exists_spanSub_agree hUc W.2
    refine ⟨U ⊔ W, glue F G (spanSub F (W : S.Opens) e) U W, ?_, hVU.trans le_sup_left, ?_,
      hG.glue (goodOn_spanSub F W.2 e) hUc W.2.isCompact hagree, ?_⟩
    · intro W' hW'
      rcases Finset.mem_insert.mp hW' with rfl | hW'
      · exact le_sup_right
      · exact (hle W' hW').trans le_sup_left
    · rw [Opens.coe_sup]
      exact hUc.union W.2.isCompact
    · rw [glue_obj_eq_left hagree hVU]
      exact hs

/-- **Stacks 01PD–01PE for one section, sub-presheaf form**: on a qcqs scheme there is a sub-presheaf of `F`
good on `⊤` (a finite type quasi-coherent submodule) containing the given section `s ∈ Γ(F, V)`. -/
theorem exists_goodOn_top [CompactSpace S] [QuasiSeparatedSpace S] {V : S.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (s : Γ(F, V)) :
    ∃ G : F.val.Submodule, GoodOn F G ⊤ ∧ s ∈ objΓ G V := by
  classical
  have htop : IsCompact ((⊤ : S.Opens) : Set S) := by
    rw [Opens.coe_top]
    exact isCompact_univ
  obtain ⟨T, hTfin, hTtop⟩ :=
    (AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : S.Opens))).mp htop
  obtain ⟨U, G, hle, -, -, hG, hs⟩ := exists_goodOn_of_finset F hV s hTfin.toFinset
  have hU : U = ⊤ := by
    apply top_le_iff.mp
    rw [hTtop]
    exact iSup₂_le fun W hW => hle W (hTfin.mem_toFinset.mpr hW)
  exact ⟨G, hG.mono hU.ge, hs⟩

/-- **Finite type approximation of one affine section** (Stacks 01PD–01PE): `S` qcqs, `F` quasi-coherent,
`V` affine, `s ∈ Γ(F, V)`. There are a finite type quasi-coherent `E`, `φ : E ⟶ F` and `e ∈ Γ(E, V)` with
`φ(e) = s`. (`E` is the submodule `toModules G hG` of `F`, `φ` its inclusion, `e = s`.) -/
theorem exists_isFiniteType_hom_of_affine_section [CompactSpace S] [QuasiSeparatedSpace S]
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) (s : Γ(F, V)) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType) (φ : E ⟶ F) (e : Γ(E, V)),
      (φ.val.app (Opposite.op V)).hom e = s := by
  obtain ⟨G, hG, hs⟩ := exists_goodOn_top F hV s
  exact ⟨toModules G hG, toModules_isQuasicoherent G hG, toModules_isFiniteType G hG,
    toModules.ι G hG, ⟨s, hs⟩, rfl⟩

end AlgebraicGeometry.Scheme.Modules.QcApprox

end
