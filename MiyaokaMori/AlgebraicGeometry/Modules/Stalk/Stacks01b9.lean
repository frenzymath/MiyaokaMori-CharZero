import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan

/-! # Vanishing of a finite type module near a point where its stalk vanishes (Stacks 01B9)

A sheaf of modules of finite type whose stalk at a point vanishes is zero on a neighbourhood of
that point (Stacks 01B9).

Proof (Stacks 01B9):
1. `exists_epi_free_pullback_of_isFiniteType` gives an open `U ∋ x`, a finite `J` and an epi
   `π : O_U^{⊕J} ⟶ (U.ι)^*M`; composing with `restrictFunctorIsoPullback` gives an epi
   `π' : O_U^{⊕J} ⟶ N := M.restrict U.ι` on `Y := U`.
2. Stalks of `N` at `z : U` are in bijection with stalks of `M` at `z.1`
   (`Scheme.Modules.restrictStalkNatIso`), so `N_y = 0` at `y = ⟨x, hxU⟩`.
3. Let `t_j := π'(e_j) ∈ Γ(N, ⊤)`. Its germ at `y` is `0`, so by `TopCat.Presheaf.germ_eq`
   there is an open `W_j ∋ y` with `t_j|_{W_j} = 0`. Put `V := ⋂_j W_j` (finite intersection).
4. For `z ∈ V`, the stalk map `(π')_z` is surjective (`FreeStalk.stalkMap_surjective_of_epi`),
   the free stalk is spanned by the germs `b_j` (`FreeStalk.span_b_eq_top`), and
   `(π')_z(b_j) = germ_z(t_j) = germ_z(t_j|_{W_j}) = 0`; hence `N_z = 0`, hence `M_{z} = 0`
   for every `z` in the open `O := U.ι(V) ⊆ X`.
5. `IsZero (M.restrict O.ι)` iff `𝟙 = 0`; by hom-extensionality this says every section of `M`
   over an open `W ⊆ O` vanishes, which follows from `TopCat.Sheaf.section_ext` since all germs
   over `W` lie in zero stalks.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- Stalks of `M.restrict g` at `z` and of `M` at `g z` are in bijection, so one is a
singleton iff the other is. -/
private theorem Stacks01b9.subsingleton_restrict_stalk_iff {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (M : X.Modules) (z : Y) :
    Subsingleton ((M.restrict g).presheaf.stalk z) ↔ Subsingleton (M.presheaf.stalk (g z)) := by
  let e : (M.restrict g).presheaf.stalk z ≃ M.presheaf.stalk (g z) :=
    ((forget Ab).mapIso ((Scheme.Modules.restrictStalkNatIso g z).app M)).toEquiv
  exact ⟨fun _ => e.symm.subsingleton, fun _ => e.subsingleton⟩

/-- Stacks 01B9: if the stalk of a finite type module `M` at `x` vanishes, then `M` is zero on an
open neighbourhood of `x`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_open_isZero_of_stalk {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsFiniteType] (x : X)
    (hx : Subsingleton (M.stalk x)) :
    ∃ U : X.Opens, x ∈ U ∧ CategoryTheory.Limits.IsZero (M.restrict U.ι) := by
  obtain ⟨U, J, hJ, π, hxU, hπ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType M x
  have := Fintype.ofFinite J
  let N : U.toScheme.Modules := M.restrict U.ι
  let π' : MiyaokaMori.FreeStalk.freeM U.toScheme J ⟶ N :=
    π ≫ ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).inv
  have hπ' : Epi π' := @epi_comp _ _ _ _ _ π hπ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))
  let y : U := ⟨x, hxU⟩
  have hx' : Subsingleton (M.presheaf.stalk x) := hx
  have hy : Subsingleton (N.presheaf.stalk y) :=
    (Stacks01b9.subsingleton_restrict_stalk_iff U.ι M y).mpr hx'
  -- the generating sections and their vanishing neighbourhoods
  let t : J → Γ(N, ⊤) := fun j => π'.app ⊤ (MiyaokaMori.FreeStalk.e J j ⊤)
  have ht : ∀ j, N.presheaf.germ ⊤ y (Opens.mem_top y) (t j) =
      N.presheaf.germ ⊤ y (Opens.mem_top y) 0 :=
    fun j => Subsingleton.elim _ _
  choose W hyW iW _ hW using
    fun j => N.presheaf.germ_eq y (Opens.mem_top y) (Opens.mem_top y) (t j) 0 (ht j)
  let V : U.toScheme.Opens := ⟨⋂ j, (W j : Set U.toScheme), isOpen_iInter_of_finite fun j => (W j).isOpen⟩
  have hyV : y ∈ V := Set.mem_iInter.mpr hyW
  -- stalks of `N` vanish on `V`
  have hV : ∀ z ∈ V, Subsingleton (N.presheaf.stalk z) := by
    intro z hz
    have hz' : ∀ j, z ∈ W j := Set.mem_iInter.mp hz
    let G := AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme z π'
    have hG : ∀ j, G (MiyaokaMori.FreeStalk.b J j z) = 0 := by
      intro j
      have h1 : N.presheaf.germ ⊤ z ((iW j).le (hz' j)) (t j) = 0 := by
        have h2 := N.presheaf.germ_res_apply (iW j) z (hz' j) (t j)
        rw [hW j, map_zero, map_zero] at h2
        exact h2.symm
      show AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme z π' (MiyaokaMori.FreeStalk.b J j z) = 0
      rw [← MiyaokaMori.FreeStalk.germ_e J j z ⊤ (Opens.mem_top z), AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ]
      exact h1
    have hker : ⊤ ≤ LinearMap.ker G := by
      rw [← MiyaokaMori.FreeStalk.span_b_eq_top J z]
      exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hG j)
    have hsurj := MiyaokaMori.FreeStalk.stalkMap_surjective_of_epi π' z
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨b, rfl⟩ := hsurj b
    rw [LinearMap.mem_ker.mp (hker (Submodule.mem_top : a ∈ ⊤)),
      LinearMap.mem_ker.mp (hker (Submodule.mem_top : b ∈ ⊤))]
  -- the open of `X`
  refine ⟨U.ι ''ᵁ V, ⟨y, hyV, rfl⟩, ?_⟩
  have hMV : ∀ z ∈ U.ι ''ᵁ V, Subsingleton (M.presheaf.stalk z) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Stacks01b9.subsingleton_restrict_stalk_iff U.ι M z).mp (hV z hz)
  rw [IsZero.iff_id_eq_zero]
  ext K s
  have hle : (U.ι ''ᵁ V).ι ''ᵁ K ≤ U.ι ''ᵁ V := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  change s = 0
  exact TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ((U.ι ''ᵁ V).ι ''ᵁ K) s 0
    (fun z hz => @Subsingleton.elim _ (hMV z (hle hz)) _ _)

end
