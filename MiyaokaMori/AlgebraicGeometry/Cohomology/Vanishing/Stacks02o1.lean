import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.FlatFamilyRestrictAffineBase
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tNoetherian
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyVanishingLocalOnBase

/-! # Relative Serre vanishing (Stacks 02O1)

Stacks 02O1 (relative Serre vanishing): `S` Noetherian, `f` proper, `F` coherent, `L` relatively ample for
`f` ⇒ there is `n₀` such that `R^p f_*(F ⊗ L^{⊗n}) = 0` for `n ≥ n₀`, `p > 0`; stated in affine-local form:
for every affine open `V` of `S`, `H^p(f⁻¹V, F ⊗ L^{⊗n}) = 0`.

Source: Stacks 02O1 (coherent-lemma-kill-by-twisting).

The proof is assembled from two ingredients:
* `sheafCohomology_tensor_pow_subsingleton_of_isAmple_of_isProper_over_noetherianRing`
  (`Stacks0b5tNoetherian.lean`): Stacks 0B5T(4) over a Noetherian ring — the absolute vanishing on each
  `f⁻¹V → Spec Γ(S, V)`;
* `sheafCohomology_restrict_preimage_subsingleton_of_forall_exists_affineOpen`
  (`SheafCohomologyVanishingLocalOnBase.lean`): Stacks 01XJ/01XK — vanishing of `H^p(f⁻¹V, G)` is local on
  the base, which makes the bound `n₀` found on a finite affine cover of the Noetherian (hence
  quasi-compact) `S` valid for every affine open `V`.
Everything else (restriction to `f⁻¹V` as a proper morphism to `Spec Γ(S, V)`, coherence and
line-bundle instances of the pullbacks, the isomorphism `(F ⊗ L^{⊗n})|_{f⁻¹V} ≅ F|_{f⁻¹V} ⊗ (L|_{f⁻¹V})^{⊗n}`,
transport of `Subsingleton` along it, and the finite subcover) is proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Sheaf cohomology of isomorphic modules: `Subsingleton` transports along an isomorphism of
`X.Modules` (the maps `Sheaf.H.map e.hom`, `Sheaf.H.map e.inv` are mutually inverse). -/
private theorem subsingleton_sheafH_of_iso_stacks02o1 {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) (p : ℕ)
    [hN : Subsingleton (CategoryTheory.Sheaf.H N.toAddCommGrpSheaf p)] :
    Subsingleton (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p) := by
  refine ⟨fun x y => ?_⟩
  have hc : (SheafOfModules.toSheaf X.ringCatSheaf).map e.hom ≫
      (SheafOfModules.toSheaf X.ringCatSheaf).map e.inv = 𝟙 _ :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).map_comp e.hom e.inv).symm.trans
      ((congrArg (SheafOfModules.toSheaf X.ringCatSheaf).map e.hom_inv_id).trans
        ((SheafOfModules.toSheaf X.ringCatSheaf).map_id M))
  have hround : ∀ z : CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p,
      z = Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) p
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) p z) := by
    intro z
    have h := Sheaf.H.map_comp_apply ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) z
    rw [hc] at h
    exact (Sheaf.H.map_id_apply z).symm.trans h
  rw [hround x, hround y,
    Subsingleton.elim (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) p x)
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) p y)]

/-- Functoriality of `Modules.tensor` in the second variable along an isomorphism (sheafification of
the presheaf-level left whiskering). Same construction as `tensorIsoRight` in
`ModuleTensorPowerIsoTensorPow.lean`, copied here because that module's import closure passes through
`Stacks02o6 → Stacks02o5 → Stacks02o1` (an import cycle). -/
private def tensorIsoRight_stacks02o1 {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    {N N' : X.Modules} (e : N ≅ N') :
    AlgebraicGeometry.Scheme.Modules.tensor M N ≅ AlgebraicGeometry.Scheme.Modules.tensor M N' :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.whiskerLeftIso M.val ((SheafOfModules.forget X.ringCatSheaf).mapIso e))

end AlgebraicGeometry.Scheme.Modules

/-- Stacks 02O1 (relative Serre vanishing): `S` Noetherian, `f` proper, `F` coherent, `L` relatively ample
for `f` (for every affine open `V` of `S`, `L|_{f⁻¹V}` is ample, as in the definition of quasi-projective
morphisms). Then there is `n₀` such that `R^p f_*(F ⊗ L^{⊗n}) = 0` for `n ≥ n₀`, `p > 0`; stated here in the
equivalent affine-local form: for every affine open `V` of `S`, `H^p(f⁻¹V, F ⊗ L^{⊗n}) = 0` (Stacks 01XK:
for `f` qcqs and `V` affine, `H^p(f⁻¹V, G) = Γ(V, R^p f_*G)` with `R^p f_*G` quasi-coherent). -/

theorem AlgebraicGeometry.higherDirectImage_tensorPow_vanish_of_relativelyAmple
    {X S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [AlgebraicGeometry.IsProper f]
    (F : X.Modules) [F.IsCoherent] (L : X.Modules) [L.IsLineBundle]
    (hL : ∀ V : S.affineOpens,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (V : S.affineOpens) (p : ℕ), 0 < p →
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict
          (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L n))
          (f ⁻¹ᵁ V.1).ι).toAddCommGrpSheaf p) := by
  classical
  -- Step 1 (Stacks 0B5T(4) on each affine open): a bound `n₀(V)` for every affine open `V ⊆ S`.
  have key : ∀ V : S.affineOpens, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℕ, 0 < p →
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict
          (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L n))
          (f ⁻¹ᵁ V.1).ι).toAddCommGrpSheaf p) := by
    intro V
    haveI : IsNoetherianRing Γ(S, V.1) := IsLocallyNoetherian.component_noetherian V
    -- `f⁻¹V → V ≅ Spec Γ(S, V)` is proper (base change of `f`, then an isomorphism).
    let g : (f ⁻¹ᵁ V.1).toScheme ⟶ AlgebraicGeometry.Spec Γ(S, V.1) := (f ∣_ V.1) ≫ V.2.isoSpec.hom
    haveI : AlgebraicGeometry.IsProper g :=
      (MorphismProperty.cancel_right_of_respectsIso @AlgebraicGeometry.IsProper (f ∣_ V.1)
        V.2.isoSpec.hom).mpr inferInstance
    haveI : ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj F).IsCoherent :=
      AlgebraicGeometry.Scheme.Modules.isCoherent_pullback _ F
    obtain ⟨n₀, hn₀⟩ :=
      AlgebraicGeometry.sheafCohomology_tensor_pow_subsingleton_of_isAmple_of_isProper_over_noetherianRing g
        ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L) (hL V)
        ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj F)
    refine ⟨n₀, fun n hn p hp => ?_⟩
    haveI := hn₀ n hn p hp
    -- `(F ⊗ L^{⊗n})|_{f⁻¹V} ≅ F|_{f⁻¹V} ⊗ (L|_{f⁻¹V})^{⊗n}`.
    let e : AlgebraicGeometry.Scheme.Modules.restrict
          (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L n))
          (f ⁻¹ᵁ V.1).ι ≅
        AlgebraicGeometry.Scheme.Modules.tensor
          ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj F)
          (AlgebraicGeometry.Scheme.Modules.tensorPow
            ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L) n) :=
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V.1).ι).app _ ≪≫
        AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (f ⁻¹ᵁ V.1).ι F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n) ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorIsoRight_stacks02o1 _
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso (f ⁻¹ᵁ V.1).ι L n)
    exact AlgebraicGeometry.Scheme.Modules.subsingleton_sheafH_of_iso_stacks02o1 e p
  choose nV hnV using key
  -- Step 2: `S` is Noetherian, hence quasi-compact; finitely many affine opens cover it.
  have hcov : (Set.univ : Set S) ⊆ ⋃ V : S.affineOpens, (V.1 : Set S) := by
    intro s _
    obtain ⟨V, hV, hs, -⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show s ∈ (⊤ : S.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hs⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : S.affineOpens => (V.1 : Set S))
    (fun V => V.1.isOpen) hcov
  refine ⟨t.sup nV, fun n hn V p hp => ?_⟩
  -- Step 3 (Stacks 01XJ/01XK): vanishing near every point of `S` gives vanishing on every affine `V`.
  haveI : F.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  haveI : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).IsLineBundle := inferInstance
  haveI : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).IsLocallyFree := inferInstance
  haveI : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
  haveI : (AlgebraicGeometry.Scheme.Modules.tensor F
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n)).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensor F _
  exact AlgebraicGeometry.sheafCohomology_restrict_preimage_subsingleton_of_forall_exists_affineOpen f
    (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L n)) p
    (fun s => by
      obtain ⟨W, hWt, hsW⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ s))
      exact ⟨W, hsW, hnV W n (le_trans (Finset.le_sup hWt) hn) p hp⟩) V

end
