import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.VanishingIdealSingletonEqPointIdeal

/-! # Base change along `Spec O_{X,x} → X` does not change stalks

For any `f : Y ⟶ X`, the second projection
`pullback.snd (X.fromSpecStalk x) f : Y ×_X Spec O_{X,x} ⟶ Y` induces a bijective stalk map at every
point. Two companion lemmas: `X.fromSpecStalk x` is flat; the pullback along `X.fromSpecStalk p` of the
vanishing ideal sheaf of a closed point `p` is the maximal ideal `𝔪_p`.

References: Stacks Project, Tag 00HT (localization is flat), Tag 01KH (a preimmersion is a topological
embedding with surjective stalk maps; stable under base change), Tag 00HR / Matsumura, Thm 7.5 (a flat
local homomorphism is faithfully flat, hence injective). In the paper, the regularity of the blowup of a
surface `S` at a point `p` uses this to replace the local rings of `Bl_p S` along the exceptional fibre
by those of `Bl_𝔪 Spec O_{S,p}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Spec O_{X,x} → X` is flat: `fromSpecStalk` is `Spec.map (germ)` (the stalk is the localization of
the ring of sections of an affine open at a prime, `IsAffineOpen.isLocalization_stalk` +
`IsLocalization.flat`) followed by the open immersion `hU.fromSpec`, and flatness is stable under
composition (Stacks Project, Tag 00HT: localization is flat). -/
theorem AlgebraicGeometry.Scheme.fromSpecStalk_flat (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    AlgebraicGeometry.Flat (X.fromSpecStalk x) := by
  have key : ∀ {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (hx : x ∈ U),
      AlgebraicGeometry.Flat (hU.fromSpecStalk hx) := by
    intro U hU hx
    have : AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map (X.presheaf.germ U x hx)) := by
      rw [AlgebraicGeometry.Flat.SpecMap_iff]
      let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
      have := hU.isLocalization_stalk ⟨x, hx⟩
      exact RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    unfold AlgebraicGeometry.IsAffineOpen.fromSpecStalk
    infer_instance
  unfold AlgebraicGeometry.Scheme.fromSpecStalk
  exact key _ _

/-- **Base change along `Spec O_{X,x} → X` does not change stalks.** For `f : Y ⟶ X` and
`y : Y ×_X Spec O_{X,x}` (written `pullback (X.fromSpecStalk x) f`), the stalk map
`O_{Y, snd y} → O_{P, y}` of the second projection `pullback.snd` at `y` is bijective.

Proof:
* **Surjectivity**: `X.fromSpecStalk x` is a preimmersion (Mathlib instance; Stacks Project, Tag 01KH);
  preimmersions are stable under base change (the `IsStableUnderBaseChange` instance of Mathlib's
  `IsPreimmersion`, giving `IsPreimmersion (pullback.snd _ _)`), and the stalk maps of a preimmersion
  are surjective (`SurjectiveOnStalks.stalkMap_surjective`).
* **Injectivity**: `X.fromSpecStalk x` is flat (`fromSpecStalk_flat`) and flatness is stable under base
  change, so `pullback.snd` is flat and the stalk map `φ : O_{Y,snd y} → O_{P,y}` is a flat ring
  homomorphism (`Flat.stalkMap`); `φ` is moreover a local homomorphism (stalk maps always are), and a
  flat local homomorphism of local rings is faithfully flat (Mathlib's
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`; Stacks Project, Tag 00HR / Matsumura 7.5), hence
  injective (`FaithfulSMul.algebraMap_injective`). -/
theorem AlgebraicGeometry.Scheme.Hom.stalkMap_pullback_snd_fromSpecStalk_bijective
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) (x : X)
    (y : ↑(CategoryTheory.Limits.pullback (X.fromSpecStalk x) f)) :
    Function.Bijective
      ((CategoryTheory.Limits.pullback.snd (X.fromSpecStalk x) f).stalkMap y).hom := by
  have : AlgebraicGeometry.Flat (X.fromSpecStalk x) := AlgebraicGeometry.Scheme.fromSpecStalk_flat X x
  refine ⟨?_, (CategoryTheory.Limits.pullback.snd (X.fromSpecStalk x) f).stalkMap_surjective y⟩
  have hfl := AlgebraicGeometry.Flat.stalkMap (CategoryTheory.Limits.pullback.snd (X.fromSpecStalk x) f) y
  let _ := ((CategoryTheory.Limits.pullback.snd (X.fromSpecStalk x) f).stalkMap y).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk ((CategoryTheory.Limits.pullback.snd (X.fromSpecStalk x) f) y))
      ((CategoryTheory.Limits.pullback (X.fromSpecStalk x) f).presheaf.stalk y) := hfl
  have : IsLocalHom (algebraMap (Y.presheaf.stalk ((CategoryTheory.Limits.pullback.snd (X.fromSpecStalk x) f) y))
      ((CategoryTheory.Limits.pullback (X.fromSpecStalk x) f).presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom ((CategoryTheory.Limits.pullback.snd (X.fromSpecStalk x) f).stalkMap y).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := Y.presheaf.stalk ((CategoryTheory.Limits.pullback.snd (X.fromSpecStalk x) f) y))
    (B := (CategoryTheory.Limits.pullback (X.fromSpecStalk x) f).presheaf.stalk y)
  exact FaithfulSMul.algebraMap_injective _ _


/-- The pullback along `Spec O_{X,p} → X` of the vanishing ideal sheaf of a closed point `p` is the ideal
sheaf given by the maximal ideal `𝔪_p` (transported to `Γ(Spec O_{X,p})` via `ΓSpecIso`) — the centre
needed for the blowup of `Spec O_{X,p}` at its closed point. This holds for an arbitrary scheme `X`.

Proof: `vanishingIdeal {p} = (fromSpecResidueField p).ker` (`vanishingIdeal_singleton_eq_pointIdeal`);
`fromSpecResidueField p = Spec.map (residue p) ≫ fromSpecStalk p`, and `fromSpecStalk p` is a monomorphism
(a preimmersion), so `pullback (fromSpecStalk p) (fromSpecResidueField p)` is `Spec κ(p)` with
`fst = Spec.map (residue p)` (`IsKernelPair.id_of_mono` and `IsPullback.paste_horiz`); by
`ker_fst_of_isClosedImmersion` (`p` closed ⇒ `fromSpecResidueField p` is a closed immersion) the comap is
`(Spec.map (residue p)).ker = ofIdealTop (ker appTop)` (`ker_of_isAffine`); finally
`ΓSpecIso_naturality` and `IsLocalRing.residue_eq_zero_iff` identify this kernel with the image of `𝔪_p`
under `ΓSpecIso.inv`. -/
theorem AlgebraicGeometry.Scheme.vanishingIdeal_singleton_comap_fromSpecStalk
    {X : AlgebraicGeometry.Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X)) :
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap (X.fromSpecStalk p) =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk p)).map
          (AlgebraicGeometry.Scheme.ΓSpecIso (X.presheaf.stalk p)).inv.hom) := by
  rw [AlgebraicGeometry.Scheme.vanishingIdeal_singleton_eq_pointIdeal p hp]
  unfold MiyaokaMori.Statement.pointIdeal
  have : AlgebraicGeometry.IsClosedImmersion (X.fromSpecResidueField p) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hp
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hpb : IsPullback (AlgebraicGeometry.Spec.map (X.residue p)) (𝟙 _)
      (X.fromSpecStalk p) (X.fromSpecResidueField p) := by
    have h1 : IsPullback (AlgebraicGeometry.Spec.map (X.residue p)) (𝟙 _) (𝟙 _)
        (AlgebraicGeometry.Spec.map (X.residue p)) :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have h2 := IsKernelPair.id_of_mono (X.fromSpecStalk p)
    have := h1.paste_horiz h2
    simpa [AlgebraicGeometry.Scheme.fromSpecResidueField] using this
  rw [← AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom, hpb.isoPullback_hom_fst,
    AlgebraicGeometry.Scheme.ker_of_isAffine]
  congr 1
  ext x
  have hnat := congrArg (fun f => f.hom x)
    (AlgebraicGeometry.Scheme.ΓSpecIso_naturality (X.residue p))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  have hmap : (IsLocalRing.maximalIdeal (X.presheaf.stalk p)).map
      (AlgebraicGeometry.Scheme.ΓSpecIso (X.presheaf.stalk p)).inv.hom =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk p)).comap
      (AlgebraicGeometry.Scheme.ΓSpecIso (X.presheaf.stalk p)).hom.hom :=
    Ideal.map_symm (AlgebraicGeometry.Scheme.ΓSpecIso
      (X.presheaf.stalk p)).commRingCatIsoToRingEquiv
  have hinj : Function.Injective
      (AlgebraicGeometry.Scheme.ΓSpecIso (X.residueField p)).hom.hom :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (X.residueField p)).commRingCatIsoToRingEquiv.injective
  rw [hmap, Ideal.mem_comap, RingHom.mem_ker, ← IsLocalRing.residue_eq_zero_iff,
    ← map_eq_zero_iff _ hinj, hnat]
  rfl

end
