import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ModulesGlueOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleChartPullback
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousTupleLocalCoordinates
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveCoordinateRatio
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleFrameChange
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleRestriction
-- ^ These imports are not used in this file; they are kept for downstream modules that reach
-- them through it.

/-! # Gluing module isomorphisms along an open cover

Variable-level lemma (no concrete scheme appears): if `U : ι → X.Opens` covers `X`, and for every
`i` and every open `V ≤ U i` we are given an isomorphism `e i V : P|_V ≅ Q|_V` such that
(1) the family is compatible with restriction to smaller opens (`restrictIsoOfLE`) and
(2) two pieces agree on any common open, then `P ≅ Q`.

Source: Stacks 04TN (gluing morphisms of sheaves), 01LI; the gluing itself is
`Scheme.Modules.exists_hom_of_restrict_compat` (`ModulesGlueOpenImmersion.lean`),
`IsIso` comes from `isIso_of_restrict_isIso_cover` (stalks). The restriction comparison
`restrictIsoOfLE` (`AlgebraicGeometry/Modules/Pullback/ModuleChartPullback.lean`, namespace
`AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistRestriction`) uses `restrictFunctorCongr ≪≫ restrictFunctorComp`
exactly like `restrictCompIso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistRestriction (restrictIsoOfLE nestedRestrictionIso)

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `nestedRestrictionIso` is the `restrictCompIso` of the transition `homOfLE`. -/
theorem nestedRestrictionIso_hom_eq (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    (nestedRestrictionIso M h).hom =
      (restrictCompIso (X.homOfLE h) V.ι U.ι (X.homOfLE_ι h)).hom.app M := by
  apply hom_ext
  intro A
  rw [restrictCompIso_hom_app_app]
  simp only [nestedRestrictionIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Hom.comp_app,
    restrictFunctorCongr_inv_app_app]
  exact glueAux_map2 M.presheaf _ _ _

/-- Inverse version of `nestedRestrictionIso_hom_eq`. -/
theorem nestedRestrictionIso_inv_eq (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    (nestedRestrictionIso M h).inv =
      (restrictCompIso (X.homOfLE h) V.ι U.ι (X.homOfLE_ι h)).inv.app M := by
  apply hom_ext
  intro A
  rw [restrictCompIso_inv_app_app]
  simp only [nestedRestrictionIso, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Hom.comp_app,
    restrictFunctorCongr_hom_app_app]
  exact glueAux_map2 M.presheaf _ _ _

/-- **Gluing isomorphisms of modules along an open cover.** Given `U : ι → X.Opens` covering `X`
and, for every `i` and every open `V ≤ U i`, an isomorphism `e i V : P|_V ≅ Q|_V`, such that
the family is compatible with restriction (`hres`) and any two pieces agree on a common open
(`hagree`), the modules `P` and `Q` are isomorphic. -/
theorem exists_iso_of_local_isos {ι : Type u} (U : ι → X.Opens)
    (hcov : ∀ x : X, ∃ i, x ∈ U i) (P Q : X.Modules)
    (e : ∀ (i : ι) (V : X.Opens), V ≤ U i → (P.restrict V.ι ≅ Q.restrict V.ι))
    (hres : ∀ (i : ι) (V V' : X.Opens) (hVV' : V ≤ V') (hV' : V' ≤ U i),
      restrictIsoOfLE hVV' (e i V' hV') = e i V (hVV'.trans hV'))
    (hagree : ∀ (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j), e i V hi = e j V hj) :
    Nonempty (P ≅ Q) := by
  -- index the pieces by pairs (i, V) with V ≤ U i
  let κ := { p : ι × X.Opens // p.2 ≤ U p.1 }
  let Y : κ → AlgebraicGeometry.Scheme.{u} := fun p => p.1.2.toScheme
  let f : ∀ p : κ, Y p ⟶ X := fun p => p.1.2.ι
  have hcov' : ∀ x : X, ∃ p : κ, x ∈ (f p).opensRange := by
    intro x
    obtain ⟨i, hi⟩ := hcov x
    refine ⟨⟨(i, U i), le_rfl⟩, ?_⟩
    rw [Opens.opensRange_ι]
    exact hi
  let ρ : ∀ p : κ, P.restrict (f p) ⟶ Q.restrict (f p) := fun p => (e p.1.1 p.1.2 p.2).hom
  -- the section map of a piece `p` on a smaller open `V` is the section map of the piece `(p.1, V)`
  have hsec : ∀ (p : κ) (V : X.Opens) (hV : V ≤ p.1.2),
      sectionMapOI (f p) (ρ p) V (by rw [Opens.opensRange_ι]; exact hV) =
        sectionMapOI (f ⟨(p.1.1, V), hV.trans p.2⟩) (ρ ⟨(p.1.1, V), hV.trans p.2⟩) V
          (by rw [Opens.opensRange_ι]) := by
    intro p V hV
    refine (sectionMapOI_eq_of_transition (X.homOfLE hV) (f p) (f ⟨(p.1.1, V), hV.trans p.2⟩)
      (X.homOfLE_ι hV) (ρ p) (ρ ⟨(p.1.1, V), hV.trans p.2⟩) ?_ V (by rw [Opens.opensRange_ι])).symm
    intro A
    have h1 := hres p.1.1 V p.1.2 hV p.2
    show (e p.1.1 V (hV.trans p.2)).hom.app A = _
    rw [← h1]
    simp only [restrictIsoOfLE, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [nestedRestrictionIso_hom_eq, nestedRestrictionIso_inv_eq, Hom.comp_app, Hom.comp_app,
      restrictCompIso_hom_app_app, restrictCompIso_inv_app_app]
    rfl
  have hagree' : ∀ (p q : κ) (V : X.Opens) (hp : V ≤ (f p).opensRange)
      (hq : V ≤ (f q).opensRange),
      sectionMapOI (f p) (ρ p) V hp = sectionMapOI (f q) (ρ q) V hq := by
    intro p q V hp hq
    have hp' : V ≤ p.1.2 := by rw [Opens.opensRange_ι] at hp; exact hp
    have hq' : V ≤ q.1.2 := by rw [Opens.opensRange_ι] at hq; exact hq
    rw [hsec p V hp', hsec q V hq']
    have : ρ ⟨(p.1.1, V), hp'.trans p.2⟩ = ρ ⟨(q.1.1, V), hq'.trans q.2⟩ := by
      show (e p.1.1 V _).hom = (e q.1.1 V _).hom
      rw [hagree p.1.1 q.1.1 V (hp'.trans p.2) (hq'.trans q.2)]
    simp only [this]
    rfl
  obtain ⟨G, hG⟩ := exists_hom_of_sectionMapOI_agree Y f hcov' P Q ρ hagree'
  have hGp : ∀ p : κ, (restrictFunctor (f p)).map G = ρ p := fun p =>
    restrict_map_eq_of_app_eq_sectionMapOI (f p) G (ρ p) (hG p)
  have : IsIso G := by
    refine isIso_of_restrict_isIso_cover Y f hcov' G ?_
    intro p
    rw [hGp p]
    exact Iso.isIso_hom _
  exact ⟨asIso G⟩

end AlgebraicGeometry.Scheme.Modules

end
