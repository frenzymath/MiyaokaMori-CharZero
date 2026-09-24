import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyFinrankOfSchemeIso

/-! # Fibre cohomology and base change over an affine open

Fibre cohomology matches base change over an affine base: if `V ⊆ T` is an affine open, `V ≅ Spec A`, and
`t ∈ V` corresponds to the prime `p`, then the scheme-theoretic fibre of `f` at `t` (with the pulled-back
module) is isomorphic to the base change of `f⁻¹(V) → Spec A` along `A → κ(p)`, so the `κ(t)`- and
`κ(p)`-dimensions of the cohomology groups agree in every degree.

Proof (all constructions explicit):
1. The residue field isomorphism `κ(t) ≅ κ(p)` (`affineOpenResidueFieldIso`): `t = fromSpec p`
   (`fromSpec_primeIdealOf`), the residue field map of the open immersion `fromSpec : Spec A → T` at `p` is
   an isomorphism (Mathlib), followed by `Spec.residueFieldIso`; it is compatible with the two "residue
   field points": `Spec κ(t) → Spec κ(p) → Spec A → T` equals `T.fromSpecResidueField t`
   (`SpecMap_affineOpenResidueFieldIso_inv_fromSpec`).
2. Pasting of pullback squares (`isPullback_fiber_affine_baseChange`): `f⁻¹V → Spec A` is the base change
   of `f` along `fromSpec` (`isPullback_morphismRestrict` pasted vertically with an isomorphism square),
   then pasted horizontally with the square of `pullback fV g`, and finally the base point `Spec κ(p)` is
   replaced by `Spec κ(t)` using step 1; hence `pullback fV g` and `f.fiber t` are pullbacks of the same
   cospan, `isoIsPullback` gives a scheme isomorphism `e` with `e ≫ fst ≫ ι = fiberι` and
   `e ≫ snd ≫ Spec σ = fiberToSpecResidueField`.
3. Modules: `(fiberι)^* M ≅ e^*((fst ≫ ι)^* M)` (`pullbackCongr` + `pullbackComp`); dimensions are
   invariant under isomorphisms of modules.
4. Dimensions: `sheafCohomology_finrank_eq_of_schemeIso'` (invariance of cohomology dimensions under a
   scheme isomorphism together with a base isomorphism `σ`, from Stacks 02UV for the isomorphism `e.inv`
   and `pushforwardInvIsoPullback`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- the `letI` in the proofs must stay inline (the instances in the statements are `letI`, which unfold to
-- these terms); they cannot be replaced by `let`
set_option linter.style.haveILetI false
-- as in Mathlib's `ResidueField.lean` / `Fiber.lean`: unifying `x : Spec R` with `x : PrimeSpectrum R` needs
-- more transparency at the type level
set_option backward.isDefEq.respectTransparency.types false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {T : Scheme.{u}}

/-- On an affine open `U ≅ Spec A`, the canonical isomorphism between the residue fields of a point
`x : Spec A` and of its image `t = fromSpec x` in `T`: `κ(t) = κ(fromSpec x) ≅ κ_{Spec A}(x) ≅ κ(x)` (first
`residueFieldCongr`, then the residue field map of the open immersion `fromSpec` is an isomorphism, then
`Spec.residueFieldIso`). With `x = primeIdealOf t` this gives `κ(t) ≅ κ(p)`. -/
def affineOpenResidueFieldIso (U : T.Opens) (hU : IsAffineOpen U) (x : Spec Γ(T, U)) (t : T)
    (h : hU.fromSpec x = t) :
    T.residueField t ≅ CommRingCat.of x.asIdeal.ResidueField :=
  T.residueFieldCongr h.symm ≪≫ asIso (hU.fromSpec.residueFieldMap x) ≪≫
    Scheme.Spec.residueFieldIso Γ(T, U) x

/-- Compatibility of the residue field isomorphism with the residue field points:
`Spec κ(t) → Spec κ(x) → Spec A → T` is `T.fromSpecResidueField t`. -/
theorem SpecMap_affineOpenResidueFieldIso_inv_fromSpec (U : T.Opens) (hU : IsAffineOpen U)
    (x : Spec Γ(T, U)) (t : T) (h : hU.fromSpec x = t) :
    Spec.map (affineOpenResidueFieldIso U hU x t h).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) x.asIdeal.ResidueField)) ≫ hU.fromSpec
      = T.fromSpecResidueField t := by
  rw [affineOpenResidueFieldIso, Iso.trans_inv, Iso.trans_inv, asIso_inv, Spec.map_comp,
    Spec.map_comp]
  simp only [Category.assoc]
  rw [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField hU.fromSpec x,
    ← Spec.map_comp_assoc (hU.fromSpec.residueFieldMap x) (inv (hU.fromSpec.residueFieldMap x)),
    IsIso.hom_inv_id, Spec.map_id, Category.id_comp, Scheme.residueFieldCongr_inv,
    Scheme.residueFieldCongr_fromSpecResidueField]

/-- The pullback square: `pullback fV g` (`fV = (f ∣_ U) ≫ hU.isoSpec.hom`, `g = Spec (A → κ(x))`) with
`fst ≫ ι` and `snd ≫ Spec σ` is the pullback of `f` along `T.fromSpecResidueField t`, i.e. it has the same
cospan as `f.fiber t`. -/
theorem isPullback_fiber_affine_baseChange {Y : Scheme.{u}} (f : Y ⟶ T) (U : T.Opens)
    (hU : IsAffineOpen U) (x : Spec Γ(T, U)) (t : T) (h : hU.fromSpec x = t) :
    IsPullback
      (pullback.fst ((f ∣_ U) ≫ hU.isoSpec.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) x.asIdeal.ResidueField)))
        ≫ (f ⁻¹ᵁ U).ι)
      (pullback.snd ((f ∣_ U) ≫ hU.isoSpec.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) x.asIdeal.ResidueField)))
        ≫ Spec.map (affineOpenResidueFieldIso U hU x t h).hom)
      f (T.fromSpecResidueField t) := by
  -- 1. `f⁻¹U → Spec A` is the base change of `f` along `fromSpec = isoSpec.inv ≫ ι`
  have sq_iso : IsPullback U.ι hU.isoSpec.hom (𝟙 T) hU.fromSpec :=
    IsPullback.of_vert_isIso ⟨by rw [← IsAffineOpen.isoSpec_inv_ι]; simp⟩
  have sq2 : IsPullback (f ⁻¹ᵁ U).ι ((f ∣_ U) ≫ hU.isoSpec.hom) (f ≫ 𝟙 T) hU.fromSpec :=
    (isPullback_morphismRestrict f U).flip.paste_vert sq_iso
  rw [Category.comp_id] at sq2
  -- 2. paste horizontally with the base change square
  have sq3 := (IsPullback.of_hasPullback ((f ∣_ U) ≫ hU.isoSpec.hom)
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) x.asIdeal.ResidueField)))).paste_horiz sq2
  -- 3. replace the base point by `Spec κ(t)`
  have sq_left : IsPullback (𝟙 _)
      (pullback.snd ((f ∣_ U) ≫ hU.isoSpec.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) x.asIdeal.ResidueField)))
        ≫ Spec.map (affineOpenResidueFieldIso U hU x t h).hom)
      (pullback.snd ((f ∣_ U) ≫ hU.isoSpec.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) x.asIdeal.ResidueField))))
      (Spec.map (affineOpenResidueFieldIso U hU x t h).inv) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.id_comp, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
        Category.comp_id]⟩
  have sq4 := sq_left.paste_horiz sq3
  rw [Category.id_comp, SpecMap_affineOpenResidueFieldIso_inv_fromSpec] at sq4
  exact sq4

end AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types true

theorem fiber_cohomology_iso_baseChange_residueField {Y T : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ T) (M : Y.Modules) (V : T.affineOpens) (t : T) (ht : t ∈ (V : T.Opens))
    (i : ℕ) :
    let A := Γ(T, (V : T.Opens))
    let fV : (f ⁻¹ᵁ (V : T.Opens)).toScheme ⟶ AlgebraicGeometry.Spec A :=
      (f ∣_ (V : T.Opens)) ≫ V.2.isoSpec.hom
    let p := V.2.primeIdealOf ⟨t, ht⟩
    -- the two fibres are viewed as `κ(t)`- and `κ(p)`-schemes via `fiberToSpecResidueField` and the second
    -- projection (this gives the linear structures on cohomology)
    letI := f.fiberOverSpecResidueField t
    letI : (CategoryTheory.Limits.pullback fV
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField)))).Over
        (AlgebraicGeometry.Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
      ⟨CategoryTheory.Limits.pullback.snd _ _⟩
    Module.finrank (T.residueField t) (AlgebraicGeometry.sheafCohomology (f.fiber t)
        ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t)).obj M) i)
      = Module.finrank (CommRingCat.of p.asIdeal.ResidueField) (AlgebraicGeometry.sheafCohomology
          (CategoryTheory.Limits.pullback fV
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
              (algebraMap A p.asIdeal.ResidueField))))
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (CategoryTheory.Limits.pullback.fst fV _ ≫ (f ⁻¹ᵁ (V : T.Opens)).ι)).obj M) i) := by
  intro A fV p
  letI := f.fiberOverSpecResidueField t
  have hfib : IsPullback (f.fiberι t) (f.fiberToSpecResidueField t) f
      (T.fromSpecResidueField t) :=
    IsPullback.of_hasPullback f (T.fromSpecResidueField t)
  have sq := AlgebraicGeometry.isPullback_fiber_affine_baseChange f (V : T.Opens) V.2 p t
    (V.2.fromSpec_primeIdealOf ⟨t, ht⟩)
  have hfst := hfib.isoIsPullback_hom_fst _ _ sq
  have hsnd := hfib.isoIsPullback_hom_snd _ _ sq
  rw [AlgebraicGeometry.sheafCohomology.finrank_eq_of_iso (T.residueField t)
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hfst.symm).app M ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp (hfib.isoIsPullback _ _ sq).hom _).app
        M).symm) i]
  dsimp only [Functor.comp_obj]
  -- all implicit arguments are given explicitly: letting Lean unify `K K' Z X N` by itself unfolds
  -- `Scheme.Modules.pullback` to whnf and times out
  exact AlgebraicGeometry.sheafCohomology_finrank_eq_of_schemeIso'
    (K := T.residueField t) (K' := CommRingCat.of p.asIdeal.ResidueField)
    (Z := f.fiber t) (X := pullback fV (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField))))
    (f.fiberToSpecResidueField t) (pullback.snd _ _) (hfib.isoIsPullback _ _ sq)
    (AlgebraicGeometry.affineOpenResidueFieldIso (V : T.Opens) V.2 p t
      (V.2.fromSpec_primeIdealOf ⟨t, ht⟩)) hsnd
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (pullback.fst fV _ ≫ (f ⁻¹ᵁ (V : T.Opens)).ι)).obj M) i

end
