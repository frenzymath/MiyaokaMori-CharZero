import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SurfaceClosedPointRegularDimTwo
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0805
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agq

/-! # The fibre of a point blowup over the centre is a projective line

For the blowup `π : Bl_p S → S` of a smooth surface `S` at a closed point `p`, the scheme-theoretic
fibre `π⁻¹(p) = Bl ×_S Spec κ(p)` is isomorphic to `P¹_{κ(p)}` as a `κ(p)`-scheme.

Source: Stacks 0AGQ(1) (the closed fibre of the blowup of a two-dimensional regular local ring along
its maximal ideal is `P¹_κ`), transported from `Spec O_{S,p}` to the surface by Stacks 0805 (blowup
commutes with flat base change); used in the proof of Lemma 5.1 of the paper (§5).

This is the geometric input of `exceptional_isSmoothRational`, which combines it with the transport
of `P¹` along `κ(p) ≅ k` and the fact that a reduced closed subscheme is determined by its support
(`IsClosedImmersion.isIso_lift`) to identify `pointBlowup.exceptional S p hp` (the reduced induced
structure on `π⁻¹{p}`) with `P¹_k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section


/-- The scheme-theoretic fibre `π⁻¹(p)` of a point blowup is isomorphic to `P¹_{κ(p)}` over `κ(p)`.

Write `A := O_{S,p}` (`S.toScheme.presheaf.stalk p`), `κ := κ(p) = A/𝔪` (`S.toScheme.residueField p`,
definitionally `IsLocalRing.ResidueField A`), `I := vanishingIdeal {p}`, `π := (blowup I).hom`, and
`j := S.fromSpecStalk p : Spec A → S`. The fibre is `π.fiber p = pullback π (S.fromSpecResidueField p)`,
and `S.fromSpecResidueField p = Spec.map (residue A) ≫ j` by definition (`rfl`).

**Proof.** (`pointBlowup.fiber_iso_projectiveLine : Nonempty (π.fiber p ≅ P¹_κ)` is the same
statement without the compatibility with the structure morphisms.)
1. **`A` is a two-dimensional regular local ring**: `SmoothProjectiveSurface.stalk_regular_dim_two S p hp`.
2. **`j` is flat**: `AlgebraicGeometry.Scheme.flat_fromSpecStalk`.
3. **Stacks 0805** (`AlgebraicGeometry.Scheme.blowup_flatBaseChange j I`): there is
   `e₁ : Bl_{I.comap j}(Spec A) ≅ Spec A ×_S Bl_I S` with `e₁.hom ≫ pullback.fst = (blowup (I.comap j)).hom`;
   this equation is exactly the compatibility needed to transport the projection to `Spec A`.
4. **`I.comap j = ofIdealTop 𝔪_A`**: `pointBlowup.vanishingIdeal_comap_fromSpecStalk`.
5. **Gluing the fibre**: `S.fromSpecResidueField p = Spec.map (residue A) ≫ j` (`rfl`);
   `pullbackSymmetry`, `pullback.congrHom`, `pullbackRightPullbackFstIso` and `pullback.map` along `e₁`
   identify `π.fiber p` with `pullback (blowup (ofIdealTop 𝔪)).hom (Spec.map (algebraMap A κ))`; this
   chain is compatible with the projections to `Spec κ` on both sides
   (`π.fiberToSpecResidueField p = pullback.snd` on the left, `pullback.snd` on the right): each step is
   a canonical pullback isomorphism (its `_snd` simp lemma) or `pullback.map` along `e₁` (using the
   equation of step 3).
6. **Stacks 0AGQ(1), with the isomorphism over `κ`**:
   `AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptional_over_residueField` gives
   `e : pullback (blowup (ofIdealTop 𝔪)).hom (Spec.map (algebraMap A κ)) ≅ P¹_κ` with
   `e.hom ≫ (P¹_κ ↘ Spec κ) = pullback.snd _ _`. Since `residueField p = IsLocalRing.ResidueField (stalk p)`
   and `algebraMap A κ = residue A` are definitional equalities, it applies directly.
7. Compose the isomorphisms of steps 5 and 6.

Implementation: first `change` unfolds `pointBlowup.π` into the structure morphism of the blowup
(otherwise `rw`/`simp` do not see through the definition of `π` at implicit transparency); the
`pullback.map` is taken in the forward direction (`i₁ = e₁.inv`), and the compatibility of `snd` is
checked by one `simp only [pullback.lift_snd, pullbackSymmetry_hom_comp_*, pullbackRightPullbackFstIso_inv_fst, …]`.
Edge cases: `p` is required to be a closed point by `hp`; `k` only needs `PerfectField` (required by
the definition of `pointBlowup`); algebraic closedness of `k` is not needed here. -/
theorem pointBlowup.exists_fiber_iso_projectiveLine_residueField {k : Type u} [Field k]
    [PerfectField k] (S : SmoothProjectiveSurface k) (p : S.toScheme)
    (hp : IsClosed ({p} : Set S.toScheme)) :
    ∃ e : (pointBlowup.π S p hp).fiber p ≅ ProjectiveLine (S.toScheme.residueField p),
      e.hom ≫ (ProjectiveLine (S.toScheme.residueField p) ↘
          AlgebraicGeometry.Spec (CommRingCat.of (S.toScheme.residueField p))) =
        (pointBlowup.π S p hp).fiberToSpecResidueField p := by
  have : AlgebraicGeometry.Flat (S.toScheme.fromSpecStalk p) :=
    AlgebraicGeometry.Scheme.flat_fromSpecStalk _ _
  obtain ⟨hreg, hdim⟩ := S.stalk_regular_dim_two p hp
  -- Step 6: Stacks 0AGQ (isomorphism over `κ`), the centre identified with `𝔪_p` by step 4;
  -- `algebraMap A κ = residue A` and `residueField p = ResidueField (stalk p)` are definitional, so `exact` works.
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : pullback (AlgebraicGeometry.Scheme.blowup ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap (S.toScheme.fromSpecStalk p))).hom (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) ≅ ProjectiveLine (S.toScheme.residueField p),
      e₂.hom ≫ (ProjectiveLine (S.toScheme.residueField p) ↘ AlgebraicGeometry.Spec (CommRingCat.of (S.toScheme.residueField p))) = pullback.snd (AlgebraicGeometry.Scheme.blowup ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap (S.toScheme.fromSpecStalk p))).hom (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) := by
    rw [pointBlowup.vanishingIdeal_comap_fromSpecStalk S p hp]
    exact AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptional_over_residueField
      (S.toScheme.presheaf.stalk p) hdim
  -- Step 3: Stacks 0805
  obtain ⟨e₁, he₁⟩ := AlgebraicGeometry.Scheme.blowup_flatBaseChange (S.toScheme.fromSpecStalk p)
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  have hφ : S.toScheme.fromSpecResidueField p = (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) ≫ S.toScheme.fromSpecStalk p := rfl
  -- `pointBlowup.π S p hp` is by definition the structure morphism of the blowup; rewrite the whole goal
  -- in terms of the blowup so that the later `rw`/`simp` need not unfold `pointBlowup`.
  change ∃ e : pullback (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom (S.toScheme.fromSpecResidueField p) ≅ ProjectiveLine (S.toScheme.residueField p),
      e.hom ≫ (ProjectiveLine (S.toScheme.residueField p) ↘ AlgebraicGeometry.Spec (CommRingCat.of (S.toScheme.residueField p))) = pullback.snd (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom (S.toScheme.fromSpecResidueField p)
  -- Step 5: the gluing chain (`pullback.map` in the forward direction, to check `snd` compatibility)
  have eq1 : pullback.fst (S.toScheme.fromSpecStalk p) (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom ≫
      𝟙 (AlgebraicGeometry.Spec (S.toScheme.presheaf.stalk p)) =
      e₁.inv ≫ (e₁.hom ≫ pullback.fst (S.toScheme.fromSpecStalk p) (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom) := by
    rw [Category.comp_id, Iso.inv_hom_id_assoc]
  have eq2 : (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) ≫ 𝟙 (AlgebraicGeometry.Spec (S.toScheme.presheaf.stalk p)) = 𝟙 _ ≫ (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) := by
    rw [Category.comp_id, Category.id_comp]
  let e₃ : pullback (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom (S.toScheme.fromSpecResidueField p) ≅ pullback (AlgebraicGeometry.Scheme.blowup ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap (S.toScheme.fromSpecStalk p))).hom (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) :=
    pullbackSymmetry _ _ ≪≫ pullback.congrHom hφ rfl ≪≫
    (pullbackRightPullbackFstIso (S.toScheme.fromSpecStalk p) (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom (AlgebraicGeometry.Spec.map (S.toScheme.residue p))).symm ≪≫
    pullbackSymmetry _ _ ≪≫
    asIso (pullback.map (pullback.fst (S.toScheme.fromSpecStalk p) (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom) (AlgebraicGeometry.Spec.map (S.toScheme.residue p))
      (e₁.hom ≫ pullback.fst (S.toScheme.fromSpecStalk p) (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom) (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) e₁.inv (𝟙 _) (𝟙 _) eq1 eq2) ≪≫
    pullback.congrHom he₁ rfl
  have he₃ : e₃.hom ≫ pullback.snd (AlgebraicGeometry.Scheme.blowup ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap (S.toScheme.fromSpecStalk p))).hom (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) = pullback.snd (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom (S.toScheme.fromSpecResidueField p) := by
    simp only [e₃, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, pullback.congrHom_hom,
      pullback.lift_snd, pullback.lift_fst, Category.comp_id, pullbackSymmetry_hom_comp_snd,
      pullbackSymmetry_hom_comp_fst, pullbackRightPullbackFstIso_inv_fst]
  exact ⟨e₃ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₃]⟩

end
