import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharLocallyConstantAffineBase
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.FiberCohomologyAffineBaseChange
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.FlatFamilyRestrictAffineBase
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap

/-! # Local constancy of the Euler characteristic in a flat proper family

Let `T` be locally Noetherian, `f : Y → T` proper, and `M` coherent and flat over `T`. Then
`t ↦ χ_{κ(t)}(Y_t, M|_{Y_t})` is a locally constant function on `T` (`T` need not be connected and `f` need
not be projective; the constancy over a connected base is a corollary).

Proof sketch:
1. Take an affine open neighbourhood `V` of `t`, `A := Γ(T, V)` Noetherian; `f_V := (f|_V) ≫ (V ≅ Spec A)` is
   proper (properness is local on the target and stable under composition with isomorphisms);
   `M_V` := the pullback of `M` along `f⁻¹(V) → Y` is coherent and flat over `A`.
2. On the affine base: `g(p) := χ_{κ(p)}((f⁻¹V)_{κ(p)}, (M_V)_{κ(p)})` is locally constant on `Spec A`
   (`EulerCharLocallyConstantAffineBase.lean`).
3. Base change of fibre cohomology: for `t' ∈ V` with corresponding prime `p'`,
   `dim H^i(Y_{t'}, M|) = dim H^i((f⁻¹V)_{κ(p')}, pullback of M along (fst ≫ ι))`; the composition
   isomorphism `Scheme.Modules.pullbackComp` turns the latter into `(M_V)_{κ(p')}`, so `χ(t') = g(p')`.
4. `t' ↦ p'` is a continuous map `V → Spec A` (`IsAffineOpen.primeIdealOf` = `isoSpec.hom`), so `t' ↦ χ(t')`
   is locally constant on `V`; `V` is open, giving an open neighbourhood of `t` in `T` on which `χ` is
   constant.

Source: Hartshorne III.9.9 / III.12.2; Stacks 0B9T.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

/-- Step 3: the fibre `χ` at a point of `V` equals the `χ` at the corresponding prime of the affine base. -/
private theorem fiber_eulerChar_eq_affine {Y T : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ T)
    (M : Y.Modules) (V : T.affineOpens) (t : T) (ht : t ∈ (V : T.Opens)) :
    (letI := f.fiberOverSpecResidueField t
     AlgebraicGeometry.sheafEulerCharacteristic (k := T.residueField t) (f.fiber t)
      ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t)).obj M))
    = AlgebraicGeometry.baseChangeResidueFieldEulerChar
        ((f ∣_ (V : T.Opens)) ≫ V.2.isoSpec.hom)
        ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ (V : T.Opens)).ι).obj M)
        (V.2.primeIdealOf ⟨t, ht⟩) := by
  unfold AlgebraicGeometry.baseChangeResidueFieldEulerChar
    AlgebraicGeometry.sheafEulerCharacteristic
  refine finsum_congr fun i => ?_
  have h := fiber_cohomology_iso_baseChange_residueField f M V t ht i
  simp only at h
  rw [h]
  let _ : (pullback ((f ∣_ (V : T.Opens)) ≫ V.2.isoSpec.hom)
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Γ(T, (V : T.Opens))
        (V.2.primeIdealOf ⟨t, ht⟩).asIdeal.ResidueField)))).Over
      (AlgebraicGeometry.Spec (CommRingCat.of (V.2.primeIdealOf ⟨t, ht⟩).asIdeal.ResidueField)) :=
    ⟨pullback.snd _ _⟩
  have e := AlgebraicGeometry.sheafCohomology.finrank_eq_of_iso
      (V.2.primeIdealOf ⟨t, ht⟩).asIdeal.ResidueField
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.fst ((f ∣_ (V : T.Opens)) ≫ V.2.isoSpec.hom)
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Γ(T, (V : T.Opens))
            (V.2.primeIdealOf ⟨t, ht⟩).asIdeal.ResidueField))))
        (f ⁻¹ᵁ (V : T.Opens)).ι).app M).symm i
  simp only [Functor.comp_obj] at e
  rw [e]

attribute [local irreducible] AlgebraicGeometry.baseChangeResidueFieldEulerChar
  AlgebraicGeometry.sheafEulerCharacteristic in
theorem eulerCharacteristic_isLocallyConstant_in_flat_family
    {Y T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian T]
    (f : Y ⟶ T) [AlgebraicGeometry.IsProper f]
    (M : Y.Modules) [M.IsCoherent]
    (hM : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f M) :
    IsLocallyConstant (fun t : T =>
      letI := f.fiberOverSpecResidueField t
      AlgebraicGeometry.sheafEulerCharacteristic (k := T.residueField t) (f.fiber t)
        ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t)).obj M)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro t
  -- step 1: an affine open neighbourhood
  obtain ⟨V, hV, htV, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (x := t) (U := (⊤ : T.Opens)) trivial
  let V' : T.affineOpens := ⟨V, hV⟩
  have : IsNoetherianRing Γ(T, V) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian V'
  have : AlgebraicGeometry.IsProper ((f ∣_ V) ≫ hV.isoSpec.hom) := inferInstance
  have : ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M).IsCoherent :=
    AlgebraicGeometry.Scheme.Modules.isCoherent_pullback_preimage_ι f M V
  -- step 2
  have hg := AlgebraicGeometry.eulerChar_baseChange_residueField_isLocallyConstant
    ((f ∣_ V) ≫ hV.isoSpec.hom) _
    (AlgebraicGeometry.Scheme.Modules.isFlatOver_restrict_affine f M hM V')
  -- step 4: pull back along the continuous map `V → Spec A`
  have hg' := hg.comp_continuous (f := fun x : V => hV.primeIdealOf x)
    (hV.isoSpec.hom.continuous)
  obtain ⟨W, hW, htW, hconst⟩ := (IsLocallyConstant.iff_exists_open _).mp hg' ⟨t, htV⟩
  refine ⟨Subtype.val '' W, V.isOpen.isOpenMap_subtype_val W hW, ⟨⟨t, htV⟩, htW, rfl⟩, ?_⟩
  rintro _ ⟨⟨t', ht'⟩, ht'W, rfl⟩
  have e1 := fiber_eulerChar_eq_affine f M V' t' ht'
  have e2 := fiber_eulerChar_eq_affine f M V' t htV
  have e3 := hconst ⟨t', ht'⟩ ht'W
  exact e1.trans (e3.trans e2.symm)

end
