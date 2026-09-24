import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Modules.RelativelyVeryAmple
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.RelativelyVeryAmpleFiberAmple_IsAmpleAt

/-! # A relatively very ample line bundle is ample on every fibre

If `π : Y → X` is **quasi-compact** and `L` is relatively very ample for `π`, then for every
`x ∈ X` the restriction of `L` to the fibre `Y_x` is ample.

References: Lazarsfeld, *Positivity I*, Thm 1.7.8 ("only if"); Stacks 0B3F. Used for the
projection `π_k` of the weighted projectivization in §2 of the paper.

The quasi-compactness hypothesis is necessary: `IsAmple` requires the underlying space to be
compact, while the graded algebra `S` in `IsRelativelyVeryAmple` carries no finiteness. For
`X = Spec k`, `S = k[x₀, x₁, …]` (countably many variables, generated in degree one),
`Y = Proj_X S`, `i = 𝟙`, `L = O(1)`, the fibre `Y_x ≅ Proj k[x₀, x₁, …]` is not quasi-compact
(the `D₊(xᵢ)` form an open cover without finite subcover). In the paper `π_k` is proper, and
Stacks 0B3F / Lazarsfeld 1.7.8 assume `f` proper.

Route (not through the base change of relative Proj, Stacks 01O3): work directly on
`P = Proj_X S`. Take an affine open `V ∋ x`; `Y_x → P_x := Spec κ(x) ×_X P` is a base change of `i`
(a closed immersion), `P_x → π⁻¹V` is a base change of `Spec κ(x) → V` (an affine morphism), and
the composite `ψ : Y_x → π⁻¹V ≅ Proj Γ(V,S)` is affine; `O(1)|_{π⁻¹V}` is pointwise ample (the
`D₊(f)`, `f ∈ Γ(V,S)_1`, are affine), pointwise ampleness pulls back along affine morphisms and
transports along isomorphisms, and compactness of the fibre comes from `π` quasi-compact.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **A relatively very ample line bundle is ample on every fibre of a quasi-compact morphism**
(Lazarsfeld Thm 1.7.8 "only if"; the fibre form of Stacks 0B3F).

Proof sketch: unfold `IsRelativelyVeryAmple`: `S` is generated in degree one, `i : Y → P := Proj_X S`
is a closed immersion with `i ≫ p = π`, and `L ≅ i^*O(1)`. The fibre `Y_x = π.fiber x` is compact
(`π` quasi-compact). For `y ∈ Y_x` take an affine open `V ∋ x`:
1. `j : Y_x → P_x := Spec κ(x) ×_X P` is given by `(Y_x → Spec κ(x), Y_x → Y → P)`; pasting the
   fibre square with the square of `P_x` (`IsPullback.of_right`) shows that `j` is a base change of
   `i`, hence a closed immersion (`MorphismProperty.of_isPullback`).
2. The image of `P_x → P` lies in `π⁻¹V`, so it lifts to `ρ : P_x → π⁻¹V`, which is a base change
   of `g' : Spec κ(x) → V` along `p|_V` (`isPullback_morphismRestrict`); `g'` is a morphism between
   affine schemes, hence affine, so `ρ` is affine; `ψ := j ≫ ρ` is affine and
   `ψ ≫ (π⁻¹V).ι = fiberι ≫ i`.
3. `O(1)|_{π⁻¹V}` is a line bundle, pointwise ample at `ψ y`
   (`relativeProj.isAmpleAt_twist_one_pullback_preimage_ι`); its pullback along the affine `ψ` is
   pointwise ample at `y` (`IsAmpleAt.pullback_of_isAffineHom`).
4. `ψ^*((π⁻¹V).ι^*O(1)) ≅ (ψ ≫ ι)^*O(1) = (fiberι ≫ i)^*O(1) ≅ fiberι^*(i^*O(1)) ≅ fiberι^*L`
   (`pullbackComp`, `eqToIso`, `mapIso e.symm`), and pointwise ampleness transports along
   isomorphisms (`IsAmpleAt.of_iso`). -/
theorem AlgebraicGeometry.isAmple_fiber_of_isRelativelyVeryAmple_of_quasiCompact
    {Y X : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ X) [AlgebraicGeometry.QuasiCompact π]
    (L : Y.Modules) [L.IsLineBundle]
    (hL : AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple π L) (x : X) :
    AlgebraicGeometry.IsAmple
      ((AlgebraicGeometry.Scheme.Modules.pullback (π.fiberι x)).obj L) := by
  obtain ⟨S, i, hgen, hci, hπ, ⟨e⟩⟩ := hL
  refine ⟨inferInstance, fun y => ?_⟩
  obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x)
  -- the fibre square
  have hfib : IsPullback (π.fiberι x) (π.fiberToSpecResidueField x) π (X.fromSpecResidueField x) :=
    IsPullback.of_hasPullback π (X.fromSpecResidueField x)
  -- Step 1: j : Y_x ⟶ Spec κ(x) ×_X P, a closed immersion
  have hw : π.fiberToSpecResidueField x ≫ X.fromSpecResidueField x =
      (π.fiberι x ≫ i) ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom := by
    rw [Category.assoc, hπ]
    exact (π.fiber_fac x).symm
  let j : π.fiber x ⟶ pullback (X.fromSpecResidueField x) (AlgebraicGeometry.Scheme.relativeProj S).hom :=
    pullback.lift (π.fiberToSpecResidueField x) (π.fiberι x ≫ i) hw
  have hj_fst : j ≫ pullback.fst _ _ = π.fiberToSpecResidueField x := pullback.lift_fst _ _ _
  have hj_snd : j ≫ pullback.snd _ _ = π.fiberι x ≫ i := pullback.lift_snd _ _ _
  have hsq : IsPullback j (π.fiberι x)
      (pullback.snd (X.fromSpecResidueField x) (AlgebraicGeometry.Scheme.relativeProj S).hom) i := by
    refine IsPullback.of_right ?_ hj_snd
      (IsPullback.of_hasPullback (X.fromSpecResidueField x) (AlgebraicGeometry.Scheme.relativeProj S).hom)
    rw [hj_fst, hπ]
    exact hfib.flip
  haveI hjci : AlgebraicGeometry.IsClosedImmersion j :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsClosedImmersion) hsq.flip hci
  -- Step 2: ρ : Spec κ(x) ×_X P ⟶ π⁻¹V, an affine morphism
  have hρ_range : Set.range (pullback.snd (X.fromSpecResidueField x)
        (AlgebraicGeometry.Scheme.relativeProj S).hom) ⊆
      Set.range ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    show (AlgebraicGeometry.Scheme.relativeProj S).hom
      (pullback.snd (X.fromSpecResidueField x) (AlgebraicGeometry.Scheme.relativeProj S).hom z) ∈ V
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, ← pullback.condition,
      AlgebraicGeometry.Scheme.Hom.comp_apply]
    have hmem : X.fromSpecResidueField x
        (pullback.fst (X.fromSpecResidueField x) (AlgebraicGeometry.Scheme.relativeProj S).hom z) ∈
        Set.range (X.fromSpecResidueField x) := Set.mem_range_self _
    rw [AlgebraicGeometry.Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hxV
  let ρ := AlgebraicGeometry.IsOpenImmersion.lift ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V).ι
    (pullback.snd (X.fromSpecResidueField x) (AlgebraicGeometry.Scheme.relativeProj S).hom) hρ_range
  have hρ : ρ ≫ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V).ι =
      pullback.snd (X.fromSpecResidueField x) (AlgebraicGeometry.Scheme.relativeProj S).hom :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hg'_range : Set.range (X.fromSpecResidueField x) ⊆ Set.range (AlgebraicGeometry.Scheme.Opens.ι V) := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι, AlgebraicGeometry.Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr hxV
  let g' := AlgebraicGeometry.IsOpenImmersion.lift (AlgebraicGeometry.Scheme.Opens.ι V) (X.fromSpecResidueField x) hg'_range
  have hg' : g' ≫ (AlgebraicGeometry.Scheme.Opens.ι V) = X.fromSpecResidueField x := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  haveI hVaff : AlgebraicGeometry.IsAffine (AlgebraicGeometry.Scheme.Opens.toScheme V) := hV
  have hsq2 : IsPullback ρ
      (pullback.fst (X.fromSpecResidueField x) (AlgebraicGeometry.Scheme.relativeProj S).hom)
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ∣_ V) g' := by
    refine IsPullback.of_right ?_ ?_
      (AlgebraicGeometry.isPullback_morphismRestrict (AlgebraicGeometry.Scheme.relativeProj S).hom V).flip
    · rw [hρ, hg']
      exact (IsPullback.of_hasPullback (X.fromSpecResidueField x)
        (AlgebraicGeometry.Scheme.relativeProj S).hom).flip
    · rw [← cancel_mono (AlgebraicGeometry.Scheme.Opens.ι V), Category.assoc, Category.assoc, AlgebraicGeometry.morphismRestrict_ι, hg',
        ← Category.assoc, hρ]
      exact pullback.condition.symm
  haveI hρaff : AlgebraicGeometry.IsAffineHom ρ :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom) hsq2.flip inferInstance
  let ψ : π.fiber x ⟶ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V).toScheme := j ≫ ρ
  haveI hψaff : AlgebraicGeometry.IsAffineHom ψ := inferInstance
  have hψ : ψ ≫ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V).ι = π.fiberι x ≫ i := by
    show (j ≫ ρ) ≫ _ = _
    rw [Category.assoc, hρ, hj_snd]
  -- Step 3: pointwise ampleness of ψ^*(O(1)|_{π⁻¹V}) at y
  haveI hLB := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_pullback_twist_one_preimage_ι S hgen ⟨V, hV⟩
  have h1 := AlgebraicGeometry.Scheme.relativeProj.isAmpleAt_twist_one_pullback_preimage_ι S hgen ⟨V, hV⟩
    (ψ.base y)
  have h2 := h1.pullback_of_isAffineHom ψ _
  -- Step 4: transport along ψ^*(ι^*O(1)) ≅ (ψ ≫ ι)^*O(1) = (fiberι ≫ i)^*O(1) ≅ fiberι^*(i^*O(1)) ≅ fiberι^*L
  let E : (AlgebraicGeometry.Scheme.Modules.pullback ψ).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V).ι).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S 1)) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (π.fiberι x)).obj L :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp ψ
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V).ι).app
      (AlgebraicGeometry.Scheme.relativeProj.twist S 1) ≪≫
    eqToIso (congrArg (fun φ : π.fiber x ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left =>
      (AlgebraicGeometry.Scheme.Modules.pullback φ).obj (AlgebraicGeometry.Scheme.relativeProj.twist S 1)) hψ) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp (π.fiberι x) i).symm.app
      (AlgebraicGeometry.Scheme.relativeProj.twist S 1) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback (π.fiberι x)).mapIso e.symm
  exact AlgebraicGeometry.IsAmpleAt.of_iso E h2

end
