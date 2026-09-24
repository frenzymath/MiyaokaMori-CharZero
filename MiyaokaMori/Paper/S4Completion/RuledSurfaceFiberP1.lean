import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIso
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.RelativeProjWeightedPolynomialProductAffine
import MiyaokaMori.Paper.S3PositiveLine.Realization.RuledSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceGradedRingIsos
import MiyaokaMori.AlgebraicGeometry.Modules.PullbackDualBiprodFreeLocalRing
import MiyaokaMori.AlgebraicGeometry.Modules.SymFreeIsoPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.SymGradedAlgebraIsoOfIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothRationalCurve
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01o3
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.Stacks01ci

/-! # Fibres of the ruled surface are `P¹`

Every fibre of the ruled surface `W = P(O_C̃ ⊕ L) → C̃` over a closed point `y` is isomorphic to `P¹_k`
and is reduced and irreducible (Corollary 4.3 and Lemma 5.1
of the paper, §4–§5).

Route. Write `V := O ⊕ L`, `𝒜 := Sym(V^∨)` (so `W = Proj_C 𝒜` and `π = ruledSurface.π L`), let
`g : Spec κ(y) → C` be the canonical map and `K := κ(y)`:
1. `π.fiber y = pullback π g ≅ (relativeProj (𝒜.pullback g)).left` over `Spec K`
   (Stacks 01O3, `relativeProj_baseChange`, plus `pullbackSymmetry`);
2. `𝒜.pullback g ≅ Sym(g^*V^∨)` (Stacks 01CI, `symGradedAlgebra_pullback`);
3. `g^*V^∨ ≅ O^2` on `Spec K` (the pullback of a rank-two bundle to a local scheme is free), hence
   `Sym(g^*V^∨) ≅ Sym(O^2) ≅ O_{Spec K}[T_0,T_1]` with the standard grading; an isomorphism of
   graded algebras induces an isomorphism of relative Proj over the base;
4. `Proj_{Spec K} O[T_0,T_1] ≅ P_K(1,1)` over `Spec K`;
5. `P_K(1,1) ≅ P^1_K` over `Spec K` (`weightedProjectiveSpace_one_iso_projectiveSpace`);
6. `κ(y) ≅ k` since `y` is closed and `k` is algebraically closed (`residueFieldIsoBase`), so
   `P^1_K ≅ P^1_k` over `Spec K ≅ Spec k` (`projectiveSpace_iso_of_ringIso`).
The composite is compatible with the structure morphisms to `Spec k`
(`ruledSurface.fiber_iso_projectiveLine_over`). The integral curve `F` is the fibre itself with
`ι = π.fiberι y`: a closed immersion because `Spec κ(y) → C` is one for the closed point `y`
(`isClosed_singleton_iff_isClosedImmersion`) and closed immersions are stable under base change;
integral, proper over `k` and one-dimensional by transport along the isomorphism with `P^1_k`
(`ProjectiveLine.asSmoothProjectiveCurve`); its image is `π⁻¹(y)` (`range_fiberι`); and it is smooth
rational by the same isomorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre embedding over a closed point is a closed immersion: `Spec κ(y) → Y` is a closed
immersion for closed `y` (Mathlib `isClosed_singleton_iff_isClosedImmersion`), and closed
immersions are stable under base change (`IsClosedImmersion.isStableUnderBaseChange`). -/
theorem AlgebraicGeometry.Scheme.Hom.fiberι_isClosedImmersion_of_isClosed
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (y : Y) (hy : IsClosed ({y} : Set Y)) :
    AlgebraicGeometry.IsClosedImmersion (f.fiberι y) := by
  have := AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hy
  exact MorphismProperty.pullback_fst (P := @AlgebraicGeometry.IsClosedImmersion) _ _ this

/-- The fibre of the ruled surface `P(O ⊕ L) → C` over a closed point `y` is `P^1_k`,
compatibly with the structure morphisms to `Spec k` (see the module docstring for the route). -/
theorem ruledSurface.fiber_iso_projectiveLine_over {k : Type u} [Field k] [IsAlgClosed k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) (y : C.toScheme)
    (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ e : (ruledSurface.π L).fiber y ≅ ProjectiveLine k,
      e.hom ≫ (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        (ruledSurface.π L).fiberι y ≫
          ((ruledSurface L).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  classical
  -- notation
  let V : C.toVariety.toScheme.Modules :=
    CategoryTheory.Limits.biprod (C := C.toVariety.toScheme.Modules)
      (show C.toVariety.toScheme.Modules from
        SheafOfModules.unit C.toVariety.toScheme.ringCatSheaf) L.toModules
  let 𝒜 : C.toScheme.GradedQCAlgebra :=
    AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)
  let K : Type u := C.toScheme.residueField y
  -- Step 1 (Stacks 01O3): the fiber is the relative Proj of the pulled-back algebra
  obtain ⟨e₀, he₀, -⟩ := AlgebraicGeometry.Scheme.relativeProj_baseChange
    (C.toScheme.fromSpecResidueField y) 𝒜
  let e₁ : CategoryTheory.Limits.pullback (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom
      (C.toScheme.fromSpecResidueField y) ≅
      (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback (C.toScheme.fromSpecResidueField y))).left :=
    (CategoryTheory.Limits.pullbackSymmetry (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom
      (C.toScheme.fromSpecResidueField y)) ≪≫ e₀.symm
  have he₁ : e₁.hom ≫
      (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback (C.toScheme.fromSpecResidueField y))).hom =
      CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom
        (C.toScheme.fromSpecResidueField y) := by
    simp only [e₁, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
      CategoryTheory.Category.assoc]
    rw [← he₀, CategoryTheory.Iso.inv_hom_id_assoc,
      CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst]
  -- Step 2 (Stacks 01CI): Sym commutes with pullback
  have : (AlgebraicGeometry.Scheme.Modules.dual V).IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' V
  have : (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
  obtain ⟨φ₂⟩ := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_pullback
    (C.toScheme.fromSpecResidueField y) (AlgebraicGeometry.Scheme.Modules.dual V)
  -- Step 3: the pulled-back module is free of rank 2, so Sym is the polynomial algebra
  obtain ⟨ψ⟩ := AlgebraicGeometry.Scheme.Modules.pullback_dual_unit_biprod_iso_free_of_isLocalRing
    L.toModules (C.toScheme.residueField y) (C.toScheme.fromSpecResidueField y)
  have : ((AlgebraicGeometry.Scheme.Modules.pullback (C.toScheme.fromSpecResidueField y)).obj
      (AlgebraicGeometry.Scheme.Modules.dual V)).IsQuasicoherent := inferInstance
  have : (SheafOfModules.free (R := (AlgebraicGeometry.Spec (C.toScheme.residueField y)).ringCatSheaf)
      (ULift.{u} (Fin 2))).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
  obtain ⟨φ₃⟩ := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_iso_of_iso ψ
  obtain ⟨φ₄⟩ := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_free_iso_weightedPolynomialQCAlgebra
    (AlgebraicGeometry.Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))
  obtain ⟨e₂, he₂, -⟩ := AlgebraicGeometry.Scheme.relativeProj.exists_iso_of_algebra_iso
    (S := 𝒜.pullback (C.toScheme.fromSpecResidueField y))
    (T := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
      (AlgebraicGeometry.Spec (CommRingCat.of K)) (fun _ : ULift.{u} (Fin 2) => 1) (fun _ => Nat.one_pos))
    (φ₂ ≪≫ φ₃ ≪≫ φ₄)
  -- Step 4: relative Proj of the polynomial algebra over Spec K is P(1,1) over K
  obtain ⟨e₄, he₄, -⟩ := relativeProj_weightedPolynomialQCAlgebra_spec_iso K
    (fun _ : ULift.{u} (Fin 2) => 1) (fun _ => Nat.one_pos)
  -- Step 5: P(1,1) = P¹
  obtain ⟨e₅, he₅⟩ := weightedProjectiveSpace_one_iso_projectiveSpace K 1
  -- Step 6: κ(y) = k
  have : AlgebraicGeometry.LocallyOfFiniteType
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := inferInstance
  obtain ⟨e₆, he₆⟩ := projectiveSpace_iso_of_ringIso 1 (K := K) (k := k)
    (AlgebraicGeometry.residueFieldIsoBase
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) y hy)
  refine ⟨e₁ ≪≫ e₂ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆, ?_⟩
  show (e₁ ≪≫ e₂ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆).hom ≫
      (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
    CategoryTheory.Limits.pullback.fst (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom
        (C.toScheme.fromSpecResidueField y) ≫
      (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Category.assoc]
  rw [he₆, reassoc_of% he₅, reassoc_of% he₄, reassoc_of% he₂, reassoc_of% he₁,
    AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv,
    ← CategoryTheory.Limits.pullback.condition_assoc]

/-- The fibre of `P(O ⊕ L) → C` over a closed point `y` is isomorphic to `P¹_k`, and it is the image of
a smooth rational integral curve `F ⊆ P(O ⊕ L)`. -/
theorem ruled_fiber_iso_p1 {k : Type u} [Field k] [IsAlgClosed k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    Nonempty ((ruledSurface.π L).fiber y ≅ ProjectiveLine k)
    ∧ ∃ F : IntegralCurve k (ruledSurface L).toScheme,
        Set.range F.ι.base = (ruledSurface.π L).base ⁻¹' {y} ∧ F.IsSmoothRational := by
  obtain ⟨e, he⟩ := ruledSurface.fiber_iso_projectiveLine_over L y hy
  have hP1 : AlgebraicGeometry.IsIntegral (ProjectiveLine k) :=
    SmoothProjectiveCurve.isIntegral (ProjectiveLine.asSmoothProjectiveCurve k)
  have : Nonempty ((ruledSurface.π L).fiber y) :=
    ⟨e.inv.base (Nonempty.some inferInstance)⟩
  have : AlgebraicGeometry.IsClosedImmersion ((ruledSurface.π L).fiberι y) :=
    AlgebraicGeometry.Scheme.Hom.fiberι_isClosedImmersion_of_isClosed _ y hy
  have : AlgebraicGeometry.IsIntegral ((ruledSurface.π L).fiber y) :=
    AlgebraicGeometry.isIntegral_of_isOpenImmersion e.hom
  have : AlgebraicGeometry.IsProper ((ruledSurface.π L).fiberι y ≫
      ((ruledSurface L).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
    rw [← he]
    infer_instance
  let F : IntegralCurve k (ruledSurface L).toScheme :=
    { carrier := (ruledSurface.π L).fiber y
      ι := (ruledSurface.π L).fiberι y
      dim_eq_one := by
        change topologicalKrullDim ((ruledSurface.π L).fiber y) = 1
        rw [IsHomeomorph.topologicalKrullDim_eq _
          (AlgebraicGeometry.Scheme.homeoOfIso e).isHomeomorph]
        exact (ProjectiveLine.asSmoothProjectiveCurve k).dim_one }
  refine ⟨⟨e⟩, F, ?_, ⟨e, he⟩⟩
  exact (ruledSurface.π L).range_fiberι y

end
