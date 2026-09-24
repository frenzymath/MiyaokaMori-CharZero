import MiyaokaMori.Prelude
import Mathlib.RingTheory.Nullstellensatz
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ProjectivizationChartLocalFormula
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationScalar
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mw

/-! # The morphism `P¹ → P^N` given by a tuple of binary forms

A tuple `(F_0, …, F_N)` of binary forms of degree `d` without common zero gives the `k`-morphism
`P¹ → P^N`, `[x : y] ↦ [F_0(x, y) : … : F_N(x, y)]`: regard each `F_j` as a global section of
`O_{P¹}(d)` and take the projectivization of the tuple (Stacks 01NE, `projectivizationMorphism`).
"No common zero" is stated for `k`-points only; for `k` algebraically closed this is equivalent to the
sections generating `O_{P¹}(d)` at every point.

Source: Debarre, Higher-Dimensional Algebraic Geometry, §6.1, formula (6.1); Stacks 01NE.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- As in `Stacks01mw`: definitional unfolding on homogeneous localizations.
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Scaling of homogeneous evaluation: if `F` is homogeneous of degree `d` then `F(t·g) = t^d · F(g)`. -/
theorem MvPolynomial.IsHomogeneous.eval₂_mul_left {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {F : MvPolynomial σ R} {d : ℕ} (hF : F.IsHomogeneous d) (ψ : R →+* S) (g : σ → S) (t : S) :
    MvPolynomial.eval₂ ψ (fun j => t * g j) F = t ^ d * MvPolynomial.eval₂ ψ g F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : ∑ j ∈ α.support, α j = d := by
    have := hF (MvPolynomial.mem_support_iff.mp hα)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  rw [Finset.prod_congr rfl (fun j _ => mul_pow t (g j) (α j)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

namespace ProjectiveSpace

variable {k : Type u} [Field k] {N : ℕ}

/-- **The algebraic half** (projective Nullstellensatz): if `F_0, …, F_M ∈ k[X_0,…,X_N]` (`k` algebraically
closed) have no common zero on `k^{N+1} ∖ {0}`, then for every point `x` of `P^N` (with relevant homogeneous
prime `𝔭_x`) some `F_j ∉ 𝔭_x`.

Proof. Suppose all `F_j ∈ 𝔭_x` and let `I = (F_0,…,F_M) ≤ 𝔭_x`. The zero locus of `I` is `⊆ {0}`, so
`(X_0,…,X_N) = I({0}) ≤ I(Z(I)) = √I ≤ √𝔭_x = 𝔭_x` (Nullstellensatz,
`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`), contradicting `x ∈ D₊(X_i)` for some `i` (the `D₊(X_i)`
cover `P^N`). -/
theorem exists_notMem_asHomogeneousIdeal [IsAlgClosed k] {M : ℕ}
    (F : Fin (M + 1) → MvPolynomial (Fin (N + 1)) k)
    (hF0 : ∀ v : Fin (N + 1) → k, v ≠ 0 → ∃ j, MvPolynomial.eval v (F j) ≠ 0)
    (x : AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N)) :
    ∃ j, F j ∉ x.asHomogeneousIdeal := by
  by_contra h
  push Not at h
  set I : Ideal (MvPolynomial (Fin (N + 1)) k) := Ideal.span (Set.range F) with hIdef
  have hI : I ≤ x.asHomogeneousIdeal.toIdeal := Ideal.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    exact h j)
  have hZ : MvPolynomial.zeroLocus k I ≤ ({0} : Set (Fin (N + 1) → k)) := by
    intro v hv
    by_contra hv0
    obtain ⟨j, hj⟩ := hF0 v hv0
    apply hj
    have := hv (F j) (Ideal.subset_span ⟨j, rfl⟩)
    rw [MvPolynomial.aeval_def, Algebra.algebraMap_self] at this
    exact this
  have hX : ∀ j, MvPolynomial.X j ∈ x.asHomogeneousIdeal.toIdeal := by
    intro j
    have h1 : MvPolynomial.X j ∈ MvPolynomial.vanishingIdeal k ({0} : Set (Fin (N + 1) → k)) := by
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have h2 := MvPolynomial.vanishingIdeal_anti_mono (k := k) hZ h1
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at h2
    have h3 : I.radical ≤ x.asHomogeneousIdeal.toIdeal := by
      calc I.radical ≤ x.asHomogeneousIdeal.toIdeal.radical := Ideal.radical_mono hI
        _ = x.asHomogeneousIdeal.toIdeal := x.isPrime.radical
    exact h3 h2
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    ((AlgebraicGeometry.Proj.projectiveGrading_iSup_basicOpen_X k N).ge (Set.mem_univ x))
  exact hi (hX i)

open MiyaokaMori.WeightedJets.ProjTwisting AlgebraicGeometry.Scheme.Modules in
/-- **The geometric half** (the degree-`d` generalization of Stacks 01MW): for `F` homogeneous of degree `d`
on `P^N`, evaluating at the coordinate sections `x_0, …, x_N ∈ Γ(O(1))` gives
`F(x_0,…,x_N) ∈ Γ(O(1)^{⊗d})` (`evalHomogeneousAtSections`); it does not vanish at the point `x` iff
`x ∈ D₊(F)`.

Proof sketch. Choose `i` with `x ∈ U := D₊(X_i)` (`projectiveGrading_iSup_basicOpen_X`). On `U`, `x_i` is a
frame of `O(1)` (`isFrame_homogeneousSection`) and `x_j|_U = (X_j/X_i) • x_i` (`coord_homogeneousSection`,
`divideSection`). The local formula `res_evalHomogeneousAtSections` gives
`F(x)|_U = F(X_0/X_i, …, X_N/X_i) • x_i^{⊗d}`, and the germ of `x_i^{⊗d}` corresponds to `1 ∈ 𝒪_x` under
`exists_stalkEquiv_monomialOn`; so `F(x)` vanishes at `x` iff the germ of the coefficient `c := F(X_j/X_i)` lies
in `𝔪_x` iff the value of `c` at `x` (`Proj.stalkIso'`) is not a unit of the homogeneous localization
`A_{(𝔭_x)}` iff its `val ∈ A_{𝔭_x}` is not a unit. Pointwise evaluation is a ring homomorphism; a constant
`φ(c₀)` has value `C c₀ / 1` (structure morphism `toSpecZero ≫ Spec(k → A_0)`,
`toSpecZero_appTop_ΓSpecIso_inv`, `zeroToGlobal_apply_val`), and `X_j/X_i` has value `X_j · (1/X_i)`; by
homogeneity the value of `c` is `(1/X_i)^d · (F/1)` with `1/X_i` a unit, so it is a unit iff `F/1` is a unit
iff `F ∉ 𝔭_x` (`IsLocalization.AtPrime.isUnit_to_map_iff`). Source: Stacks 01MW(5), 01MN. -/
theorem not_isZeroAt_evalHomogeneousAtSections_coordinate_iff {d : ℕ}
    (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous d)
    (x : AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N)) :
    ¬ IsZeroAt (evalHomogeneousAtSections (k := k) (projectiveSpaceTwist k N 1) F hF
        (projectiveSpaceCoordinate k N)) x ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) F := by
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp
    ((AlgebraicGeometry.Proj.projectiveGrading_iSup_basicOpen_X k N).ge (Set.mem_univ x))
  have hXm : ∀ j, MvPolynomial.X j ∈ AlgebraicGeometry.Proj.projectiveGrading k N 1 := fun j =>
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k j)
  set U : (AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N)).Opens :=
    AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X i) with hUdef
  have hU : ∀ y : U, MvPolynomial.X i ∉ y.1.asHomogeneousIdeal := fun y => y.2
  -- the frame `x_i` of `O(1)` on `U` and the coordinates `X_j / X_i`
  set s : Γ(projectiveSpaceTwist k N 1, U) :=
    homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X i) (hXm i) U with hsdef
  have hfr : IsFrame (projectiveSpaceTwist k N 1) U s :=
    isFrame_homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X i) (hXm i) U hU
  set r : Fin (N + 1) → Γ(AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N), U) := fun j =>
    divideSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X i) (hXm i) hU
      (homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X j) (hXm j) U) with hrdef
  have hf : ∀ j, (projectiveSpaceTwist k N 1).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (projectiveSpaceCoordinate k N j) = r j • s := by
    intro j
    have h1 := hfr.coord_smul_frame le_rfl
      (homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X j) (hXm j) U)
    rw [res_self, coord_homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X i) (hXm i) U hU]
      at h1
    exact h1.symm
  have hres := ProjectivizationChartLocalFormula.res_evalHomogeneousAtSections
    (projectiveSpaceTwist k N 1) F hF (projectiveSpaceCoordinate k N) U s r hf
  -- the coefficient `c = F(X_0/X_i, …, X_N/X_i)`
  set ψ : k →+* Γ(AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N), U) :=
    ((ProjectiveSpace N k).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom with hψdef
  set c : Γ(AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N), U) :=
    MvPolynomial.eval₂ ψ r F with hcdef
  -- Step 1: vanishing of `F(x)` at `x` ⟺ the germ of `c` lies in `𝔪_x`
  obtain ⟨Θ, hΘ⟩ := ProjectivizationChartLocalFormula.exists_stalkEquiv_monomialOn
    (projectiveSpaceTwist k N 1) U s hfr hxi d (fun _ => (0 : Fin (N + 1)))
  have key1 : IsZeroAt (evalHomogeneousAtSections (k := k) (projectiveSpaceTwist k N 1) F hF
      (projectiveSpaceCoordinate k N)) x ↔
      (ProjectiveSpace N k).presheaf.germ U x hxi c ∈
        IsLocalRing.maximalIdeal ((ProjectiveSpace N k).presheaf.stalk x) := by
    have e1 : IsZeroAt (evalHomogeneousAtSections (k := k) (projectiveSpaceTwist k N 1) F hF
        (projectiveSpaceCoordinate k N)) x ↔
        ((AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k N 1) d).presheaf.germ ⊤ x
            trivial (evalHomogeneousAtSections (k := k) (projectiveSpaceTwist k N 1) F hF
              (projectiveSpaceCoordinate k N)) :
          (AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k N 1) d).presheaf.stalk x) ∈
          (IsLocalRing.maximalIdeal ((ProjectiveSpace N k).presheaf.stalk x)) •
            (⊤ : Submodule ((ProjectiveSpace N k).presheaf.stalk x)
              ((AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k N 1) d).presheaf.stalk x)) :=
      Iff.rfl
    rw [e1, ← TopCat.Presheaf.germ_res_apply
      (AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k N 1) d).presheaf
      (homOfLE (le_top : U ≤ ⊤)) x hxi]
    rw [hres, germ_smul', mem_maximalIdeal_smul_top_iff_of_linearEquiv Θ, LinearEquiv.map_smul, hΘ, smul_eq_mul,
      mul_one]
  -- Step 2: the germ of `c` lies in `𝔪_x` ⟺ the value `c(x) ∈ A_{(𝔭_x)}` is not a unit
  have key2 : (ProjectiveSpace N k).presheaf.germ U x hxi c ∈
      IsLocalRing.maximalIdeal ((ProjectiveSpace N k).presheaf.stalk x) ↔ ¬ IsUnit (c.1 ⟨x, hxi⟩) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have key : (AlgebraicGeometry.Proj.stalkIso' (AlgebraicGeometry.Proj.projectiveGrading k N) x)
        ((ProjectiveSpace N k).presheaf.germ U x hxi c) = c.1 ⟨x, hxi⟩ :=
      AlgebraicGeometry.Proj.stalkIso'_germ (AlgebraicGeometry.Proj.projectiveGrading k N) U x hxi c
    constructor
    · intro h hu
      apply h
      have := hu.map (AlgebraicGeometry.Proj.stalkIso' (AlgebraicGeometry.Proj.projectiveGrading k N) x).symm
      rw [← key, RingEquiv.symm_apply_apply] at this
      exact this
    · intro h hu
      apply h
      convert hu.map (AlgebraicGeometry.Proj.stalkIso' (AlgebraicGeometry.Proj.projectiveGrading k N) x) using 1
      exact key.symm
  -- Step 3: the value of `c` at `x` is `(1/X_i)^d · (F/1)`
  have hev : IsUnit (c.1 ⟨x, hxi⟩) ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) F := by
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
    set L := Localization.AtPrime x.asHomogeneousIdeal.toIdeal with hLdef
    -- pointwise evaluation followed by `val` is a ring hom
    let ev : Γ(AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N), U) →+* L :=
      { toFun := fun t => (t.1 ⟨x, hxi⟩).val
        map_one' := HomogeneousLocalization.val_one
        map_mul' := fun a b => HomogeneousLocalization.val_mul _ _
        map_zero' := HomogeneousLocalization.val_zero
        map_add' := fun a b => HomogeneousLocalization.val_add _ _ }
    change IsUnit (ev c) ↔ _
    have hc : ev c = MvPolynomial.eval₂ (ev.comp ψ) (ev ∘ r) F := MvPolynomial.eval₂_comp_left ev ψ r F
    set u : L := Localization.mk 1 ⟨MvPolynomial.X i, hxi⟩ with hudef
    have hr' : ev ∘ r = fun j => u * (algebraMap (MvPolynomial (Fin (N + 1)) k) L ∘ MvPolynomial.X) j := by
      funext j
      show ((divideSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X i) (hXm i) hU
        (homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X j) (hXm j) U)).1
          ⟨x, hxi⟩).val = _
      rw [divideSection_val]
      show (Localization.mk (MvPolynomial.X j) 1 : L) * Localization.mk 1 ⟨MvPolynomial.X i, hxi⟩ = _
      rw [mul_comm, Localization.mk_one_eq_algebraMap]
      rfl
    have hφ : ∀ c₀ : k, (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom c₀) =
        AlgebraicGeometry.Proj.zeroToGlobal (AlgebraicGeometry.Proj.projectiveGrading k N)
          (algebraMap k (AlgebraicGeometry.Proj.projectiveGrading k N 0) c₀) := by
      intro c₀
      have h1 : (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
          AlgebraicGeometry.Proj.toSpecZero (AlgebraicGeometry.Proj.projectiveGrading k N) ≫
            AlgebraicGeometry.Spec.map (CommRingCat.ofHom
              (algebraMap k (AlgebraicGeometry.Proj.projectiveGrading k N 0))) := rfl
      rw [h1, AlgebraicGeometry.Scheme.Hom.comp_appTop, ← Category.assoc,
        ← AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality, Category.assoc, CommRingCat.hom_comp,
        RingHom.comp_apply]
      exact AlgebraicGeometry.Proj.toSpecZero_appTop_ΓSpecIso_inv (AlgebraicGeometry.Proj.projectiveGrading k N)
        (algebraMap k (AlgebraicGeometry.Proj.projectiveGrading k N 0) c₀)
    have hψ' : ev.comp ψ = (algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp MvPolynomial.C := by
      refine RingHom.ext fun c₀ => ?_
      show ((ψ c₀).1 ⟨x, hxi⟩).val = _
      have h2 : (ψ c₀).1 ⟨x, hxi⟩ =
          (AlgebraicGeometry.Proj.zeroToGlobal (AlgebraicGeometry.Proj.projectiveGrading k N)
            (algebraMap k (AlgebraicGeometry.Proj.projectiveGrading k N 0) c₀)).1 ⟨x, trivial⟩ := by
        rw [← hφ c₀]
        rfl
      rw [h2, AlgebraicGeometry.Proj.zeroToGlobal_apply_val, Localization.mk_one_eq_algebraMap,
        RingHom.comp_apply]
      congr 1
    rw [hc, hr', hψ', hF.eval₂_mul_left, ← MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eta]
    have hu : IsUnit u := by
      refine IsUnit.of_mul_eq_one (algebraMap (MvPolynomial (Fin (N + 1)) k) L (MvPolynomial.X i)) ?_
      rw [← Localization.mk_one_eq_algebraMap, hudef, Localization.mk_mul, one_mul, mul_one]
      exact Localization.mk_self ⟨MvPolynomial.X i, hxi⟩
    rw [IsUnit.mul_iff, IsLocalization.AtPrime.isUnit_to_map_iff L x.asHomogeneousIdeal.toIdeal]
    exact ⟨fun h => h.2, fun h => ⟨hu.pow d, h⟩⟩
  rw [key1, key2, not_not]
  exact hev

end ProjectiveSpace

/-- The form `F_j` as a global section of `O_{P¹}(1)^{⊗d}`. -/

noncomputable def ProjectiveLine.formSections {k : Type u} [Field k] [IsAlgClosed k] {N d : ℕ}
    (F : Fin (N + 1) → MvPolynomial (Fin 2) k) (hF : ∀ j, (F j).IsHomogeneous d) (j : Fin (N + 1)) :
    ((AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k 1 1) d).val.obj (Opposite.op ⊤) : Type u) :=
  evalHomogeneousAtSections (k := k) (projectiveSpaceTwist k 1 1) (F j) (hF j) (projectiveSpaceCoordinate k 1)

/-- For `k` algebraically closed, if the forms `F_j` have no common zero at `k`-points, then the sections
`formSections F hF j` do not vanish simultaneously at any point.

Proof. For a point `v` (relevant homogeneous prime `𝔭_v`) the projective Nullstellensatz gives `ℓ` with
`F_ℓ ∉ 𝔭_v` (`ProjectiveSpace.exists_notMem_asHomogeneousIdeal`), and `F_ℓ(x_0, x_1)` does not vanish at `v`
iff `v ∈ D₊(F_ℓ)` (`ProjectiveSpace.not_isZeroAt_evalHomogeneousAtSections_coordinate_iff`, the degree-`d`
version of Stacks 01MW(5)). No identification of closed points with `k`-points is needed. -/
theorem ProjectiveLine.formSections_not_all_isZeroAt {k : Type u} [Field k] [IsAlgClosed k] {N d : ℕ}
    (F : Fin (N + 1) → MvPolynomial (Fin 2) k) (hF : ∀ j, (F j).IsHomogeneous d)
    (hF0 : ∀ v : Fin 2 → k, v ≠ 0 → ∃ j, MvPolynomial.eval v (F j) ≠ 0) :
    ∀ v, ∃ ℓ, ¬ IsZeroAt (ProjectiveLine.formSections F hF ℓ) v := by
  intro v
  obtain ⟨ℓ, hℓ⟩ := ProjectiveSpace.exists_notMem_asHomogeneousIdeal F hF0 v
  exact ⟨ℓ, (ProjectiveSpace.not_isZeroAt_evalHomogeneousAtSections_coordinate_iff (F ℓ) (hF ℓ) v).mpr hℓ⟩

noncomputable def ProjectiveLine.morphismOfForms {k : Type u} [Field k] [IsAlgClosed k] {N d : ℕ}
    (F : Fin (N + 1) → MvPolynomial (Fin 2) k) (hF : ∀ j, (F j).IsHomogeneous d)
    (hF0 : ∀ v : Fin 2 → k, v ≠ 0 → ∃ j, MvPolynomial.eval v (F j) ≠ 0) :
    ProjectiveLine k ⟶ ProjectiveSpace N k :=
  projectivizationMorphism (k := k)
    (AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k 1 1) d)
    (ProjectiveLine.formSections F hF)
    (ProjectiveLine.formSections_not_all_isZeroAt F hF hF0)

end
