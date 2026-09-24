import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveSpaceIsIntegral

/-! # Chart-level facts about the relative Proj of a locally weighted polynomial algebra

Chart-level facts about the relative Proj of a graded algebra `S` that is locally the weighted
polynomial algebra (atlas `𝒜 : S.WeightedPolynomialAtlas w`), used to show that such a relative
Proj is integral:

1. `MvPolynomial.exists_retraction_fromZeroRingHom_comp_algebraMap`: for the weighted grading `𝒜` of `R[x_σ]`
   and a variable `x_{i₀}`, the ring map `R → 𝒜₀ → (R[x_σ]_{x_{i₀}})₀` has a ring-theoretic retraction
   (evaluate `x_k ↦ 0` for `k ≠ i₀`, `x_{i₀} ↦ 1`; this is well defined on the localisation since `x_{i₀}` becomes a unit).
2. `MvPolynomial.weightedProj_toSpecZero_comp_surjective`: the structure morphism
   `Proj R[x_σ]_w → Spec 𝒜₀ → Spec R` is surjective on points (σ nonempty, weights positive): it has a section over
   the affine chart `D_+(x_{i₀}) = Spec (R[x_σ]_{x_{i₀}})₀` (Mathlib `Proj.awayι`, `Proj.awayι_toSpecZero`), namely
   `Spec` of the retraction of 1. (Stacks 00HQ would give this from faithful flatness; the retraction is more direct.)
3. `WeightedPolynomialAtlas.projToOpen_surjective`: the chart structure map `Proj S(U_i) → U_i` is surjective
   (transport 2 along `projIso : Proj S(U_i) ≅ Proj Γ(X,U_i)[x_σ]_w`, `projIso_hom_weightedProjToOpen`).
4. `WeightedPolynomialAtlas.proj_isIntegral`: if `Γ(X, U_i)` is a domain, `Proj S(U_i)` is an integral scheme
   (`Proj.isIntegral_of_isDomain` for `Γ(X,U_i)[x_σ]` with the positive-degree nonzero homogeneous element `x_{i₀}`,
   transported along `projIso`).

References: Stacks 01NE (`D_+(f) = Spec A_(f)`), 01OA.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MvPolynomial

variable {R : Type u} [CommRing R] {σ : Type u} (w : σ → ℕ)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The composite `R → 𝒜₀ → (R[x_σ]_{x_{i₀}})₀` (weighted grading `𝒜`) has a ring-theoretic retraction:
evaluation `x_{i₀} ↦ 1`, `x_k ↦ 0` (`k ≠ i₀`), which is defined on the localisation since `x_{i₀}` maps to a unit,
restricted to the degree-zero homogeneous localisation via `HomogeneousLocalization.val`. -/
theorem exists_retraction_fromZeroRingHom_comp_algebraMap (i₀ : σ) :
    ∃ ψ : HomogeneousLocalization.Away (weightedHomogeneousSubmodule R w) (X i₀) →+* R,
      ψ.comp ((HomogeneousLocalization.fromZeroRingHom (weightedHomogeneousSubmodule R w)
        (Submonoid.powers (X i₀))).comp
          (algebraMap R (weightedHomogeneousSubmodule R w 0))) = RingHom.id R := by
  classical
  let 𝒜 := weightedHomogeneousSubmodule R w
  let g : MvPolynomial σ R →+* R := MvPolynomial.eval (fun k => if k = i₀ then (1 : R) else 0)
  have hg : IsUnit (g (X i₀)) := by simp [g]
  let L : Localization.Away (X i₀ : MvPolynomial σ R) →+* R := IsLocalization.Away.lift (X i₀) hg
  let v : HomogeneousLocalization.Away 𝒜 (X i₀) →+* Localization.Away (X i₀ : MvPolynomial σ R) :=
    { toFun := HomogeneousLocalization.val
      map_one' := HomogeneousLocalization.val_one
      map_mul' := HomogeneousLocalization.val_mul
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
  refine ⟨L.comp v, ?_⟩
  ext r
  have hval : v (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (X i₀))
      (algebraMap R (𝒜 0) r)) =
      algebraMap (MvPolynomial σ R) (Localization.Away (X i₀ : MvPolynomial σ R)) (C r) := by
    change HomogeneousLocalization.val (HomogeneousLocalization.mk
      ⟨0, algebraMap R (𝒜 0) r, 1, one_mem _⟩) = _
    rw [HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap]
    congr 1
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [hval]
  simp [L, g]

/-- The structure morphism `Proj R[x_σ]_w → Spec 𝒜₀ → Spec R` is surjective on points when `σ` is nonempty
and all weights are positive: over `D_+(x_{i₀})` it is `Spec` of `R → (R[x_σ]_{x_{i₀}})₀`, which has a
retraction (`exists_retraction_fromZeroRingHom_comp_algebraMap`), hence a section. -/
theorem weightedProj_toSpecZero_comp_surjective [Nonempty σ] (hw : ∀ i, 0 < w i) :
    Function.Surjective (AlgebraicGeometry.Proj.toSpecZero (weightedHomogeneousSubmodule R w) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (weightedHomogeneousSubmodule R w 0)))).base := by
  classical
  let i₀ : σ := Classical.choice inferInstance
  obtain ⟨ψ, hψ⟩ := exists_retraction_fromZeroRingHom_comp_algebraMap (R := R) w i₀
  let 𝒜 := weightedHomogeneousSubmodule R w
  have hX : X i₀ ∈ 𝒜 (w i₀) :=
    (mem_weightedHomogeneousSubmodule R w _ _).mpr (isWeightedHomogeneous_X R w i₀)
  let φ : R →+* HomogeneousLocalization.Away 𝒜 (X i₀) :=
    (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (X i₀))).comp (algebraMap R (𝒜 0))
  have h1 : AlgebraicGeometry.Proj.awayι 𝒜 (X i₀) hX (hw i₀) ≫
      (AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) := by
    rw [← Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero, ← AlgebraicGeometry.Spec.map_comp]
    rfl
  have h2 : AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) = 𝟙 _ := by
    rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_id,
      AlgebraicGeometry.Spec.map_id]
  intro x
  refine ⟨(AlgebraicGeometry.Proj.awayι 𝒜 (X i₀) hX (hw i₀))
    ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ)) x), ?_⟩
  change (AlgebraicGeometry.Proj.awayι 𝒜 (X i₀) hX (hw i₀) ≫
    (AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))))
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ)) x) = x
  rw [h1, ← AlgebraicGeometry.Scheme.Hom.comp_apply, h2]
  rfl

end MvPolynomial

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

variable {X : AlgebraicGeometry.Scheme.{u}} {S : X.GradedAffineAlgebra}
variable {σ : Type u} {w : σ → ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The chart structure map `Proj S(U_i) → U_i` of a weighted-polynomial atlas is surjective on points
(σ nonempty, positive weights): transport `weightedProj_toSpecZero_comp_surjective` along `projIso`. -/
theorem projToOpen_surjective (𝒜 : S.WeightedPolynomialAtlas w) [Nonempty σ] (hw : ∀ i, 0 < w i)
    (i : 𝒜.I) : Function.Surjective (S.projToOpen (𝒜.chart i)).base := by
  rw [← 𝒜.projIso_hom_weightedProjToOpen i]
  intro x
  obtain ⟨y, hy⟩ := MvPolynomial.weightedProj_toSpecZero_comp_surjective w hw
    ((𝒜.chart i).2.isoSpec.hom x)
  refine ⟨(𝒜.projIso i).inv y, ?_⟩
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]
  unfold weightedProjToOpen
  rw [← Category.assoc, AlgebraicGeometry.Scheme.Hom.comp_apply]
  change (𝒜.chart i).2.isoSpec.inv ((AlgebraicGeometry.Proj.toSpecZero _ ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Γ(X, (𝒜.chart i).toOpens) _))).base y) = x
  rw [hy, ← AlgebraicGeometry.Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- If `Γ(X, U_i)` is a domain, the chart `Proj S(U_i)` of a weighted-polynomial atlas (σ nonempty, positive
weights) is an integral scheme: `Proj Γ(X,U_i)[x_σ]_w` is integral by `Proj.isIntegral_of_isDomain`
(`x_{i₀}` is a nonzero homogeneous element of positive degree `w i₀`), and `projIso` transports it. -/
theorem proj_isIntegral (𝒜 : S.WeightedPolynomialAtlas w) [Nonempty σ] (hw : ∀ i, 0 < w i) (i : 𝒜.I)
    [IsDomain Γ(X, (𝒜.chart i).toOpens)] :
    AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Proj (S.grading (𝒜.chart i))) := by
  let i₀ : σ := Classical.choice inferInstance
  have hX : MvPolynomial.X i₀ ∈ MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w (w i₀) :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ w _ _).mpr (MvPolynomial.isWeightedHomogeneous_X _ w i₀)
  have : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Proj
      (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w)) :=
    AlgebraicGeometry.Proj.isIntegral_of_isDomain _ ⟨w i₀, MvPolynomial.X i₀, hw i₀, hX, MvPolynomial.X_ne_zero i₀⟩
  exact AlgebraicGeometry.IsIntegral.of_isIso (𝒜.projIso i).inv

end AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

end
