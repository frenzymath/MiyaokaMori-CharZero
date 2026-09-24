import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationEpi
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus

/-! # The germ of an evaluated section is not in the maximal ideal times the stalk

For an arbitrary graded quasi-coherent algebra: on the relative Proj `π : Proj_X 𝒜 → X`, let `U ⊆ X` be affine,
`a ∈ Γ(U, 𝒜_m)`, and `y ∈ π⁻¹U` a point whose chart image `φ_U(y) ∈ Proj A(U)` (Stacks 01NQ,
`relativeProj.affineIso`) does **not** contain `a` (as the element `sectionsOf a ∈ A(U)_m` of the section ring).
Then the germ at `y` of the local evaluation `evaluationLocal 𝒜 m U a ∈ Γ(π⁻¹U, O(m))` ("`a/1`") is **not**
in `𝔪_y · O(m)_y`.

Source: Stacks 01MW(5) (`x_f` generates `O(d)` on `D₊(f)`), 01NQ, 01NR; the proof of Proposition 2.4 of the paper (coordinate sections and coordinate divisors).

Proof. `isFrame_evaluationLocal'` (below): `evaluationLocal 𝒜 m U a`, restricted to the chart basic open
`V_a = ι(φ_U⁻¹ D₊(a))` (`chartBasicOpen`), is a frame of `O(m)` — the degree-`m` version of
`relativeProj.isFrame_evaluationLocal` (`RelativeProjEvaluationEpi`, degree 1), proved by the same five steps:
`f/1` is a frame of `O_{Proj A(U)}(m)` on `D₊(f)` (`isFrame_homogeneousSection`, any degree),
frames are preserved along `restrict φ_U`, `restrictFunctorIsoPullback`, `twistAffineIso⁻¹` and
`restrictAppIso`, and `evaluationLocal_eq` identifies the resulting section. Then `y ∈ V_a` (`mem_chartBasicOpen`
with `Proj.mem_basicOpen`), the germ of a frame is not in `𝔪_y · stalk` (`IsFrame.germ_notMem_maximalIdeal_smul`,
one-generator Nakayama), and the germ over `π⁻¹U` equals the germ over `V_a` of the restriction
(`TopCat.Presheaf.germ_res_apply`).

Edge cases: `m = 0` allowed (`O(0)`, `a/1` a unit on `D₊(a)`); `kk`, weights irrelevant here; `U = ⊥` has no `y`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `a ∈ Γ(U, 𝒜_m)`: `evaluationLocal 𝒜 m U a` restricted to `V_a = chartBasicOpen 𝒜 m U a` is a frame of
`O(m)`. Degree-`m` version of `relativeProj.isFrame_evaluationLocal` (`RelativeProjEvaluationEpi`), same proof:
(i) `x_a|_{D₊(a)}` is a frame of `O_{Proj A(U)}(m)` (`isFrame_homogeneousSection`);
(ii) transport along `restrict φ_U` and `restrictFunctorIsoPullback` (the pullback adjunction unit is the
`restrict` adjunction unit followed by this iso, Mathlib `Adjunction.unit_leftAdjointUniq_hom_app`);
(iii) transport along `twistAffineIso⁻¹`; (iv) `restrictAppIso`: sections of `O(m)|_{π⁻¹U}` on `φ_U⁻¹D₊(a)` are
sections of `O(m)` on `V_a`; (v) `evaluationLocal_eq` + `res_res`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.isFrame_evaluationLocal'
    {X : AlgebraicGeometry.Scheme.{u}} (𝒜 : X.GradedQCAlgebra) (m : ℕ) (U : X.affineOpens)
    (a : Γ(𝒜.part m, U.1)) :
    AlgebraicGeometry.Scheme.Modules.IsFrame (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 (m : ℤ))
      (AlgebraicGeometry.Scheme.relativeProj.chartBasicOpen 𝒜 m U a)
      ((AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 (m : ℤ)).res
        (AlgebraicGeometry.Scheme.relativeProj.chartBasicOpen_le 𝒜 m U a)
        (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal 𝒜 m U a)) := by
  let φ := (AlgebraicGeometry.Scheme.relativeProj.affineIso 𝒜 U).hom
  let ι := ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ U.1).ι
  let G := AlgebraicGeometry.Proj.twist (𝒜.sectionsGrading U.1) (m : ℤ)
  let T := AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 (m : ℤ)
  let a' := 𝒜.sectionsOf U.1 m a
  let D := AlgebraicGeometry.Proj.basicOpen (𝒜.sectionsGrading U.1) a'.1
  let s : Γ(G, ⊤) := AlgebraicGeometry.Proj.twistSection (𝒜.sectionsGrading U.1) a'.1 a'.2
  have hDtop : φ ⁻¹ᵁ D ≤ φ ⁻¹ᵁ ⊤ := φ.preimage_mono le_top
  -- (i)
  have hD : AlgebraicGeometry.Scheme.Modules.IsFrame G D (G.res le_top s) :=
    MiyaokaMori.WeightedJets.ProjTwisting.isFrame_homogeneousSection (𝒜.sectionsGrading U.1) m
      a'.1 a'.2 D (fun x => x.2)
  -- (ii)
  have hR : AlgebraicGeometry.Scheme.Modules.IsFrame (G.restrict φ) (φ ⁻¹ᵁ D)
      ((G.restrictAppIso φ (φ ⁻¹ᵁ D)).inv (G.res (φ.image_preimage_le D) (G.res le_top s))) :=
    (hD.restrict (φ.image_preimage_le D)).restrictAppIso_inv_of_image φ
  let e₁ := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback φ).app G
  have hP := hR.map_iso e₁
  let u : Γ((AlgebraicGeometry.Scheme.Modules.pullback φ).obj G, φ ⁻¹ᵁ ⊤) :=
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app G).app ⊤).hom s
  have hu : u = e₁.hom.app (φ ⁻¹ᵁ ⊤)
      ((G.restrictAppIso φ (φ ⁻¹ᵁ ⊤)).inv (G.res (φ.image_preimage_le ⊤) s)) := by
    have h1 := CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
      (AlgebraicGeometry.Scheme.Modules.restrictAdjunction φ)
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction φ) G
    have h2 := congrArg (fun ψ => ψ.app ⊤ s) h1
    simp only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
      AlgebraicGeometry.Scheme.Modules.pushforward_map_app,
      AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app] at h2
    exact h2.symm
  have hu' : ((AlgebraicGeometry.Scheme.Modules.pullback φ).obj G).res hDtop u =
      e₁.hom.app (φ ⁻¹ᵁ D)
        ((G.restrictAppIso φ (φ ⁻¹ᵁ D)).inv (G.res (φ.image_preimage_le D) (G.res le_top s))) := by
    rw [hu, ← AlgebraicGeometry.Scheme.Modules.Hom.app_res]
    rfl
  rw [← hu'] at hP
  -- (iii)
  let e₂ := AlgebraicGeometry.Scheme.relativeProj.twistAffineIso 𝒜 U (m : ℤ)
  have hQ := hP.map_iso e₂.symm
  rw [CategoryTheory.Iso.symm_hom, AlgebraicGeometry.Scheme.Modules.Hom.app_res] at hQ
  -- (iv)
  have hT := hQ.restrictAppIso_hom_of_restrict ι
  -- (v)
  have heq : (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 (m : ℤ)).res
      (AlgebraicGeometry.Scheme.relativeProj.chartBasicOpen_le 𝒜 m U a)
      (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal 𝒜 m U a) =
      (T.restrictAppIso ι (φ ⁻¹ᵁ D)).hom
        ((T.restrict ι).res hDtop (e₂.inv.app (φ ⁻¹ᵁ ⊤) u)) := by
    rw [AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq]
    exact AlgebraicGeometry.Scheme.Modules.res_res T _ _ _
  rw [heq]
  exact hT

/-- **The germ of `a/1` at a point of `D₊(a)` is not in `𝔪_y · O(m)_y`** (Stacks 01MW(5) transported to the
relative Proj along 01NQ/01NR). `y ∈ π⁻¹U`, and `a ∈ A(U)_m` is not in the homogeneous prime of the chart image
`φ_U(y)`; then the germ at `y` of `evaluationLocal 𝒜 m U a ∈ Γ(π⁻¹U, O(m))` is not in `𝔪_y • ⊤`.

Proof: `y ∈ V_a` (`mem_chartBasicOpen`, `Proj.mem_basicOpen`); `evaluationLocal a|_{V_a}` is a frame
(`isFrame_evaluationLocal'`); the germ of a frame is not in `𝔪_y • ⊤` (`IsFrame.germ_notMem_maximalIdeal_smul`);
germ over `π⁻¹U` = germ over `V_a` of the restriction (`germ_res_apply`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.germ_evaluationLocal_notMem_maximalIdeal_smul
    {X : AlgebraicGeometry.Scheme.{u}} (𝒜 : X.GradedQCAlgebra) (m : ℕ) (U : X.affineOpens)
    (a : Γ(𝒜.part m, U.1)) (y : (AlgebraicGeometry.Scheme.relativeProj 𝒜).left)
    (hy : y ∈ (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ U.1)
    (ha : ((𝒜.sectionsOf U.1 m a : 𝒜.sectionsGrading U.1 m) : 𝒜.sectionsRing U.1) ∉
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso 𝒜 U).hom ⟨y, hy⟩).asHomogeneousIdeal) :
    (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 (m : ℤ)).presheaf.germ
        ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ U.1) y hy
        (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal 𝒜 m U a) ∉
      (IsLocalRing.maximalIdeal ((AlgebraicGeometry.Scheme.relativeProj 𝒜).left.presheaf.stalk y)) •
        (⊤ : Submodule ((AlgebraicGeometry.Scheme.relativeProj 𝒜).left.presheaf.stalk y)
          ((AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 (m : ℤ)).stalk y)) := by
  have hyV : y ∈ AlgebraicGeometry.Scheme.relativeProj.chartBasicOpen 𝒜 m U a :=
    AlgebraicGeometry.Scheme.relativeProj.mem_chartBasicOpen 𝒜 m U a y hy
      ((AlgebraicGeometry.Proj.mem_basicOpen _ _ _).mpr ha)
  have hfr := AlgebraicGeometry.Scheme.relativeProj.isFrame_evaluationLocal' 𝒜 m U a
  intro hmem
  refine hfr.germ_notMem_maximalIdeal_smul hyV ?_
  rw [AlgebraicGeometry.Scheme.Modules.res, TopCat.Presheaf.germ_res_apply]
  exact hmem

end
