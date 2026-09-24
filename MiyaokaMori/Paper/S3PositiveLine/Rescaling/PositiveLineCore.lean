import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveToCurveFinite
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.DegreeRelation
import MiyaokaMori.Paper.S3PositiveLine.Realization.ExcludeScalarJets
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.GeneralFiberAvoidsFiniteSet
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.HorizontalCurve
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.NegativeCurveViaFibrationYGG
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.NegativeSlope
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.NormalizationOfIntegralCurve
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PolarizationPullback
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.PositiveLineArithmetic
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCoreWeightedRescaling
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetOfAffineJet
import MiyaokaMori.Paper.S2WeightedJets.Cone.PullbackDegreeDimPos
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.PullbackDegreeFiniteCover
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.PullbackPointDegreeHorizontal
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.ShiftedClassLineBundle
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.TauMorphism
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.ThetaShiftNegative
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.YggGeometry

/-! # The core of the positive line: a based jet on a line bundle of positive slope

Statement: given a nonconstant map and positive degree of the pulled-back tangent bundle, construct a
finite cover, a line bundle and a based jet satisfying the normalization / generically-non-scalar
conditions and the strict slope lower bound.

Source: §2.4 and §3 of the paper. The proof is split into three statements, and this file follows that split:
* Lemma 2.5 of the paper (a negative horizontal curve)
  → `negative_horizontal_curve`;
* Lemma 3.1 of the paper (an affine lift after finite base change)
  → `weighted_rescaling` (its two halves are in `PositiveLineCoreWeightedRescaling_AffineJet` and
  `BasedJetOfAffineJet`);
* Proposition 3.2 of the paper (tautological identification, the degree)
  → assembled here in `positive_line_core` from `tau_pullback_polarization`, `degree_relation` and the slope
  inequality of the negative horizontal curve; the exclusion of generically scalar jets
  is `not_genericallyScalar_of_degree_pos`, which needs `deg L > 0` — a consequence of the slope bound.
  This order (slope first, then non-scalarity) is the paper's.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `FiniteCover.degree ρ` (the authors' `finiteMapFunctionFieldDegree`) agrees with
`functionFieldDegree ρ.hom` (the residue-field degree at the generic point). Both are
`[K(C̃) : K(C)]`: `functionFieldDegree_eq_finrank` identifies the second with a `finrank` for the
algebra structure through the residue field at the generic point, and the two algebra structures
on `K(C̃)` over `K(C)` agree because `dominantFunctionFieldMap` factors through the residue map.
Same proof as the private lemma `functionFieldDegree_eq_finiteMapFunctionFieldDegree` in
`PullbackDegreeFiniteCover`, made public here because the assembly of `positive_line_core`
needs it (degree_relation speaks about `functionFieldDegree ρ.hom`, the target about `ρ.degree`). -/
theorem FiniteCover.degree_eq_functionFieldDegree {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (ρ : FiniteCover k C) :
    ρ.degree = functionFieldDegree ρ.hom := by
  have hff := functionFieldDegree_eq_finrank ρ.hom ρ.hom_genericPoint
  unfold FiniteCover.degree AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree
  rw [hff]
  let A1 : Algebra C.toScheme.functionField ρ.source.toScheme.functionField :=
    @AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra ρ.source.toScheme C.toScheme
      ρ.source.isIntegral C.isIntegral ρ.hom inferInstance
  let A2 : Algebra C.toScheme.functionField ρ.source.toScheme.functionField :=
    ((C.toScheme.functionFieldIsoResidueField.hom ≫
      (C.toScheme.residueFieldCongr ρ.hom_genericPoint.symm).hom ≫
      ρ.hom.residueFieldMap (genericPoint ρ.source.toScheme) ≫
      ρ.source.toScheme.functionFieldIsoResidueField.inv).hom.toAlgebra)
  have hmap : AlgebraicGeometry.Scheme.dominantFunctionFieldMap ρ.hom =
      C.toScheme.functionFieldIsoResidueField.hom ≫
        (C.toScheme.residueFieldCongr ρ.hom_genericPoint.symm).hom ≫
        ρ.hom.residueFieldMap (genericPoint ρ.source.toScheme) ≫
        ρ.source.toScheme.functionFieldIsoResidueField.inv := by
    unfold AlgebraicGeometry.Scheme.dominantFunctionFieldMap
    apply (cancel_mono (ρ.source.toScheme.residue (genericPoint ρ.source.toScheme))).1
    simp only [Category.assoc]
    rw [← AlgebraicGeometry.Scheme.residue_residueFieldMap]
    rw [← Category.assoc]
    rw [← AlgebraicGeometry.Scheme.residue_residueFieldCongr]
    simp [AlgebraicGeometry.Scheme.functionFieldIsoResidueField]
    exact ρ.hom_genericPoint.symm
  have hA : A2 = A1 := by
    apply Algebra.algebra_ext
    intro r
    change ((C.toScheme.functionFieldIsoResidueField.hom ≫
      (C.toScheme.residueFieldCongr ρ.hom_genericPoint.symm).hom ≫
      ρ.hom.residueFieldMap (genericPoint ρ.source.toScheme) ≫
      ρ.source.toScheme.functionFieldIsoResidueField.inv).hom r) =
      (AlgebraicGeometry.Scheme.dominantFunctionFieldMap ρ.hom).hom r
    exact congrArg (fun q => q.hom r) hmap.symm
  change @Module.finrank C.toScheme.functionField ρ.source.toScheme.functionField _ _
      (@Algebra.toModule _ _ _ _ A1) =
    @Module.finrank C.toScheme.functionField ρ.source.toScheme.functionField _ _
      (@Algebra.toModule _ _ _ _ A2)
  rw [hA]

/-- **A negative horizontal curve** (Lemma 2.5 of the paper;
§3 of the paper). Data: `n := X.dim`, `d := deg f^*T_X > 0`, `κ ≥ 1`,
`θ := d h_κ / (2(n+1)κ)`. Conclusion: a sufficiently divisible `m` (every weight `q ≤ κ` divides
`m`, so `B_κ = polarization f κ m` is a line bundle), an integral curve `Γ ⊂ Y_κ^GG`, and the
normalization `ν : C̃₀ → Γ` (finite, birational, generic point to generic point, a `k`-morphism
after composing with `Γ.ι`) such that `ρ₀ := ν ≫ Γ.ι ≫ π_κ : C̃₀ → C` is finite, surjective, sends the
generic point to the generic point, and
`θ < -(Γ · B_κ) / (m · deg ρ₀)`, i.e. `-(H_κ · Γ)/e₀ > θ` with `H_κ · Γ := Γ.degree B_κ / m`
(2.11).

Proof (every step names its lemma):
1. `n ≥ 1`: if `n = 0` then `T_X` has rank `0`, so `f^*T_X` has rank `0` and degree `0`, contradicting
   `hd` (§2.1 of the paper; `SmoothProjectiveVariety.one_le_dim_of_pullbackDegree_ne_zero`).
2. `m := (n+1) κ · jetWeight κ`: every `q ≤ κ` divides `m` (`YGG.dvd_of_dvd_mul_jetWeight`) and
   `(jetAlgebra f κ).SufficientlyDivisible m` (`YGG.sufficientlyDivisible`, :
   the jet algebra is locally a weighted polynomial algebra with weights `1..κ`, and
   `veronese_generation_multiple` gives generation of the `m`-th Veronese in degree one,
   §2.1 of the paper).
3. Geometry of `Y_κ^GG` : `π_κ` is proper (locally on `C` it is `U × P(w) → U`),
   so `Y_κ^GG` is proper over `k` (`YGG.isProperOver`), its fibers are proper over the residue fields
   (`YGG.fiber_isProperOver`), and it is projective over `k` (`YGG.isProjectiveOver`).
4. `YGG.isIntegral`, `YGG.dimension_eq` (`ykGG_integral_normal_projective`): `IsIntegral (Y_κ^GG)` and
   `(Y_κ^GG).dimension = (n+1) κ`.
5. Choose a closed point `p₀ ∈ C` (`exists_closedPoint_mem_open` with `V = ⊤`). Write `θ = a/b` with
   `a b : ℕ`, `0 < b` (`θ > 0` by `positive_line_threshold_pos`; `a := θ.num.toNat`, `b := θ.den`).
   `theta_shift_top_self_intersection_neg` gives `(H'_κ)^{(n+1)κ} < 0` for
   `H'_κ = tautClass + θ • π_κ^*[p₀]`; `shiftedBundle_ratDivisorOp` writes `(m b) • H'_κ` as the
   class of the line bundle `M := shiftedBundle f κ m p₀ a b`.
6. `exists_integralCurve_shiftedBundle_degree_neg`  gives
   `Γ : IntegralCurve k (Y_κ^GG)` with `Γ.degree M < 0`.
7. `horizontal_of_shifted_degree_neg` : `g := Γ.ι ≫ π_κ` is surjective onto
   `C`; a surjective morphism of integral schemes is dominant, so it sends the generic point of `Γ` to
   the generic point of `C` (`AlgebraicGeometry.Scheme.dominantMap_genericPoint`).
8. `isFinite_and_functionFieldDegree_pos_of_curve_to_curve` : `g` is
   finite and `e₀ := functionFieldDegree g > 0`. `degree_pullback_point_eq_functionFieldDegree`
   : `Γ.degree (π_κ^* O_C(p₀)) = e₀`.
   `negative_slope`  then gives `a/b < -(Γ.degree B_κ)/(m e₀)`.
9. `Γ.carrier` is projective over `k` (`IsProjectiveOver.of_isClosedImmersion` from 3.), integral and
   one-dimensional; `exists_normalization_of_integralCurve`
   gives `C̃₀` and `ν` finite, surjective, `k`-linear, generic point to generic point, with
   `functionFieldDegree ν = 1`. Hence `ν ≫ Γ.ι` is a `k`-morphism, `ρ₀ := ν ≫ g` is finite (composition
   of finite morphisms), surjective, sends generic point to generic point, and by
   `functionFieldDegree_comp_of_genericPoint` its function-field degree is `1 · e₀ = e₀`.
   Substituting in 8. gives the stated inequality. ∎ -/
theorem negative_horizontal_curve {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f]
    (hd : 0 < TangentBundle.pullbackDegree f) (κ : ℕ) (hκ : 1 ≤ κ) :
    ∃ (m : ℕ) (hSD : (jetAlgebra f κ).SufficientlyDivisible m) (_ : ∀ q ∈ Finset.Icc 1 κ, q ∣ m)
      (Γ : IntegralCurve k (YGG f κ)) (Ct₀ : SmoothProjectiveCurve k)
      (ν : Ct₀.toScheme ⟶ Γ.carrier)
      (_ : AlgebraicGeometry.IsFinite ν)
      (_ : ν.base (genericPoint Ct₀.toScheme) = genericPoint Γ.carrier)
      (_ : functionFieldDegree ν = 1)
      (_ : (ν ≫ Γ.ι).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (_ : AlgebraicGeometry.IsFinite (ν ≫ Γ.ι ≫ YGG.proj f κ))
      (_ : Function.Surjective (ν ≫ Γ.ι ≫ YGG.proj f κ).base)
      (_ : (ν ≫ Γ.ι ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme),
      haveI : Fact ((jetAlgebra f κ).SufficientlyDivisible m) := ⟨hSD⟩
      ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ) / (2 * ((X.toVariety.dim : ℚ) + 1) * κ)
        < - (Γ.degree (polarization f κ m) : ℚ)
            / ((m : ℚ) * (functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) : ℚ)) := by
  -- Step 1: n ≥ 1
  set n : ℕ := X.toVariety.dim with hn
  have hn1 : 1 ≤ n :=
    SmoothProjectiveVariety.one_le_dim_of_pullbackDegree_ne_zero f (ne_of_gt hd)
  have hnX : X.toVariety.dim = n := rfl
  -- Step 2: the sufficiently divisible m
  let m : ℕ := (n + 1) * κ * jetWeight κ
  have hm : 0 < m := by
    letI : Nonempty (ULift.{u} (Fin (n + 1) × Fin κ)) :=
      ⟨ULift.up ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
    have h := veroneseDegree_pos (σ := ULift.{u} (Fin (n + 1) × Fin κ)) κ
    simpa [m, Fintype.card_ulift, Fintype.card_prod, Fintype.card_fin] using h
  have hmdiv : (n + 1) * κ * jetWeight κ ∣ m := dvd_rfl
  have hSD : (jetAlgebra f κ).SufficientlyDivisible m :=
    YGG.sufficientlyDivisible f hnX κ hκ m hm hmdiv
  have hdiv : ∀ q ∈ Finset.Icc 1 κ, q ∣ m := YGG.dvd_of_dvd_mul_jetWeight n κ m hmdiv
  haveI hFact : Fact ((jetAlgebra f κ).SufficientlyDivisible m) := ⟨hSD⟩
  -- Steps 3, 4: geometry of Y_κ^GG
  haveI hint : AlgebraicGeometry.IsIntegral (YGG f κ) := YGG.isIntegral f hnX κ hκ
  have hY : IsProperOver k (YGG f κ) := YGG.isProperOver f hnX κ
  have hs : (YGG f κ).dimension = (n + 1) * κ := YGG.dimension_eq f hnX κ hκ
  have hYproj : IsProjectiveOver k (YGG f κ) := YGG.isProjectiveOver f hnX κ hκ
  -- Step 5: a closed point p₀ and θ = a / b
  obtain ⟨p₀, -, hp₀⟩ := exists_closedPoint_mem_open (C := C) isOpen_univ Set.univ_nonempty
  have hfib := YGG.fiber_isProperOver f hnX κ p₀
  set θ : ℚ := ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ)
    / (2 * ((n : ℚ) + 1) * κ) with hθ
  have hθpos : 0 < θ := positive_line_threshold_pos f hd κ hκ
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ((a : ℤ) : ℚ) = (θ.num : ℚ) :=
    ⟨θ.num.toNat, by rw [Int.toNat_of_nonneg (Rat.num_nonneg.mpr hθpos.le)]⟩
  set b : ℕ := θ.den with hb
  have hbpos : 0 < b := θ.den_pos
  have hθab : θ = (a : ℚ) / (b : ℚ) := by
    rw [← Int.cast_natCast (R := ℚ) a, ha, hb]
    exact (Rat.num_div_den θ).symm
  obtain ⟨-, hneg⟩ := theta_shift_top_self_intersection_neg f κ m hκ p₀ hp₀ n hnX hn1
    (TangentBundle.pullbackDegree f) hd rfl hm hmdiv hY hs hfib
  have hDL := shiftedBundle_ratDivisorOp f κ m hm p₀ a b hbpos
  rw [← hθab] at hDL
  -- Step 6: the negative integral curve Γ
  obtain ⟨Γ, hΓ⟩ := MiyaokaMori.FiberedNegativeCurve.exists_integralCurve_shiftedBundle_degree_neg
    f κ m hY p₀ hp₀ a b hbpos
    (tautClass f κ m + θ • ratPullbackOp (YGG.proj f κ) (Divisor.ofPoint p₀)) (m * b)
    (Nat.mul_pos hm hbpos) hDL ((n + 1) * κ) hs hneg
  -- Step 7: Γ is horizontal
  obtain ⟨-, hsurjΓ⟩ := horizontal_of_shifted_degree_neg f κ m p₀ a b hbpos Γ hΓ
  let g : Γ.carrier ⟶ C.toScheme := Γ.ι ≫ YGG.proj f κ
  letI : AlgebraicGeometry.IsDominant g := ⟨hsurjΓ.denseRange⟩
  have hgΓ : g.base (genericPoint Γ.carrier) = genericPoint C.toScheme :=
    AlgebraicGeometry.Scheme.dominantMap_genericPoint g
  -- Step 8: e₀ = Γ.degree (π^* O(p₀)) > 0 and the slope inequality for Γ
  letI : (YGG.proj f κ).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  letI : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨Category.assoc _ _ _⟩
  obtain ⟨hgfin, he₀pos⟩ := isFinite_and_functionFieldDegree_pos_of_curve_to_curve Γ.carrier
    Γ.isProperOver Γ.dim_eq_one g hgΓ
  have hfibdeg := degree_pullback_point_eq_functionFieldDegree (YGG.proj f κ) Γ p₀ hp₀ hsurjΓ hgΓ
  have hslope := negative_slope f κ m hm p₀ hp₀ a b (functionFieldDegree g) hbpos he₀pos Γ
    hfibdeg hΓ
  -- Step 9: normalization ν : C̃₀ → Γ
  letI : Γ.ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hΓproj : IsProjectiveOver k Γ.carrier := IsProjectiveOver.of_isClosedImmersion Γ.ι hYproj
  obtain ⟨Ct₀, ν, hνover, hνfin, hνsurj, hνg, hνdeg⟩ :=
    exists_normalization_of_integralCurve Γ.carrier hΓproj Γ.dim_eq_one
  haveI := hνfin
  have hover : (ν ≫ Γ.ι).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    constructor
    rw [Category.assoc]
    exact hνover
  have hρfin : AlgebraicGeometry.IsFinite (ν ≫ Γ.ι ≫ YGG.proj f κ) := by
    change AlgebraicGeometry.IsFinite (ν ≫ g)
    haveI := hgfin
    infer_instance
  have hρsurj : Function.Surjective (ν ≫ Γ.ι ≫ YGG.proj f κ).base := by
    intro c
    obtain ⟨γ, hγ⟩ := hsurjΓ c
    obtain ⟨t, ht⟩ := hνsurj γ
    refine ⟨t, ?_⟩
    change g.base (ν.base t) = c
    rw [ht]
    exact hγ
  have hρgen : (ν ≫ Γ.ι ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme)
      = genericPoint C.toScheme := by
    change g.base (ν.base (genericPoint Ct₀.toScheme)) = genericPoint C.toScheme
    rw [hνg]
    exact hgΓ
  have hρdeg : functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) = functionFieldDegree g := by
    change functionFieldDegree (ν ≫ g) = functionFieldDegree g
    rw [functionFieldDegree_comp_of_genericPoint ν g hνg, hνdeg, one_mul]
  refine ⟨m, hSD, hdiv, Γ, Ct₀, ν, hνfin, hνg, hνdeg, hover, hρfin, hρsurj, hρgen, ?_⟩
  rw [hρdeg]
  change θ < _
  rw [hθab]
  exact hslope

/-- **An affine lift after finite base change** (Lemma 3.1 of the paper;
§3 of the paper). Input: a `k`-morphism `ν₀ : C̃₀ → Y_κ^GG` from a smooth projective curve
such that `ν₀ ≫ π_κ` is finite, surjective and sends the generic point to the generic point (in the
paper `ν₀ = τ₀` is the normalization of the horizontal curve followed by the inclusion; only these
properties are used). Output: a finite cover `ρ : C̃ → C` factoring as `ρ = η ≫ ν₀ ≫ π_κ` with
`η : C̃ → C̃₀` finite and dominant, a line bundle `L` on `C̃`, and a based jet
`J : C̃_(κ)(L) → 𝒵` over `ρ` whose positive-order coefficient tuple is nowhere zero and whose
weighted projectivization `J.projectivize hnz : C̃ → Y_κ^GG` equals `η ≫ ν₀`.
(`κ ≥ 1` is needed: for `κ = 0` there are no positive-order coefficients.)

Proof (the `q`-th roots are obtained by a further finite extension, as in the paper; the two main steps
live in `PositiveLineCoreWeightedRescaling_AffineJet` and `BasedJetOfAffineJet`):
1. `weighted_rescaling_generic_affineJet` (the paper's
   paragraph "A generic affine representative", Lemma 3.1 of the paper): a finite family of affine
   honest jet charts `(V α, chart α)` covering `C` and containing `η_C`, a designated chart `α₀`, a
   finite cover `ρ = η ≫ ν₀ ≫ π_κ : C̃ → C` (`η : C̃ → C̃₀` finite, generic point to generic point), an
   affine jet `ĵ : Spec κ(η_{C̃}) → J_κ^s` over `η_{C̃} ≫ ρ` lying over every chart, whose coordinate
   tuples `b α` (`affineJetCoord`) are nonzero and have `(q+1)`-th roots **in every chart** (the
   paper's "simultaneously for the finitely many charts", Lemma 3.1 of the paper), and such that the
   fiber coordinate of `η ≫ ν₀` at the generic point of `C̃` in the chart `α₀` is the weighted point
   of `b α₀` (`weightedPointOfCoords`).
2. `weighted_rescaling_jet_of_affineJet` (the paragraph
   "The parameter line and the based jet", Lemma 3.1 of the paper): from these data, the line bundle
   `L = O(Σ w_y [y])` (the weights `w_y` computed chart by chart, integral by the roots), the based
   jet `J : BasedJet f ρ L κ` with nowhere-zero normalized tuple and a nonzero positive-order
   coefficient, whose generic weighted point has fiber coordinate the weighted point of `b α₀` in the
   chart `α₀`.
3. `J.genericWeightedPoint` and `Spec κ(η_{C̃}) → C̃ → C̃₀ → Y_κ^GG` both lie over `Spec κ(η_{C̃}) → C̃ → C`
   (`BasedJet.genericWeightedPoint_proj`, `ρ = η ≫ ν₀ ≫ π_κ`) and have the same fiber coordinate
   (1. and 2.), so they are equal (`jetChart.hom_ext_of_fiberCoords_eq`: a `K`-point of
   `π_κ⁻¹(V) ≅ V × P(w)` is determined by its two components). `exists_tau`
   then gives `J.projectivize hnz = η ≫ ν₀` (agreement at the dense generic point, `Y_κ^GG`
   separated). ∎

Note that the roots must be taken simultaneously for the finitely many charts, as in the paper: a root
hypothesis in a **single** chart `V ∋ η_C` does not make the weighted orders at points `y` with `ρ(y) ∉ V`
integral, so `L` need not exist (for `X = C = P¹`, `κ = 2`, `ρ = id`, `A = O(1)` and the tuple
`b = (0; 1, 0)`, the weighted order at `∞` in the other chart is `-1/2`).

Comparison with Lemma 3.1 of the paper: `η` is the paper's `ρ₁` (finite, generic point to
generic point; surjective because `ρ` is a `FiniteCover`), `ρ.hom = η ≫ ν₀ ≫ π_κ` is `ρ = ρ₀ ∘ ρ₁`,
`J : BasedJet f ρ L κ` is the morphism `C̃_(κ)(L) → 𝒵` over `C` (`BasedJet.over`) restricting to
`s ∘ ρ` on the zero section (`BasedJet.restrict`), `NormalizedTupleNowhereZero J` is "its
positive-order coefficient tuple is nowhere zero", and `J.projectivize hnz = η ≫ ν₀` is "its weighted
projectivization is `τ = τ₀ ∘ ρ₁`". The input generalizes the paper harmlessly: any `ν₀` with the
three properties the proof uses, instead of the specific `τ₀` supplied by Lemma 2.5. -/
theorem weighted_rescaling {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (hκ : 1 ≤ κ)
    {Ct₀ : SmoothProjectiveCurve k} (ν₀ : Ct₀.toScheme ⟶ YGG f κ)
    [ν₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsFinite (ν₀ ≫ YGG.proj f κ)]
    (hsurj : Function.Surjective (ν₀ ≫ YGG.proj f κ).base)
    (hgen : (ν₀ ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme) :
    ∃ (ρ : FiniteCover k C) (η : ρ.source.toScheme ⟶ Ct₀.toScheme)
      (_ : AlgebraicGeometry.IsFinite η)
      (_ : η.base (genericPoint ρ.source.toScheme) = genericPoint Ct₀.toScheme)
      (_ : ρ.hom = η ≫ ν₀ ≫ YGG.proj f κ)
      (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
      (hnz : NormalizedTupleNowhereZero J),
      J.projectivize hnz = η ≫ ν₀ := by
  obtain ⟨ι, _, V, hV, chart, hηV, hcover, α₀, ρ, η, hηfin, hηg, hρ, ĵ, hĵ, hĵV, b, hb, hne, hroot,
      hx, hfib⟩ :=
    weighted_rescaling_generic_affineJet f κ hκ ν₀ hsurj hgen
  obtain ⟨L, J, hnz, hne', hx', hfib'⟩ :=
    weighted_rescaling_jet_of_affineJet f κ ρ ĵ hĵ hV chart hηV hcover hĵV b hb hne hroot α₀
  have hgenpt : J.genericWeightedPoint hne' =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ η ≫ ν₀ := by
    refine (chart α₀).hom_ext_of_fiberCoords_eq _ _ hx' hx ?_ ?_
    · have h1 : ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom =
          (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ η ≫ ν₀) ≫
            YGG.proj f κ := by
        rw [hρ]
        simp only [Category.assoc]
      exact (J.genericWeightedPoint_proj hne').trans h1
    · exact hfib'.trans hfib.symm
  obtain ⟨τ, hτJ, -, hτ⟩ := exists_tau f κ ν₀ ρ η L J hnz hne' hgenpt
  exact ⟨ρ, η, hηfin, hηg, hρ, L, J, hnz, hτJ.symm.trans hτ⟩

/-- Proposition 3.2 of the paper (§3), core statement: assembled
from `negative_horizontal_curve`, `weighted_rescaling`, `tau_pullback_polarization`
(`τ^*B_κ ≅ L^{-m}`), `degree_relation` (`d_L = -deg η · (Γ·B_κ)/m`, `deg ρ = deg η · e₀`),
and `not_genericallyScalar_of_degree_pos` (`d_L > 0` and nowhere-zero normalized tuple ⇒ not
generically scalar). -/
theorem positive_line_core {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (hf : ¬ IsConstantMorphism f)
    (hd : 0 < TangentBundle.pullbackDegree f) (κ : ℕ) (hκ : 1 ≤ κ) :
    ∃ (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
      (J : BasedJet f ρ L κ),
      NormalizedTupleNowhereZero J ∧
      ¬ J.IsGenericallyScalar ∧
      (L.degree : ℚ) / (ρ.degree : ℚ)
        > ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ)
            / (2 * ((X.toVariety.dim : ℚ) + 1) * κ) := by
  obtain ⟨m, hSD, hdiv, Γ, Ct₀, ν, hνfin, hνg, hνbir, hover, hfin, hsurj, hgen, hslope⟩ :=
    negative_horizontal_curve f hd κ hκ
  have : Fact ((jetAlgebra f κ).SufficientlyDivisible m) := ⟨hSD⟩
  have := hνfin
  have := hover
  have : AlgebraicGeometry.IsFinite ((ν ≫ Γ.ι) ≫ YGG.proj f κ) := by
    rw [Category.assoc]; exact hfin
  have hsurj' : Function.Surjective ((ν ≫ Γ.ι) ≫ YGG.proj f κ).base := by
    rw [Category.assoc]; exact hsurj
  have hgen' : ((ν ≫ Γ.ι) ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme)
      = genericPoint C.toScheme := by
    rw [Category.assoc]; exact hgen
  obtain ⟨ρ, η, hηfin, hηg, hρ, L, J, hnz, hτ⟩ :=
    weighted_rescaling f κ hκ (ν ≫ Γ.ι) hsurj' hgen'
  have := hηfin
  have hm : 0 < m := hSD.1
  -- τ^*B_κ ≅ L^{-m} with τ = J.projectivize hnz = η ≫ ν ≫ Γ.ι
  have hiso := tau_pullback_polarization f κ m hdiv ρ L J hnz (J.projectivize hnz) rfl
    (J.projectivize_proj hnz)
  rw [hτ] at hiso
  have hρ' : ρ.hom = η ≫ ν ≫ Γ.ι ≫ YGG.proj f κ := by
    rw [hρ]; simp only [Category.assoc]
  obtain ⟨hL, he⟩ := degree_relation f κ m hm ρ L Γ ν hνg hνbir η hηg hρ' hgen hiso
  -- arithmetic
  set θ : ℚ := ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ)
    / (2 * ((X.toVariety.dim : ℚ) + 1) * κ) with hθ
  set B : ℚ := (Γ.degree (polarization f κ m) : ℚ) with hB
  set dη : ℕ := functionFieldDegree η with hdη
  set e₀ : ℕ := functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) with he₀
  have hρdeg : ρ.degree = dη * e₀ := by
    rw [FiniteCover.degree_eq_functionFieldDegree]; exact he
  have hρpos : 0 < ρ.degree := ρ.degree_pos
  have hdηpos : 0 < dη := by
    rcases Nat.eq_zero_or_pos dη with h | h
    · rw [h, zero_mul] at hρdeg; omega
    · exact h
  have he₀pos : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · rw [h, mul_zero] at hρdeg; omega
    · exact h
  have hdηQ : (0 : ℚ) < dη := by exact_mod_cast hdηpos
  have he₀Q : (0 : ℚ) < e₀ := by exact_mod_cast he₀pos
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hslope' : (L.degree : ℚ) / (ρ.degree : ℚ) = - B / ((m : ℚ) * e₀) := by
    rw [hL, hρdeg]
    push_cast
    field_simp
  have hθlt : θ < (L.degree : ℚ) / (ρ.degree : ℚ) := by
    rw [hslope']; exact hslope
  have hθpos : 0 < θ := positive_line_threshold_pos f hd κ hκ
  have hLpos : 0 < L.degree := by
    have hρQ : (0 : ℚ) < ρ.degree := by exact_mod_cast hρpos
    have : (0 : ℚ) < (L.degree : ℚ) / (ρ.degree : ℚ) := lt_trans hθpos hθlt
    have := (div_pos_iff_of_pos_right hρQ).mp this
    exact_mod_cast this
  exact ⟨ρ, L, J, hnz, not_genericallyScalar_of_degree_pos f κ ρ L hLpos J hnz, hθlt⟩

/-- Qualitative output of the geometric construction only: a based jet on a finite cover which is
everywhere normalized and generically non-scalar. Corollary of `positive_line_core`. -/
theorem positive_line_core_geometric_witness {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (hf : ¬ IsConstantMorphism f)
    (hd : 0 < TangentBundle.pullbackDegree f) (κ : ℕ) (hκ : 1 ≤ κ) :
    ∃ (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
      (J : BasedJet f ρ L κ),
      NormalizedTupleNowhereZero J ∧ ¬ J.IsGenericallyScalar := by
  obtain ⟨ρ, L, J, hN, hS, -⟩ := positive_line_core f hf hd κ hκ
  exact ⟨ρ, L, J, hN, hS⟩

/-- Numerical output of the slope estimate only: a finite cover and a line bundle reaching the strict
threshold. Corollary of `positive_line_core`. -/
theorem positive_line_core_slope_witness {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (hf : ¬ IsConstantMorphism f)
    (hd : 0 < TangentBundle.pullbackDegree f) (κ : ℕ) (hκ : 1 ≤ κ) :
    ∃ (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety),
      (L.degree : ℚ) / (ρ.degree : ℚ)
        > ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ)
            / (2 * ((X.toVariety.dim : ℚ) + 1) * κ) := by
  obtain ⟨ρ, L, J, -, -, hslope⟩ := positive_line_core f hf hd κ hκ
  exact ⟨ρ, L, hslope⟩

end
