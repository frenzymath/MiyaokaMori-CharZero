import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.AffineJetChartCoords
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.ParameterLineBundleRationalSection
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.ChartFamilyWeightFunction
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.AffineJetChartTransition
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetOfRegularCoefficients
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.ChartFamilyNowhereZero
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetGenericChartCoordsOfFrame
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.NormalizeCoefficients
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Frames
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame

/-! # The based jet of an affine jet with root coordinates in a chart family

Lemma 3.1 of the paper: the generic affine jet is **one** `K`-point of the affine jet scheme
`J_κ^s ×_C Spec K`; its coordinate tuples `b_α` in the finitely many charts `U_α` covering `C` are
related by the exact jet transitions, and the `q`-th roots are extracted "simultaneously for the
finitely many charts". Lemma 3.1 of the paper then computes the weight `w_y` of the parameter line at
`y ∈ C̃` "in a jet chart whose base open contains `ρ(y)`".

A version knowing only the tuple `b` of **one** chart `V ∋ η_C` with roots would not suffice: at `y` with
`ρ(y) ∉ V` the weighted order of
the same affine jet in a chart `V' ∋ ρ(y)` differs from `weightedOrderQ b y` by the order at `y` of the
transition (regular on `V ∩ V'` only), which need not be a multiple of the weights — integrality can
fail and then no `L` exists (explicit configuration in the docstring of `exists_basedJet_of_tuple`).
Replacing the single tuple by a family of tuples `b α` with roots that merely define the **same
weighted-projective point** does not repair this either: in `P(1^{n+1}, 2^{n+1})` the tuples
`(0; 1, 0, …)` and `(0; g, 0, …)` define the same `K`-point for every `g ∈ K^×` (both lie in the chart
`x_{0,1} ≠ 0`, where all degree-`0` fractions vanish on them), so the tuple with roots in the second
chart carries no information about the order of `g`. The hypothesis has to say that the `b α` are the
coordinates of one affine jet `ĵ`.

This module states the construction with exactly that hypothesis: a `κ(η_{C̃})`-point `ĵ` of the
affine jet scheme `J_κ^s` (`relativeJetScheme`) over `η_{C̃} ≫ ρ`, a family of affine honest charts
`(V α, chart α)` covering `C`, the tuples `b α := (ĵ^♯ (chart α).coords (i,q))` (`affineJetCoord`,
`AffineJetChartCoords`) with roots. The conclusion is that of `exists_basedJet_of_tuple`
for any designated chart `α₀`.

* `exists_basedJet_of_affineJet_frame`: the construction (steps 1–5 of the paper's second paragraph),
  the coefficients of `J` identified on an open `U ∋ η_{C̃}` in a frame `μ` of `L^{-1}` — the form the
  construction produces. Assembled from the lemmas
  - `affineJetCoord_jetTransitionRelated` → `exists_weightFunction_of_affineJet` (step 1;
    `AffineJetChartTransition`, `ChartFamilyWeightFunction`),
  - `exists_lineBundle_rationalSection_of_weightFunction` and
    `SmoothProjectiveCurve.exists_section_of_forall_ord_nonneg` (steps 2–3; `ParameterLineBundleRationalSection`),
  - `exists_basedJet_of_regular_coefficients` (steps 4–5, the gluing; `BasedJetOfRegularCoefficients`),
  - `BasedJet.normalizedTupleNowhereZero_of_unit_coefficient` (nowhere-zero tuple; module
    `ChartFamilyNowhereZero`),
  together with `normalized_coefficients_regular_and_unit`.
* `exists_basedJet_of_affineJet`: the same with generic chart coordinates (`BasedJet.genericChartCoords`),
  assembled from the frame version and `BasedJet.exists_genericTrivialization_of_frame`
  (`BasedJetGenericChartCoordsOfFrame`). The affine jet `ĵ` and the family are produced by the first half of the
  proof of Lemma 3.1 of the paper.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- **The parameter line and the based jet of an affine jet, in a frame**
(Lemma 3.1 of the paper). Input: a finite cover `ρ : C̃ → C`; a
`κ(η_{C̃})`-point `ĵ` of the affine jet scheme `J_κ^s = relativeJetScheme 𝒵 s κ` over `η_{C̃} ≫ ρ`
(`hĵ`; the generic affine jet of the paper); a family of affine honest jet charts `(V α, chart α)`
covering `C` (`hcover`), each containing `η_C` (`hηV`, automatic for nonempty opens of the irreducible
`C`) and hence containing the image of `ĵ` (`hĵV`, likewise automatic — both are kept as hypotheses
so that the statement needs no proof terms); the coordinate tuples `b α i q = ĵ^♯((chart α).coords (i,q))`
(`hb`, `affineJetCoord`; weight `q + 1` on `b α i q`), nonzero (`hne`) and with `(q+1)`-th roots
(`hroot`, the paper's "simultaneously for the finitely many charts", Lemma 3.1 of the paper).
Output, for a designated chart `α₀`: a line bundle `L` on `C̃`, a based jet `J : C̃_(κ)(L) → 𝒵` over
`ρ` with nowhere-zero normalized tuple, an open `U ∋ η_{C̃}` with `U ⊆ ρ⁻¹(V α₀)`, a frame `μ` of
`L^{-1}` on `U`, and `γ ∈ K(C̃)^×` such that for every `(i, q)` the section `Ψ_{q+1}(x_{i,q})` of
`(L^∨)^{⊗(q+1)}` on `ρ⁻¹(V α₀)` (`J.weightComponent` transposed along the adjunction;
`x_{i,q} = (chart α₀).coords (i,q)`) restricts on `U` to `r • μ^{⊗(q+1)}` with `r ∈ O(U)` regular and
with germ `γ^{q+1} b α₀ i q` at `η_{C̃}` — the paper's normalized coefficient
`a_{i,q} = γ_ε^{-(q+1)} b_{i,q}` in the frame `ε` dual to `μ` (Lemma 3.1 of the paper; our `γ` is
`γ_ε⁻¹`).

Natural-language proof (notation `w := jetWeights n κ`, `S := jetAlgebra f κ`, `𝒵 := MMSetup.cone f`,
`s := MMSetup.seed f`, `B_α := Γ(𝒵, π⁻¹(V α))`):
1. **Weighted orders.** For `y ∈ C̃` choose `α(y)` with `ρ(y) ∈ V α(y)` (`hcover`) and put
   `w_y := weightedOrderQ (b α(y)) (hne α(y)) y`; `exists_int_weightedOrder`
   (from `hroot α(y)`) gives `w_y ∈ ℤ`. Independence of the choice: for
   `α, β` with `ρ(y) ∈ V α ∩ V β` the two tuples are the coordinates of the same affine jet `ĵ` (`hb`),
   so they are related by the jet transition of the two honest charts (`jet_transition_formula`,
   : `S(V α ∩ V β)` has the two polynomial presentations `ε_α`, `ε_β` restricted
   from `V α`, `V β`, and `ε_β ∘ ε_α⁻¹` is a weighted-homogeneous substitution with coefficients in
   `Γ(V α ∩ V β)`, regular at `ρ(y)`; `ĵ^♯` is a ring map, so it carries the substitution to the tuples),
   and `weightedOrder_chart_independent`  gives equality of
   the two weighted orders at `y`. `finite_support_weightedOrder`
    for `b α₀`, plus the finiteness of `C̃ ∖ ρ⁻¹(V α₀)`
   (a proper closed subset of a curve), shows that only finitely many `w_y` are nonzero.
2. **The line bundle.** `D_L := Σ_y w_y [y]` (a finite sum of `Divisor.ofPoint`, as in `divisorDL`),
   `L := D_L.lineBundle` (`CartierDivisor.lineBundle`). Its canonical
   rational section `1` has order `w_y` at `y`; on an open `U` with a frame `ε` of `L`
   (`LineBundle.Frame`) write `1 = γ_ε ε`, `γ_ε ∈ K(C̃)^×`,
   `ord_y γ_ε = w_y` for `y ∈ U`.
3. **Normalized coefficients.** On `U ⊆ ρ⁻¹(V α)` with frame `ε`: `a^α_{i,q} := γ_ε^{-(q+1)} b α i q`;
   `normalized_coefficients_regular_and_unit`  shows all `a^α_{i,q}` are
   regular on `U` and at every point of `U` some `a^α_{i,q}` is a unit. A change of frame `ε' = u ε`
   multiplies them by `u^{q+1}` (`normalized_coefficients_frame_change`); a change of chart applies the jet transition (step 1; weighted
   homogeneity commutes with the rescaling by `γ_ε^{-(q+1)}`).
4. **Local jets and gluing.** Cover `C̃_(κ)(L)` by `p_L⁻¹(U)` with `U` affine, `U ⊆ ρ⁻¹(V α)` for
   some `α`, and `L|_U` framed by `ε`. `jetNeighborhood.trivialization_of_frame`
    gives `p_L⁻¹(U) ≅ Spec O(U)[t]/(t^{κ+1})` over `U` with `t` the
   dual frame `ε^∨`. The honest chart gives `S(V α) ≅ Γ(V α)[x_{i,q}]` (`(chart α).honest`) and
   `S(V α) = J_κ(B_α, s^♯)` is the based jet algebra of the cone over `V α`
   (`relativeJetScheme.chartRing`, `BasedJetAlgebra`). The `Γ(V α)`-algebra map `S(V α) → O(U)`,
   `x_{i,q} ↦ a^α_{i,q}`, corresponds under `BasedJetAlgebra.homEquiv`  to a
   ring map `B_α → O(U)[t]/(t^{κ+1})` over `Γ(V α) → O(U)` with constant term `s^♯`, i.e. (as
   `𝒵|_{V α} = Spec B_α` is affine over `V α`, `MMSetup.cone_isAffineHom`) to `g_U : p_L⁻¹(U) → 𝒵` over
   `ρ|_U` restricting to `s ∘ ρ` on the zero section. On overlaps the `g_U` agree (step 3: the frame
   change is the substitution `t ↦ u^{-1} t`, the chart change is the identification of `S(V α)` and
   `S(V β)` over `V α ∩ V β`), so `exists_glued_jet`  glues them to
   `J : BasedJet f ρ L κ` with `p_L⁻¹(U).ι ≫ J.hom = g_U`.
5. **The coefficients of `J`.** For `U`, `α`, `ε` as in step 4 and `c ∈ B_α`, `J.pieceSection U (q+1) c`
   is the `t^{q+1}`-coefficient of `g_U^♯ c`, and `BasedJet.weightComponent_jetCoordinate`
    identifies `Ψ_{q+1}(d_q c)` with it; by the
   construction of `g_U` through `homEquiv`, `Ψ_{q+1}(x_{i,q})|_U = a^α_{i,q} · μ^{⊗(q+1)}` with
   `μ = ε^∨` (for honest coordinates not of the form `d_q c`, write `x_{i,q}` as a polynomial in the
   `d_q c` through `ε_α` and use multiplicativity of `Ψ`, `BasedJet.weightComponent_map_mul`).
   Nowhere-zero normalized tuple: at every `y` some `a^α_{i,q}` is a unit (step 3), so some `Ψ_{q+1}`
   is surjective at `y`; the cone coefficients `J.coefficient ℓ (q+1)` are the `Ψ_{q+1}(d_q x_ℓ)` for
   the cone coordinates `x_ℓ`, which generate `S_{q+1}` over lower weights, so some
   `J.coefficient ℓ (q+1)` does not vanish at `y` (the converse
   direction of `BasedJet.exists_pieceSection_generatesAt`). Finally take `U ∋ η_{C̃}` with
   `U ⊆ ρ⁻¹(V α₀)`, the frame `ε`, `μ := ε^∨`, `γ := γ_ε⁻¹`, `r := a^{α₀}_{i,q}` (regular on `U` by
   step 3, germ `γ^{q+1} b α₀ i q`). ∎

**Assembly**: step 1 is
`exists_weightFunction_of_affineJet` (`AffineJetChartTransition`; its main ingredient is the jet
transition `affineJetCoord_jetTransitionRelated`, piece (iv) above); step 2 is
`exists_lineBundle_rationalSection_of_weightFunction` (`ParameterLineBundleRationalSection`, piece (iii));
step 3 is `normalized_coefficients_regular_and_unit` plus the regularity lemma
`SmoothProjectiveCurve.exists_section_of_forall_ord_nonneg`; steps 4–5 are the gluing lemma
`exists_basedJet_of_regular_coefficients` (`BasedJetOfRegularCoefficients`, pieces (i)–(ii)), and the
nowhere-zero tuple is `BasedJet.normalizedTupleNowhereZero_of_unit_coefficient`
(`ChartFamilyNowhereZero`, the converse direction of `BasedJet.exists_pieceSection_generatesAt`).
The frame `μ` of `L^{-1}` is `zpowNegOneIso⁻¹ δ` for the dual frame `δ` of `e`
(`IsFrame.exists_dual_pairing_one_dualEv`, `IsFrame.dual_of_pairing_eq_one`), exactly as in
`jetNeighborhood.trivialization_of_frame`; `γ` here is `γ_e⁻¹` for the coefficient `γ_e` of `s_L` in `e`.

Edge cases: `κ = 0` — `hne α` is impossible (`Fin 0` empty), vacuous; `n = 0` fine; `ι` empty is
excluded by `hcover` (`C` is nonempty). Nothing requires `ι` to be finite (finiteness is needed only
upstream, to take the roots in one finite extension). -/
theorem exists_basedJet_of_affineJet_frame [IsAlgClosed k]
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {ι : Type u} {V : ι → C.toScheme.Opens} (hV : ∀ α, AlgebraicGeometry.IsAffineOpen (V α))
    (chart : ∀ α, HonestJetChart f κ (V α)) (hηV : ∀ α, genericPoint C.toScheme ∈ V α)
    (hcover : ∀ c : C.toScheme, ∃ α, c ∈ V α)
    (hĵV : ∀ α, (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α))
    (b : ι → Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hb : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      b α i q = affineJetCoord ρ ĵ (hĵV α) _ ((chart α).coords (i, q)))
    (hne : ∀ α, ∃ i q, b α i q ≠ 0)
    (hroot : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), b α i q ≠ 0 →
      ∃ c : ρ.source.toScheme.functionField, c ^ ((q : ℕ) + 1) = b α i q)
    (α₀ : ι) :
    ∃ (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
      (_ : NormalizedTupleNowhereZero J)
      (U : ρ.source.toScheme.Opens) (_ : genericPoint ρ.source.toScheme ∈ U)
      (hUV : U ≤ ρ.hom ⁻¹ᵁ V α₀) (μ : Γ((L.zpow (-1)).toModules, U))
      (_ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules U μ)
      (γ : ρ.source.toScheme.functionField), γ ≠ 0 ∧
      ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), ∃ r : Γ(ρ.source.toScheme, U),
        (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
         haveI : Nonempty U := ⟨⟨_, ‹genericPoint ρ.source.toScheme ∈ U›⟩⟩
         (ρ.source.toScheme.germToFunctionField U).hom r) = γ ^ ((q : ℕ) + 1) * b α₀ i q ∧
        (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩), U) from
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).val.map (CategoryTheory.homOfLE hUV).op).hom
          (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
            (J.weightComponent (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩))).val.app
              (Opposite.op (V α₀))).hom ((chart α₀).coords (i, q)))) =
          r • (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩), U) from
            (((truncatedJetAlgebra.pieceIso L (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).hom.val.app
              (Opposite.op U)).hom
              (truncatedJetAlgebra.framePow L U μ (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)))) := by
  classical
  haveI hInt : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  -- Step 1: the integer weight function `w`
  obtain ⟨w, hwfin, hw⟩ :=
    exists_weightFunction_of_affineJet f κ ρ ĵ hĵ chart hcover hĵV b hb hne hroot
  -- Step 2: the line bundle `L = O(Σ w_y [y])` and its canonical rational section `s`
  obtain ⟨L, s, hs0, hsord⟩ := exists_lineBundle_rationalSection_of_weightFunction ρ.source w hwfin
  -- the coefficient of `s` in a frame over `ρ⁻¹(V α)` has the weighted orders of `b α`
  have hγord : ∀ (U : ρ.source.toScheme.Opens) (hηU : genericPoint ρ.source.toScheme ∈ U) (α : ι)
      (_ : U ≤ ρ.hom ⁻¹ᵁ V α) (e : Γ(L.toModules, U))
      (_ : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U e) (γ : ρ.source.toScheme.functionField),
      s = γ • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
        L.toModules.stalk (genericPoint ρ.source.toScheme)) →
      γ ≠ 0 ∧ ∀ z ∈ U, (ρ.source.toScheme.ord γ z : ℚ) = weightedOrderQ (b α) (hne α) z := by
    intro U hηU α hUV e he γ hγ
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      exact hs0 (by rw [hγ]; exact zero_smul _ _)
    refine ⟨hγ0, fun z hz => ?_⟩
    by_cases hco : Order.coheight z = 1
    · rw [hsord U hηU e he γ hγ z hz hco]
      exact hw α z (hUV hz)
    · have hz' := SmoothProjectiveCurve.eq_genericPoint_of_coheight_ne_one ρ.source z hco
      subst hz'
      rw [ρ.source.ord_genericPoint, weightedOrder_genericPoint]
      simp
  -- Step 3: the normalized coefficients are regular
  have hreg : ∀ (U : ρ.source.toScheme.Opens) (_ : AlgebraicGeometry.IsAffineOpen U)
      (hηU : genericPoint ρ.source.toScheme ∈ U) (α : ι) (_ : U ≤ ρ.hom ⁻¹ᵁ V α)
      (e : Γ(L.toModules, U)) (_ : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U e)
      (γ : ρ.source.toScheme.functionField),
      s = γ • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
        L.toModules.stalk (genericPoint ρ.source.toScheme)) →
      ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), ∃ r : Γ(ρ.source.toScheme, U),
        (haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
         (ρ.source.toScheme.germToFunctionField U).hom r) = γ ^ (-((q : ℕ) + 1 : ℤ)) * b α i q := by
    intro U _ hηU α hUV e he γ hγ i q
    obtain ⟨hγ0, hord⟩ := hγord U hηU α hUV e he γ hγ
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    exact ρ.source.exists_section_of_forall_ord_nonneg U _ fun z hz =>
      (normalized_coefficients_regular_and_unit (b α) (hne α) U γ hγ0 hord z hz).1 i q
  -- Step 4: the based jet
  obtain ⟨J, hJ⟩ :=
    exists_basedJet_of_regular_coefficients f κ ρ ĵ hĵ hV chart hηV hcover hĵV b hb L s hreg
  -- Step 5: the normalized tuple is nowhere zero
  have hnz : NormalizedTupleNowhereZero J := by
    refine J.normalizedTupleNowhereZero_of_unit_coefficient fun y => ?_
    obtain ⟨α, hyα⟩ := hcover (ρ.hom.base y)
    have hy' : y ∈ ρ.hom ⁻¹ᵁ V α := hyα
    obtain ⟨U, hU, hUV, hyU, e, he⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le L.toModules hy'
    have hηU : genericPoint ρ.source.toScheme ∈ U :=
      (genericPoint_specializes y).mem_open U.isOpen hyU
    obtain ⟨γ, hγ⟩ := he.exists_smul_germ_eq hηU s
    obtain ⟨hγ0, hord⟩ := hγord U hηU α hUV e he γ hγ
    obtain ⟨i, q, hne', hord0⟩ :=
      (normalized_coefficients_regular_and_unit (b α) (hne α) U γ hγ0 hord y hyU).2
    obtain ⟨r, hr⟩ := hreg U hU hηU α hUV e he γ hγ i q
    obtain ⟨δ, hδ⟩ := he.exists_dual_pairing_one_dualEv
    have hμ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules U
        (L.zpowNegOneIso.inv.app U δ) :=
      (AlgebraicGeometry.Scheme.Modules.IsFrame.dual_of_pairing_eq_one hδ).map_iso
        L.zpowNegOneIso.symm
    refine ⟨V α, chart α, U, hyU, hUV, _, hμ, i, q, r, ?_,
      hJ U hU hηU α hUV e he γ hγ δ hδ i q r hr⟩
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    have hgerm := ρ.source.toScheme.algebraMap_germ_eq_germToFunctionField hyU r
    have hr0 : ρ.source.toScheme.presheaf.germ U y hyU r ≠ 0 := by
      intro h0
      rw [h0, map_zero, hr] at hgerm
      exact hne' hgerm.symm
    exact SmoothProjectiveCurve.isUnit_of_ord_eq_zero ρ.source y hr0
      (by rw [hgerm, hr]; exact hord0)
  -- Step 6: the designated chart `α₀`
  have hη₀ : genericPoint ρ.source.toScheme ∈ ρ.hom ⁻¹ᵁ V α₀ := by
    show ρ.hom.base (genericPoint ρ.source.toScheme) ∈ V α₀
    rw [ρ.hom_genericPoint]
    exact hηV α₀
  obtain ⟨U, hU, hUV, hηU, e, he⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le L.toModules hη₀
  obtain ⟨γ, hγ⟩ := he.exists_smul_germ_eq hηU s
  obtain ⟨hγ0, -⟩ := hγord U hηU α₀ hUV e he γ hγ
  obtain ⟨δ, hδ⟩ := he.exists_dual_pairing_one_dualEv
  have hμ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules U
      (L.zpowNegOneIso.inv.app U δ) :=
    (AlgebraicGeometry.Scheme.Modules.IsFrame.dual_of_pairing_eq_one hδ).map_iso L.zpowNegOneIso.symm
  refine ⟨L, J, hnz, U, hηU, hUV, L.zpowNegOneIso.inv.app U δ, hμ, γ⁻¹, inv_ne_zero hγ0,
    fun i q => ?_⟩
  obtain ⟨r, hr⟩ := hreg U hU hηU α₀ hUV e he γ hγ i q
  refine ⟨r, ?_, hJ U hU hηU α₀ hUV e he γ hγ δ hδ i q r hr⟩
  rw [hr, inv_pow, ← zpow_natCast, ← zpow_neg]
  push_cast
  rfl

/-- **The parameter line and the based jet of an affine jet** (Lemma 3.1 of the paper; the
paper-faithful form of `exists_basedJet_of_tuple`, see the module docstring). Same hypotheses as
`exists_basedJet_of_affineJet_frame`; conclusion: `L`, `J` with nowhere-zero normalized tuple, a
trivialization `e` of `η^*L^∨` on `Spec κ(η_{C̃})` and `γ ≠ 0` with
`J.genericChartCoords … (chart α₀) … e (i, q) = γ^{q+1} b α₀ i q` — exactly what
`weighted_rescaling_jet_of_affineJet` (`BasedJetOfAffineJet`) needs for the chart `α₀`.

Proof: `exists_basedJet_of_affineJet_frame` gives `L`, `J`, `hnz`,
`U ∋ η_{C̃}`, `U ⊆ ρ⁻¹(V α₀)`, the frame `μ`, `γ`, and for each `(i, q)` a regular `r` with germ
`γ^{q+1} b α₀ i q` and `Ψ_{q+1}(x_{i,q})|_U = r • μ^{⊗(q+1)}`;
`BasedJet.exists_genericTrivialization_of_frame`  gives the
trivialization `e` induced by `μ` and turns the latter equation into `genericChartCoords (i, q) = germ r`. -/
theorem exists_basedJet_of_affineJet [IsAlgClosed k]
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {ι : Type u} {V : ι → C.toScheme.Opens} (hV : ∀ α, AlgebraicGeometry.IsAffineOpen (V α))
    (chart : ∀ α, HonestJetChart f κ (V α)) (hηV : ∀ α, genericPoint C.toScheme ∈ V α)
    (hcover : ∀ c : C.toScheme, ∃ α, c ∈ V α)
    (hĵV : ∀ α, (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α))
    (b : ι → Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hb : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      b α i q = affineJetCoord ρ ĵ (hĵV α) _ ((chart α).coords (i, q)))
    (hne : ∀ α, ∃ i q, b α i q ≠ 0)
    (hroot : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), b α i q ≠ 0 →
      ∃ c : ρ.source.toScheme.functionField, c ^ ((q : ℕ) + 1) = b α i q)
    (α₀ : ι) :
    ∃ (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
      (hnz : NormalizedTupleNowhereZero J)
      (e : (AlgebraicGeometry.Scheme.Modules.pullback
          (𝟙 (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).ringCatSheaf)
      (γ : ρ.source.toScheme.functionField), γ ≠ 0 ∧
      ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
        J.genericChartCoords hnz.exists_coefficient_ne_zero (chart α₀) (hηV α₀) e (i, q) =
          γ ^ ((q : ℕ) + 1) * b α₀ i q := by
  obtain ⟨L, J, hnz, U, hηU, hUV, μ, hμ, γ, hγ, hcoef⟩ :=
    exists_basedJet_of_affineJet_frame f κ ρ ĵ hĵ hV chart hηV hcover hĵV b hb hne hroot α₀
  obtain ⟨e, he⟩ := J.exists_genericTrivialization_of_frame hnz.exists_coefficient_ne_zero
    (chart α₀) (hηV α₀) hηU hUV μ hμ
  refine ⟨L, J, hnz, e, γ, hγ, fun i q => ?_⟩
  obtain ⟨r, hr, hΨ⟩ := hcoef i q
  rw [he (i, q) r hΨ]
  exact hr

end
