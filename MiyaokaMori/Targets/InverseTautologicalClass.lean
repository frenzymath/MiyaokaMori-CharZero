import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PolarizationPullback
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.DegreeRelation
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCore

/-! # Realization of the inverse tautological class

**Proposition 3.2** of the paper.** For the data of Lemma 2.5 (an
integral horizontal curve `Γ ⊂ Y_k^GG`, its normalization `τ₀ : C̃₀ → Γ`, `ρ₀ = π_k ∘ τ₀`) and of
Lemma 3.1 (a finite cover `ρ₁ : C̃ → C̃₀`, a line bundle `L` on `C̃` and a based
jet `ȷ` whose weighted projectivization is `τ = τ₀ ∘ ρ₁`), and `m > 0` divisible by every `q ≤ k`
with `𝒮^{(m)}` generated in degree one:

  `τ^* O_{Y_k^GG}(m) ≃ L^{-m}`,   hence   `deg L / deg ρ = −(H_k·Γ)/deg ρ₀ > d h_k / (2(n+1)k) > 0`.

The paper also states `[L] = ρ₁^* 𝓛₀` in `Pic(C̃) ⊗ ℚ`; the library has no rational Picard group, and
the integral isomorphism `τ^*O(m) ≃ L^{-m}` is the stronger statement from which that class identity
is read off, so only the isomorphism and its degree consequence are stated here. The existence
statement packaging `ρ, L, ȷ` together with the slope bound is `positive_line`
(`Paper/S3PositiveLine/PositiveLine.lean`).

Proof sketch:
1. *Tautological evaluation.* Evaluating weight-`m` functions on the affine jet gives `ρ^*𝒮_m → L^{-m}`
   (locally `ρ^*R ↦ R(a_α) ε^{-m}`; frame changes `ε' = uε` rescale `a` by `u^q` and `ε^{-m}` by
   `u^{-m}`, weighted homogeneity makes it frame-independent; chart changes are compatible by the jet
   transition formula). In the library this map is `ȷ.weightComponent m : ρ^*𝒮_m ⟶ (L^∨)^{⊗m}`.
2. *Surjectivity.* At every point some normalized coefficient `a_{α,i,q}` is a unit
   (`NormalizedTupleNowhereZero`); since `q ∣ m`, `x_{α,i,q}^{m/q} ∈ 𝒮_m` evaluates to a local
   generator of `L^{-m}` (`BasedJet.weightComponent_generates`).
3. *Veronese realization.* `𝒮^{(m)}` generated in degree one (`SufficientlyDivisible m`) realizes
   `Y_k^GG` inside `ℙ(𝒮_m^∨)` with tautological quotient `π_k^*𝒮_m ↠ O(m)`
   (Lemma 2.2 of the paper). `τ = ȷ.projectivize` is by definition the
   `relativeProj.lift` of the data `(L^∨, ȷ.weightComponent)`, so the surjection of step 2 is exactly
   the quotient corresponding to `τ`; hence `τ^*O(m) ≃ (L^∨)^{⊗m} ≃ L^{-m}`.
   In the library steps 1-3 are `tau_pullback_polarization`.
4. *The degree.* `deg τ^*O(m) = m·(H_k·Γ)·deg ρ₁` (finite pullback multiplies degrees by `deg ρ₁`,
   `τ₀^*O(m)` has degree `c₁(O(m))·Γ = m H_k·Γ`), and `deg L^{-m} = −m deg L`; with
   `deg ρ = deg ρ₁ · deg ρ₀` this gives `deg L / deg ρ = −(H_k·Γ)/deg ρ₀` (`degree_relation`, plus
   `FiniteCover.degree = functionFieldDegree`), and Lemma 2.5
   (`negative_horizontal_curve`) gives `> d h_k/(2(n+1)k) > 0`.

Edge cases: `m` is forced positive by `SufficientlyDivisible`; `deg ρ₀ > 0` since `ρ₀` is finite
surjective onto the integral curve `C` (`functionFieldDegree` of a finite dominant map of integral
curves is `≥ 1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Realization of the inverse tautological class** (Proposition 3.2 of the paper). For the data of the negative horizontal
curve `Γ` (with normalization `ν : C̃₀ → Γ`, `ρ₀ = ν ≫ Γ.ι ≫ π_k`) and of the affine lift after finite base change
(`η : C̃ → C̃₀`, `ρ = η ≫ ρ₀`, line bundle `L`, based jet `J` with nowhere-zero normalized tuple whose weighted
projectivization is `τ = η ≫ ν ≫ Γ.ι`), and `m` divisible by every `q ≤ κ` with `𝒮^{(m)}` generated in degree one:
`τ^*O_{Y_κ^GG}(m) ≅ L^{-m}`, `deg L / deg ρ = −(H_κ·Γ)/deg ρ₀` where `H_κ·Γ = deg(O(m)|_Γ)/m`, and, given the
negative-slope bound of the horizontal curve, `deg L / deg ρ > d h_κ /(2(n+1)κ)`. -/
theorem inverse_tautological_class {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ)
    (hm : ∀ q ∈ Finset.Icc 1 κ, q ∣ m) [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    -- data of Lemma 2.5
    (Γ : IntegralCurve k (YGG f κ))
    {Ct₀ : SmoothProjectiveCurve k} (ν : Ct₀.toScheme ⟶ Γ.carrier) [AlgebraicGeometry.IsFinite ν]
    (hνg : ν.base (genericPoint Ct₀.toScheme) = genericPoint Γ.carrier)
    (hνbir : functionFieldDegree ν = 1)
    (hg₀ : (ν ≫ Γ.ι ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme)
    (hslope₀ : ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ) / (2 * ((X.toVariety.dim : ℚ) + 1) * κ)
      < - (Γ.degree (polarization f κ m) : ℚ)
          / ((m : ℚ) * (functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) : ℚ)))
    -- data of Lemma 3.1
    (ρ : FiniteCover k C) (η : ρ.source.toScheme ⟶ Ct₀.toScheme) [AlgebraicGeometry.IsFinite η]
    (hηg : η.base (genericPoint ρ.source.toScheme) = genericPoint Ct₀.toScheme)
    (hρ : ρ.hom = η ≫ ν ≫ Γ.ι ≫ YGG.proj f κ)
    (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J)
    (hτ : J.projectivize hnz = η ≫ ν ≫ Γ.ι) :
    -- (i) the tautological identification τ^*O(m) ≅ L^{-m}
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (η ≫ ν ≫ Γ.ι)).obj (polarization f κ m)
        ≅ (L.zpow (-(m : ℤ))).toModules) ∧
    -- (ii) the degree: deg L / deg ρ = −(H_κ·Γ) / deg ρ₀
    (L.degree : ℚ) / (ρ.degree : ℚ)
        = - (Γ.degree (polarization f κ m) : ℚ)
            / ((m : ℚ) * (functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) : ℚ)) ∧
    -- (iii) the slope bound transferred to L
    (L.degree : ℚ) / (ρ.degree : ℚ)
        > ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ) / (2 * ((X.toVariety.dim : ℚ) + 1) * κ) := by
  have hm0 : 0 < m := (Fact.out : (jetAlgebra f κ).SufficientlyDivisible m).1
  -- (i): steps 1-3 of the docstring are `tau_pullback_polarization` for τ = J.projectivize hnz
  have hiso := tau_pullback_polarization f κ m hm ρ L J hnz (J.projectivize hnz) rfl
    (J.projectivize_proj hnz)
  rw [hτ] at hiso
  -- (ii): step 4, degrees from the isomorphism
  obtain ⟨hL, he⟩ := degree_relation f κ m hm0 ρ L Γ ν hνg hνbir η hηg hρ hg₀ hiso
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
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have hslope' : (L.degree : ℚ) / (ρ.degree : ℚ) = - B / ((m : ℚ) * e₀) := by
    rw [hL, hρdeg]
    push_cast
    field_simp
  -- (iii): step 5
  refine ⟨hiso, hslope', ?_⟩
  rw [hslope']
  exact hslope₀

end
