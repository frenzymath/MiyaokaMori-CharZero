import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCore

/-! # A negative horizontal curve

**Lemma 2.5** of the paper.** Fix `k ≥ 1` and put `θ = d h_k / (2(n+1)k)`. There
exist an integral horizontal curve `Γ ⊂ Y_k^GG`, a smooth connected projective curve `C̃₀` and a
morphism `τ₀ : C̃₀ → Γ ⊂ Y_k^GG` which is the normalization of `Γ` followed by the inclusion;
`ρ₀ = π_k ∘ τ₀ : C̃₀ → C` is finite and surjective, and

  `H_k·Γ + θ deg ρ₀ < 0`,  equivalently  `−(H_k·Γ)/deg ρ₀ > θ`.

This file is the target-level restatement; the theorem is `negative_horizontal_curve`
(`Paper/S3PositiveLine/Rescaling/PositiveLineCore.lean`), whose docstring carries the proof sketch
(the class `m(H_k + θ π_k^*[c])` has negative top self-intersection by Proposition 2.4,
hence is not nef; a curve on which it is negative is horizontal by relative ampleness; normalize it).
Dictionary: `Γ.ι` is the inclusion, `ν` the normalization (`functionFieldDegree ν = 1`, generic point
to generic point), `ν ≫ Γ.ι ≫ YGG.proj f κ` is `ρ₀` (finite, surjective, generic point to generic
point); `H_k·Γ = Γ.degree (polarization f κ m) / m` for `m` with `𝒮^{(m)}` generated in degree one
(`SufficientlyDivisible m`, `q ∣ m` for all `q ≤ k`), and the conclusion is stated as
`θ < −(Γ.degree B_m)/(m·deg ρ₀)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **A negative horizontal curve** (Lemma 2.5 of the paper): a curve `Γ ⊂ Y_κ^GG` with its normalization `ν : C̃₀ → Γ`
and `ρ₀ = ν ≫ Γ.ι ≫ π_κ` finite surjective, such that `θ = d h_κ/(2(n+1)κ) < −(H_κ·Γ)/deg ρ₀`, where
`H_κ·Γ = Γ.degree (O(m)) / m` for a sufficiently divisible `m`. -/
theorem negative_horizontal {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
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
            / ((m : ℚ) * (functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) : ℚ)) :=
  negative_horizontal_curve f hd κ hκ

end
