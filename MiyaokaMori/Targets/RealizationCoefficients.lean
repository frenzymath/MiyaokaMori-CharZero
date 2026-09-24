import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Realization.CoefficientCutoff
import MiyaokaMori.Paper.S3PositiveLine.Realization.ExcludeScalarJets

/-! # Vanishing of the high realization coefficients (Lemma 4.1 of the paper)

**Lemma 4.1** ("Coefficient vanishing and nonconstant projection").

Let `ρ : C̃ → C`, `L` and `ȷ : C̃_(k)(L) → 𝒵^×` be as in Lemma 3.1
(`Targets/AffineLiftAfterBaseChange.lean`: `J : BasedJet f ρ L κ` restricting to `s ∘ ρ` on the zero
section, with nowhere-zero positive-order coefficient tuple `NormalizedTupleNowhereZero J`), and
`deg L > 0` (Proposition 3.2). Put `r_k = ⌊a · deg ρ / deg L⌋`, `a = deg f^*O_X(1)`.
Composing `ȷ` with the cone embedding gives the `N + 1` coordinate sections
`P_ℓ^{(k)} = π_L^*(ρ^*f_ℓ) + Σ_{q=1}^k π_L^*B_{ℓ,q} ξ^q`, `B_{ℓ,q} ∈ H⁰(C̃, ρ^*A ⊗ L^{-q})`
(4.1). Then
(i) `B_{ℓ,q} = 0` for every `ℓ` and `r_k < q ≤ k`;
(ii) the composite `C̃_(k)(L) → 𝒵^× → X` is nonconstant in the jet parameter over the generic point of `C̃`;
in particular `r_k ≥ 1`.

**Dictionary.** `P_ℓ^{(k)}` is `J.coneCoordinate ℓ`, its expansion is `jet_coefficient_expansion`
(`Paper/S3PositiveLine/JetNeighborhood/CoefficientSections.lean`), and `B_{ℓ,q}` is
`J.coefficient ℓ q : H⁰(C̃, (ρ^*A)^{⊗1} ⊗ L^{-q})` — the `q`-th component of `P_ℓ^{(k)}` under
`π_{L*}O_{C̃_(k)(L)} = ⊕_{q=0}^k L^{-q}` (`xiCoefficientThickening`;
`Paper/S3PositiveLine/JetNeighborhood/NormalizedTupleNowhereZero.lean`). `r_k` is the integer division
`(f^*O_X(1)).degree * ρ.degree / L.degree`, which is the floor since `deg L > 0`; the paper writes `r_k`
for what the older Lean text (`realization`) calls `r₀`. Item (ii) is `¬ J.IsGenericallyScalar`
(`Paper/S3PositiveLine/JetNeighborhood/GenericallyScalar.lean`): `J` is generically scalar when over
some nonempty open `U ⊆ C̃` it equals `u · (s ∘ ρ ∘ π_L)` for a unit `u` of the truncated algebra with
constant term `1`, i.e. when its projection to `X` is the constant jet `f ∘ ρ` over `U` — exactly the
situation the paper's proof of (ii) rules out ("its homogeneous coordinate tuple would be proportional
to `ρ^*s` modulo `t^{k+1}`"). The statement also records the intermediate
fact "some positive-order coefficient survives" as an explicit conjunct.

**Proof (self-contained).**
1. *Vanishing of higher coefficients.* The coefficient bundle `ρ^*A ⊗ L^{-q}` has degree
   `a·deg ρ − q·deg L`, negative for `q > r_k`; a line bundle of negative degree on a smooth projective
   curve has no nonzero global section, so `B_{ℓ,q} = 0` (`BasedJet.coefficient_eq_zero_of_gt_r0`,
   from `coefficient_degree_bound` / `no_global_sections_of_degree_neg`). We state it for every
   `q > r_k`, which contains the paper's range `r_k < q ≤ k` (for `q > k` the coefficient is `0` by
   definition).
2. *Nonconstant projection.* Suppose `J` were generically scalar: over a nonempty open `U`,
   `J = u · (s ∘ ρ ∘ π_L)`. Then on `π_L⁻¹U` each cone coordinate is `u · π_L^*ρ^*f_ℓ`
   (`BasedJet.coneCoordinate_restrict_of_eq_scale`), so the coordinate minors
   `(ρ^*f_i) B_{j,q} − (ρ^*f_j) B_{i,q}` vanish over `U`, hence everywhere (sections of a locally free
   sheaf on the thickening vanishing on a dense open vanish); `ρ^*s` has no common zero, so
   `B_q = (ρ^*s) ⊗ η_q` with `η_q ∈ H⁰(C̃, L^{-q})`, and `H⁰(C̃, L^{-q}) = 0` for `q ≥ 1` because
   `deg L > 0` (functions on the thickening are pulled back from `C̃`,
   `jetNeighborhood.appTop_eq_proj_zeroSection_of_degree_pos`). So every `B_{ℓ,q}` with `1 ≤ q ≤ k`
   vanishes (`BasedJet.coefficient_eq_zero_of_coneCoordinate_restrict_eq_smul`), contradicting the
   nowhere-zero positive-order tuple at any point of `C̃` (`not_genericallyScalar_of_degree_pos`,
   `Paper/S3PositiveLine/Realization/ExcludeScalarJets.lean`).
3. *`r_k ≥ 1`.* By 2 the jet is not generically scalar, so some `B_{ℓ,q}` with `1 ≤ q ≤ k` is nonzero
   (`jet_coefficient_ne_zero_of_not_scalar`: if all positive-order coefficients vanished the jet would
   be the constant seed jet, hence scalar with `u = 1`); by step 1 this forces `q ≤ r_k`, i.e.
   `deg L ≤ q·deg L ≤ a·deg ρ` and `r_k = ⌊a·deg ρ / deg L⌋ ≥ 1`
   (`BasedJet.one_le_r0_of_not_genericallyScalar`).

Hypotheses: those of Lemma 3.1's output (`ρ`, `L`, `J`, `hnz`) together with `deg L > 0`
(the paper's "and `deg L > 0` by Proposition 3.2"); `[CharZero k]` and `1 ≤ κ` are not needed and
are omitted. Consumed by `realization` (`Targets/Realization.lean`), which uses (ii) and `r_k ≥ 1`
exactly as the paper's proof of Theorem 4.2 does.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Lemma 4.1**: for `ρ`, `L`, `J` as in
Lemma 3.1 (nowhere-zero positive-order coefficient tuple) with `deg L > 0`, and
`r_k = ⌊deg(f^*O_X(1)) · deg ρ / deg L⌋`:
(i) the ambient coefficients `B_{ℓ,q} = J.coefficient ℓ q` vanish for `q > r_k`;
(ii) `J` is not generically scalar (the projected jet `C̃_(k)(L) → X` is nonconstant in the jet parameter
over the generic point of `C̃`); some positive-order coefficient `B_{ℓ,q}`, `1 ≤ q ≤ k`, is nonzero;
and `r_k ≥ 1`. See the module docstring for the proof. -/
theorem realization_coefficients {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)
    (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
    (hnz : NormalizedTupleNowhereZero J) (hL : 0 < L.degree) :
    (∀ (ℓ : Fin (X.embDim + 1)) (q : ℕ),
      (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree < (q : ℤ) →
        J.coefficient ℓ q = 0) ∧
    ¬ J.IsGenericallyScalar ∧
    (∃ (ℓ : Fin (X.embDim + 1)) (q : ℕ), 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) ∧
    1 ≤ (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree := by
  have hns : ¬ J.IsGenericallyScalar := not_genericallyScalar_of_degree_pos f κ ρ L hL J hnz
  exact ⟨fun ℓ q hq => BasedJet.coefficient_eq_zero_of_gt_r0 J hL ℓ q hq, hns,
    BasedJet.exists_coefficient_ne_zero_of_not_genericallyScalar J hns,
    BasedJet.one_le_r0_of_not_genericallyScalar J hL hns⟩

end
