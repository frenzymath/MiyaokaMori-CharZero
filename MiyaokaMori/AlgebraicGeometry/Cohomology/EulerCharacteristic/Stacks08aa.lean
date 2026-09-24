import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearLongExact

/-! # Additivity of the Euler characteristic (Stacks 08AA)

The Euler characteristic is additive on short exact sequences (Stacks 08AA): for a short exact sequence
`0 → F_1 → F_2 → F_3 → 0` of coherent sheaves on a proper scheme over a field, `χ(F_2) = χ(F_1) + χ(F_3)`.

Source: Stacks 08AA (varieties-lemma-euler-characteristic-additive).

Route: the `K`-linear long exact sequence (`range = ker` at the three places) plus rank–nullity: with
`k_n := dim ker(H^n(F_1) → H^n(F_2))`, `h^n(F_1) − h^n(F_2) + h^n(F_3) = k_n + k_{n+1}`; the alternating
sum telescopes to `k_0 + (−1)^d k_{d+1}`, where `k_0 = 0` (`H^0` preserves monomorphisms,
`Ext.postcomp_mk₀_injective_of_mono`) and `k_{d+1} = 0` (Grothendieck vanishing, `d = dim X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Telescoping sum: `Σ_{n ≤ N} (−1)^n (k_n + k_{n+1}) = k_0 + (−1)^N k_{N+1}`. -/
theorem Stacks08aa.sum_neg_one_pow_mul_add_succ (k : ℕ → ℤ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (k n + k (n + 1)) =
      k 0 + (-1 : ℤ) ^ N * k (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- **Alternating sum of dimensions along an exact sequence** (the linear-algebra core of Stacks 08AA).
Given finite-dimensional `K`-vector spaces `A_n, B_n, C_n` and linear maps `f_n : A_n → B_n`,
`g_n : B_n → C_n`, `δ_n : C_n → A_{n+1}`, exact (`range = ker`) at `B_n`, `C_n` and `A_{n+1}`,
`Σ_{n ≤ N} (−1)^n (dim A_n − dim B_n + dim C_n) = dim ker f_0 + (−1)^N dim ker f_{N+1}`.

Proof: rank–nullity three times: `dim B_n = dim range g_n + dim ker g_n = dim ker δ_n + dim range f_n`;
`dim A_n = dim range f_n + dim ker f_n`; `dim C_n = dim range δ_n + dim ker δ_n`; and
`range δ_n = ker f_{n+1}`, so `dim A_n − dim B_n + dim C_n = dim ker f_n + dim ker f_{n+1}`; then telescope. -/
theorem Stacks08aa.alternating_sum_finrank_of_exact {K : Type v} [Field K]
    {A B C : ℕ → Type w}
    [∀ n, AddCommGroup (A n)] [∀ n, Module K (A n)] [∀ n, FiniteDimensional K (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module K (B n)] [∀ n, FiniteDimensional K (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)] [∀ n, FiniteDimensional K (C n)]
    (f : ∀ n, A n →ₗ[K] B n) (g : ∀ n, B n →ₗ[K] C n) (δ : ∀ n, C n →ₗ[K] A (n + 1))
    (hfg : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (hgδ : ∀ n, LinearMap.range (g n) = LinearMap.ker (δ n))
    (hδf : ∀ n, LinearMap.range (δ n) = LinearMap.ker (f (n + 1))) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n *
        ((Module.finrank K (A n) : ℤ) - Module.finrank K (B n) + Module.finrank K (C n)) =
      (Module.finrank K (LinearMap.ker (f 0)) : ℤ) +
        (-1 : ℤ) ^ N * Module.finrank K (LinearMap.ker (f (N + 1))) := by
  have hterm : ∀ n, ((Module.finrank K (A n) : ℤ) - Module.finrank K (B n) + Module.finrank K (C n)) =
      (Module.finrank K (LinearMap.ker (f n)) : ℤ) + Module.finrank K (LinearMap.ker (f (n + 1))) := by
    intro n
    have hA := LinearMap.finrank_range_add_finrank_ker (f n)
    have hB := LinearMap.finrank_range_add_finrank_ker (g n)
    have hC := LinearMap.finrank_range_add_finrank_ker (δ n)
    rw [hfg n] at hA
    rw [hgδ n] at hB
    rw [hδf n] at hC
    omega
  rw [← Stacks08aa.sum_neg_one_pow_mul_add_succ (fun n => (Module.finrank K (LinearMap.ker (f n)) : ℤ)) N]
  exact Finset.sum_congr rfl fun n _ => by rw [hterm n]

/-- `H^0` preserves monomorphisms: for a short exact sequence `0 → M' → M → M'' → 0` of `O_X`-modules,
`H^0(X, M') → H^0(X, M)` is injective. Proof: `Sheaf.H.map f 0` is postcomposition with `Ext.mk₀ f` in
`Ext^0`, `f` is a monomorphism of abelian sheaves (`bridge_shortExact_toSheaf`), and Mathlib's
`Ext.postcomp_mk₀_injective_of_mono` applies. -/
theorem AlgebraicGeometry.sheafCohomology.map_f_injective_zero {X : AlgebraicGeometry.Scheme.{u}}
    {S : CategoryTheory.ShortComplex X.Modules} (hS : S.ShortExact) :
    Function.Injective (AlgebraicGeometry.sheafCohomology.map S.f 0) := by
  have hmono : CategoryTheory.Mono (AlgebraicGeometry.Scheme.Modules.toAddCommGrpSheafMap S.f) :=
    (AlgebraicGeometry.Scheme.Modules.shortExact_toAddCommGrpSheaf hS).mono_f
  intro x y hxy
  have h1 := AlgebraicGeometry.sheafCohomology.map_apply S.f 0 x
  have h2 := AlgebraicGeometry.sheafCohomology.map_apply S.f 0 y
  exact CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono _
    (AlgebraicGeometry.Scheme.Modules.toAddCommGrpSheafMap S.f) (h1.symm.trans (hxy.trans h2))

theorem AlgebraicGeometry.sheafEulerCharacteristic_additive {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (S : CategoryTheory.ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) X S.X₂ =
      AlgebraicGeometry.sheafEulerCharacteristic (k := k) X S.X₁ + AlgebraicGeometry.sheafEulerCharacteristic (k := k) X S.X₃ := by
  have hfin1 : ∀ n, FiniteDimensional k (AlgebraicGeometry.sheafCohomology X S.X₁ n) :=
    fun n => AlgebraicGeometry.sheafCohomology_finiteDimensional_of_isProperOver X hX S.X₁ n
  have hfin2 : ∀ n, FiniteDimensional k (AlgebraicGeometry.sheafCohomology X S.X₂ n) :=
    fun n => AlgebraicGeometry.sheafCohomology_finiteDimensional_of_isProperOver X hX S.X₂ n
  have hfin3 : ∀ n, FiniteDimensional k (AlgebraicGeometry.sheafCohomology X S.X₃ n) :=
    fun n => AlgebraicGeometry.sheafCohomology_finiteDimensional_of_isProperOver X hX S.X₃ n
  have key := Stacks08aa.alternating_sum_finrank_of_exact (K := k)
    (A := fun n => AlgebraicGeometry.sheafCohomology X S.X₁ n)
    (B := fun n => AlgebraicGeometry.sheafCohomology X S.X₂ n)
    (C := fun n => AlgebraicGeometry.sheafCohomology X S.X₃ n)
    (fun n => AlgebraicGeometry.sheafCohomology.mapOver k S.f n)
    (fun n => AlgebraicGeometry.sheafCohomology.mapOver k S.g n)
    (fun n => AlgebraicGeometry.sheafCohomology.δOver hS n (n + 1) rfl k)
    (fun n => AlgebraicGeometry.sheafCohomology.range_mapOver_f_eq_ker_mapOver_g hS k n)
    (fun n => AlgebraicGeometry.sheafCohomology.range_mapOver_g_eq_ker_δOver hS n (n + 1) rfl k)
    (fun n => AlgebraicGeometry.sheafCohomology.range_δOver_eq_ker_mapOver_f hS n (n + 1) rfl k)
    X.dimension
  -- `k_0 = 0`: `H^0` preserves monomorphisms
  have hk0 : Module.finrank k (LinearMap.ker (AlgebraicGeometry.sheafCohomology.mapOver k S.f 0)) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr, finrank_bot]
    intro x y hxy
    exact AlgebraicGeometry.sheafCohomology.map_f_injective_zero hS hxy
  -- `k_{d+1} = 0`: Grothendieck vanishing
  have hkN : Module.finrank k
      (LinearMap.ker (AlgebraicGeometry.sheafCohomology.mapOver k S.f (X.dimension + 1))) = 0 := by
    have := AlgebraicGeometry.sheafCohomology_subsingleton_of_dimension_lt X hX S.X₁ (X.dimension + 1)
      (Nat.lt_succ_self _)
    exact Module.finrank_zero_of_subsingleton
  rw [hk0, hkN] at key
  simp only [Nat.cast_zero, mul_zero, add_zero] at key
  rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_sum X hX S.X₁,
    AlgebraicGeometry.sheafEulerCharacteristic_eq_sum X hX S.X₂,
    AlgebraicGeometry.sheafEulerCharacteristic_eq_sum X hX S.X₃]
  have hsplit : ∑ n ∈ Finset.range (X.dimension + 1), (-1 : ℤ) ^ n *
        ((Module.finrank k (AlgebraicGeometry.sheafCohomology X S.X₁ n) : ℤ) -
          Module.finrank k (AlgebraicGeometry.sheafCohomology X S.X₂ n) +
          Module.finrank k (AlgebraicGeometry.sheafCohomology X S.X₃ n)) =
      ∑ n ∈ Finset.range (X.dimension + 1), (-1 : ℤ) ^ n *
          (Module.finrank k (AlgebraicGeometry.sheafCohomology X S.X₁ n) : ℤ) -
        ∑ n ∈ Finset.range (X.dimension + 1), (-1 : ℤ) ^ n *
          (Module.finrank k (AlgebraicGeometry.sheafCohomology X S.X₂ n) : ℤ) +
        ∑ n ∈ Finset.range (X.dimension + 1), (-1 : ℤ) ^ n *
          (Module.finrank k (AlgebraicGeometry.sheafCohomology X S.X₃ n) : ℤ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit] at key
  linarith

end
