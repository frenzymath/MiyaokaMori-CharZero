import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00np
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nq
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00o7ChangeOfRings

/-! # Stacks 00O7, the case `e = 0`: finite modules over a regular local ring

**Stacks 00O7, the case `e = 0`** (this is the only form the users Stacks 00OC, 00OF, 0AFZ need): over a regular local ring `R` of dimension `d`,
every finite module `M` has projective dimension `≤ d`
(`IsRegularLocalRing.hasProjectiveDimensionLE_of_finite`; also stated as
`projectiveDimension (ModuleCat.of R M) ≤ ringKrullDim R`).

Source: Stacks 00O7 (algebra-proposition-regular-finite-gl-dim). The proof here is **not** the Stacks
depth/CM argument (00NG/00NT) but the elementary induction on `dim R` via change of rings
(Matsumura, *Commutative Ring Theory*, proof of Thm 19.2 / Bruns–Herzog Thm 2.2.7 direction
"regular ⇒ finite global dimension"), which needs only facts already in the library:

1. `dim R = 0`: `R` is a field (`m = ⊥`, Nakayama not needed: `spanFinrank m = dim R = 0`), every
   module is free, `pd = 0`.
2. `dim R ≤ d + 1`, `m ≠ ⊥`: Nakayama gives `m ≠ m²`; pick `x ∈ m ∖ m²`. Then `R/(x)` is regular of
   dimension `≤ d` (Stacks 00NQ: `IsRegularLocalRing.quotient_span_singleton`,
   `spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le`), and `x` is a nonzerodivisor
   (Stacks 00NP: regular local rings are domains). For finite `M` choose `0 → K → R^m → M → 0`;
   `K ⊆ R^m` is torsion-free so `x` is `K`-regular, hence
   `pd_R (K/xK) = pd_R K + 1` (Mathlib `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular`).
   `K/xK` is a finite `R/(x)`-module, so `pd_{R/(x)} (K/xK) ≤ d` by induction, and
   `pd_R (K/xK) ≤ d + 1` by change of rings (`Stacks00o7ChangeOfRings`). Thus `pd_R K ≤ d` and
   `pd_R M ≤ d + 1` (dimension shift along `0 → K → R^m → M → 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Abelian
open scoped Pointwise

noncomputable section

/-- A local ring with `m = ⊥` is a field; every module over it is free, hence projective. -/
theorem IsLocalRing.hasProjectiveDimensionLE_zero_of_maximalIdeal_eq_bot {R : Type u} [CommRing R]
    [IsLocalRing R] (h : IsLocalRing.maximalIdeal R = ⊥) (M : Type u) [AddCommGroup M]
    [Module R M] : HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by
  let _ : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h).toField
  have : Module.Free R M := Module.Free.of_divisionRing R M
  have : Projective (ModuleCat.of R M) := ModuleCat.projective_of_free (Module.Free.chooseBasis R M)
  infer_instance

/-- In a Noetherian local ring with `m ≠ ⊥` there is `x ∈ m ∖ m²` (Nakayama: `m = m²` forces `m = ⊥`). -/
theorem IsLocalRing.exists_mem_maximalIdeal_notMem_sq {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (hbot : IsLocalRing.maximalIdeal R ≠ ⊥) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, x ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  by_contra hcon
  push Not at hcon
  apply hbot
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro y hy
  rw [smul_eq_mul, ← pow_two]
  exact hcon y hy

/-- **Stacks 00O7 with `e = 0`, induction form**: if `R` is a regular local ring with
`dim R ≤ d`, every finite `R`-module has projective dimension `≤ d`. -/
theorem IsRegularLocalRing.hasProjectiveDimensionLE_of_ringKrullDim_le (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], ringKrullDim R ≤ d →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
        HasProjectiveDimensionLE (ModuleCat.of R M) d := by
  induction d with
  | zero =>
    intro R _ _ hd M _ _ _
    have h1 : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal]; exact_mod_cast hd
    have h2 : (IsLocalRing.maximalIdeal R).spanFinrank = 0 :=
      Nat.le_zero.mp (by exact_mod_cast h1)
    have h3 : IsLocalRing.maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h2
    exact IsLocalRing.hasProjectiveDimensionLE_zero_of_maximalIdeal_eq_bot h3 M
  | succ d ih =>
    intro R _ _ hd M _ _ _
    by_cases hbot : IsLocalRing.maximalIdeal R = ⊥
    · have := IsLocalRing.hasProjectiveDimensionLE_zero_of_maximalIdeal_eq_bot hbot M
      exact hasProjectiveDimensionLT_of_ge _ 1 (d + 2) (by omega)
    obtain ⟨x, hx, hx2⟩ := IsLocalRing.exists_mem_maximalIdeal_notMem_sq hbot
    have hS : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
      IsRegularLocalRing.quotient_span_singleton hx hx2
    -- `dim R/(x) ≤ d`
    have hdimS : ringKrullDim (R ⧸ Ideal.span {x}) ≤ d := by
      have h1 := IsLocalRing.spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le hx hx2
      have h2 : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
        rw [IsRegularLocalRing.spanFinrank_maximalIdeal]; exact_mod_cast hd
      have h3 : (IsLocalRing.maximalIdeal R).spanFinrank ≤ d + 1 := by exact_mod_cast h2
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ Ideal.span {x})]
      exact_mod_cast (show (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ d by omega)
    -- `x` is a nonzerodivisor (regular local rings are domains, Stacks 00NP)
    have hx0 : x ≠ 0 := fun h => hx2 (h ▸ zero_mem _)
    have hxreg : IsSMulRegular R x := fun a b h => mul_left_cancel₀ hx0 h
    -- the syzygy `K = ker (R^m → M)`
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
    have hSE := LinearMap.shortExact_shortComplexKer hf
    have : Projective (ModuleCat.of R (Fin m → R)) :=
      ModuleCat.projective_of_free (Pi.basisFun R (Fin m))
    have hKreg : IsSMulRegular (LinearMap.ker f) x := fun k₁ k₂ h => Subtype.ext (funext fun i =>
      hxreg (by simpa only [Submodule.coe_smul, Pi.smul_apply] using
        congrFun (congrArg Subtype.val h) i))
    have hpdK := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (LinearMap.ker f)) x hKreg hx
    have hfinS : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x (LinearMap.ker f)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hQ := ih (R ⧸ Ideal.span {x}) hdimS (QuotSMulTop x (LinearMap.ker f))
    have hQR := hasProjectiveDimensionLE_restrictScalars_quotient_span_singleton hxreg hx d
      (QuotSMulTop x (LinearMap.ker f)) hQ
    -- `pd_R K + 1 = pd_R (K/xK) ≤ d + 1`, so `pd_R K ≤ d`
    have hK : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) d := by
      rw [← projectiveDimension_le_iff]
      have h1 : projectiveDimension (ModuleCat.of R (QuotSMulTop x (LinearMap.ker f))) ≤
          ((d + 1 : ℕ) : WithBot ℕ∞) := (projectiveDimension_le_iff _ _).mpr hQR
      rw [hpdK] at h1
      have h2 : projectiveDimension (ModuleCat.of R (LinearMap.ker f)) + ((1 : ℕ) : WithBot ℕ∞) ≤
          (d : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by
        push_cast at h1 ⊢; exact h1
      exact ENat.WithBot.add_le_add_natCast_right_iff.mp h2
    exact (hSE.hasProjectiveDimensionLT_X₃_iff d inferInstance).mpr hK

/-- **Stacks 00O7 with `e = 0`**: over a regular local ring `R` with `dim R = d`, every finite
module has projective dimension `≤ d`. This is the form used by Stacks 00OC, 00OF and 0AFZ. -/
theorem IsRegularLocalRing.hasProjectiveDimensionLE_of_finite {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : ℕ) (hd : ringKrullDim R = d) : HasProjectiveDimensionLE (ModuleCat.of R M) d :=
  IsRegularLocalRing.hasProjectiveDimensionLE_of_ringKrullDim_le d R hd.le M

/-- **Stacks 00O7 with `e = 0`, `projectiveDimension` form**: `pd M ≤ dim R` for every finite
module over a regular local ring. -/
theorem IsRegularLocalRing.projectiveDimension_le_ringKrullDim {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    projectiveDimension (ModuleCat.of R M) ≤ ringKrullDim R := by
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)]
  exact (projectiveDimension_le_iff _ _).mpr
    (IsRegularLocalRing.hasProjectiveDimensionLE_of_finite M _
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm)

end
