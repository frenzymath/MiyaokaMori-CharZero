import MiyaokaMori.Prelude
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.Regular.Free

/-! # Change of rings for the projective dimension (Stacks 00O7)

Change of rings for projective dimension along `R → R/(x)`, `x` a nonzerodivisor of a Noetherian
local ring `R` lying in the maximal ideal: for a finite `R/(x)`-module `N`,
`pd_R N ≤ pd_{R/(x)} N + 1`.

Source: Stacks 00O7 is proved here (see `Stacks00o7GlobalDimension.lean`) by induction on `dim R`
with the Matsumura / Bruns–Herzog change-of-rings inequality
`pd_R N ≤ pd_S N + pd_R S` for `S = R/(x)` (Bruns–Herzog, *Cohen–Macaulay rings*, Lemma 1.3.x-style
"first change of rings"; the case needed is `pd_R S = 1`, i.e. `0 → R --x--> R → S → 0`).
The proof below is self-contained:

* `pd_R (S^m) ≤ 1`: `S^m ≅ R^m / x R^m` as `R`-modules and Mathlib's
  `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular` gives `pd (R^m/xR^m) = pd R^m + 1 = 1`.
* Induction on `n := pd_S N`. `n = 0`: `N` is projective over `S`, so a retract of some `S^m`
  (lift the identity along a surjection `S^m → N`), hence a retract of `S^m` as `R`-modules, and
  `pd_R N ≤ pd_R S^m ≤ 1`. `n + 1`: choose `0 → K → S^m → N → 0` (`K` finite since `S` is Noetherian);
  `pd_S K ≤ n` (dimension shift); by induction `pd_R K ≤ n + 1`; `pd_R S^m ≤ 1 ≤ n + 2`; so
  `pd_R N ≤ n + 2` by the dimension-shift lemma for the same sequence read over `R`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Abelian
open scoped Pointwise

noncomputable section

variable {R : Type u} [CommRing R]

/-- In `Fin m → R`, the submodule of vectors with all coordinates in `(x)` is `x • ⊤`. -/
theorem Submodule.pi_univ_span_singleton_eq_pointwise_smul_top (x : R) (m : ℕ) :
    Submodule.pi (Set.univ : Set (Fin m)) (fun _ => (Ideal.span {x} : Submodule R R)) =
      x • (⊤ : Submodule R (Fin m → R)) := by
  ext v
  rw [Submodule.mem_pi, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro h
    choose w hw using fun i => Ideal.mem_span_singleton'.mp (h i (Set.mem_univ i))
    refine ⟨w, Submodule.mem_top, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, hw i]
  · rintro ⟨w, -, rfl⟩ i -
    exact Ideal.mem_span_singleton'.mpr ⟨w i, by rw [Pi.smul_apply, smul_eq_mul, mul_comm]⟩

/-- `R^m / x R^m ≅ (R/(x))^m` as `R`-modules. -/
def quotSMulTopPiEquivPiQuotient (x : R) (m : ℕ) :
    QuotSMulTop x (Fin m → R) ≃ₗ[R] (Fin m → R ⧸ Ideal.span {x}) :=
  (Submodule.quotEquivOfEq _ _ (Submodule.pi_univ_span_singleton_eq_pointwise_smul_top x m).symm).trans
    (Submodule.quotientPi (fun _ : Fin m => (Ideal.span {x} : Submodule R R)))

/-- `pd_R ((R/(x))^m) ≤ 1` for a nonzerodivisor `x` in the maximal ideal of a Noetherian local ring. -/
theorem hasProjectiveDimensionLE_pi_quotient_span_singleton [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : IsSMulRegular R x) (hmem : x ∈ IsLocalRing.maximalIdeal R) (m : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R (Fin m → R ⧸ Ideal.span {x})) 1 := by
  have hreg : IsSMulRegular (Fin m → R) x := fun v w h => funext fun i => hx (congrFun h i)
  have h1 := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
    (ModuleCat.of R (Fin m → R)) x hreg hmem
  have : Projective (ModuleCat.of R (Fin m → R)) := ModuleCat.projective_of_free (Pi.basisFun R (Fin m))
  have h2 : projectiveDimension (ModuleCat.of R (Fin m → R)) ≤ 0 := by
    have := (projectiveDimension_le_iff (ModuleCat.of R (Fin m → R)) 0).mpr inferInstance
    simpa using this
  have h3 : projectiveDimension (ModuleCat.of R (QuotSMulTop x (Fin m → R))) ≤ 1 := by
    calc projectiveDimension (ModuleCat.of R (QuotSMulTop x (Fin m → R)))
        = projectiveDimension (ModuleCat.of R (Fin m → R)) + 1 := h1
      _ ≤ 0 + 1 := add_le_add h2 le_rfl
      _ = 1 := zero_add 1
  have : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop x (Fin m → R))) 1 :=
    (projectiveDimension_le_iff _ 1).mp (by simpa using h3)
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
    (M := ModuleCat.of R (QuotSMulTop x (Fin m → R))) (quotSMulTopPiEquivPiQuotient x m) 1

/-- **Change of rings** (`S = R/(x)`, `x` a nonzerodivisor in the maximal ideal of the Noetherian
local ring `R`): a finite `S`-module `N` with `pd_S N ≤ n` has `pd_R N ≤ n + 1`. -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient_span_singleton
    [IsLocalRing R] [IsNoetherianRing R] {x : R} (hx : IsSMulRegular R x)
    (hmem : x ∈ IsLocalRing.maximalIdeal R) (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module (R ⧸ Ideal.span {x}) N]
      [IsScalarTower R (R ⧸ Ideal.span {x}) N] [Module.Finite (R ⧸ Ideal.span {x}) N],
      HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x}) N) n →
        HasProjectiveDimensionLE (ModuleCat.of R N) (n + 1) := by
  induction n with
  | zero =>
    intro N _ _ _ _ _ h
    have : Projective (ModuleCat.of (R ⧸ Ideal.span {x}) N) :=
      projective_iff_hasProjectiveDimensionLT_one.mpr h
    have hproj : Module.Projective (R ⧸ Ideal.span {x}) N :=
      (IsProjective.iff_projective N).mpr this
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (R ⧸ Ideal.span {x}) N
    obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
    have hr : Retract (ModuleCat.of R N) (ModuleCat.of R (Fin m → R ⧸ Ideal.span {x})) :=
      { i := ModuleCat.ofHom (g.restrictScalars R)
        r := ModuleCat.ofHom (f.restrictScalars R)
        retract := by
          ext v
          have := LinearMap.congr_fun hg v
          simpa using this }
    have := hasProjectiveDimensionLE_pi_quotient_span_singleton hx hmem m
    exact hr.hasProjectiveDimensionLT 2
  | succ n ih =>
    intro N _ _ _ _ _ h
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (R ⧸ Ideal.span {x}) N
    have hS := LinearMap.shortExact_shortComplexKer hf
    have : Projective (ModuleCat.of (R ⧸ Ideal.span {x}) (Fin m → R ⧸ Ideal.span {x})) :=
      ModuleCat.projective_of_free (Pi.basisFun _ (Fin m))
    have hK : HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x}) (LinearMap.ker f)) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
    have hKR := ih (LinearMap.ker f) hK
    have hR := LinearMap.shortExact_shortComplexKer (f := f.restrictScalars R) hf
    have : HasProjectiveDimensionLE
        (ModuleCat.of R (LinearMap.ker (f.restrictScalars R))) (n + 1) := by
      have := hKR
      refine ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
        (M := ModuleCat.of R (LinearMap.ker f)) ?_ (n + 1)
      exact (({ AddEquiv.refl (LinearMap.ker f) with map_smul' := fun _ _ => rfl } :
          LinearMap.ker f ≃ₗ[R] (LinearMap.ker f).restrictScalars R).trans
        (LinearEquiv.ofEq _ _ (LinearMap.ker_restrictScalars (R := R) f).symm))
    have := hasProjectiveDimensionLE_pi_quotient_span_singleton hx hmem m
    exact hR.hasProjectiveDimensionLT_X₃ (n + 2) inferInstance
      (hasProjectiveDimensionLT_of_ge _ 2 (n + 3) (by omega))

end
