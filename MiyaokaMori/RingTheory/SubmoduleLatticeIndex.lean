import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Length.PeriodicComplexLength
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Lattice index and `Ring.ordFrac` (algebra behind `rationalSectionOrd`)

For submodules `N S` of an `R`-module `V` the **lattice index**
`[N : S] := ℓ(N / (N ⊓ S)) − ℓ(S / (N ⊓ S)) ∈ ℤ` (lengths via `PeriodicComplex.relLength`, cast with `ENat.toNat`)
is the signed "number of steps" from `S` to `N`. It is the module-theoretic form of the order of vanishing:
for `R` a Noetherian domain of Krull dimension ≤ 1 with fraction field `K`, a `K`-vector space `V` (an `R`-module by
restriction of scalars), `t ≠ 0` in `V` and `g ≠ 0` in `K`,

  `Ring.ordFrac R g = ofAdd [R•t : R•(g•t)]`   (`LatticeOrd.ordFrac_eq_latticeIndex`).

Proof (Stacks 02MD, the definition `ord_A(a/b) = ℓ(A/aA) − ℓ(A/bA)` of the order of vanishing on a fraction field,
made lattice-invariant): write `g = a/b` with `a, b ∈ R∖0` (`IsLocalization.mk'_surjective`), so `b•(g•t) = a•t`.
The submodule `C := R•(a•t)` lies in both `R•t` and `R•(g•t)`; by the chain additivity of relative lengths
(`PeriodicComplex.relLength_add`, i.e. `Module.length_eq_add_of_exact`) `[N : S] = ℓ(N/C) − ℓ(S/C)` for any
`C ≤ N ⊓ S` with both lengths finite (`Submodule.latticeIndex_eq_of_le`). Since `x ↦ (r ↦ r•x)` identifies `R` with
`R•x` for `x ≠ 0` in a torsion-free module (`LinearEquiv.toSpanNonzeroSingleton`), it carries `aR` onto `R•(a•x)`, so
`ℓ(R•x / R•(a•x)) = ℓ(R/aR) = Ring.ord R a` (`LatticeOrd.relLength_span_smul_singleton`). With `x = t` and
`x = g•t` (and `a•t = b•(g•t)`) this gives `[R•t : R•(g•t)] = ord a − ord b`, which is `Ring.ordFrac R (a/b)` by
`Ring.ordFrac_eq_div`; the lengths are finite by `Ring.ord_ne_top` (Krull dimension ≤ 1, Noetherian).

Used by the choice-free definition of `rationalSectionOrd` and its evaluation by a trivialization
coordinate.
Source: Stacks 02MD (`Ring.ord`, `Ring.ordFrac`), 02SE (order of a rational section along a prime
divisor); §2 of the paper.
-/

set_option autoImplicit false

open Submodule PeriodicComplex

section LatticeIndex

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Lattice index `[N : S] := ℓ(N/(N ⊓ S)) − ℓ(S/(N ⊓ S))` of two submodules, as an integer
(`PeriodicComplex.relLength A B = ℓ(B/(A ⊓ B))`; an infinite length is cast to `0` by `ENat.toNat`, so the
value is meaningful only when both lengths are finite, e.g. when `N` and `S` are commensurable lattices). -/
noncomputable def Submodule.latticeIndex (N S : Submodule R M) : ℤ :=
  ((relLength S N).toNat : ℤ) - ((relLength N S).toNat : ℤ)

/-- The lattice index can be computed from any common sublattice `C ≤ N ⊓ S` with `ℓ(N/C), ℓ(S/C) < ∞`:
`[N : S] = ℓ(N/C) − ℓ(S/C)` (chain additivity of lengths). -/
theorem Submodule.latticeIndex_eq_of_le {C N S : Submodule R M} (hCN : C ≤ N) (hCS : C ≤ S)
    (hN : relLength C N ≠ ⊤) (hS : relLength C S ≠ ⊤) :
    N.latticeIndex S = ((relLength C N).toNat : ℤ) - ((relLength C S).toNat : ℤ) := by
  have hSN : relLength (N ⊓ S) N = relLength S N := by
    rw [inf_comm]; exact relLength_congr_inf S N
  have h1 : relLength C N = relLength C (N ⊓ S) + relLength S N := by
    rw [relLength_add (le_inf hCN hCS) inf_le_left, hSN]
  have h2 : relLength C S = relLength C (N ⊓ S) + relLength N S := by
    rw [relLength_add (le_inf hCN hCS) inf_le_right, relLength_congr_inf]
  have hx : relLength C (N ⊓ S) ≠ ⊤ := fun h => hN (by rw [h1, h, top_add])
  have hSN' : relLength S N ≠ ⊤ := fun h => hN (by rw [h1, h, add_top])
  have hNS' : relLength N S ≠ ⊤ := fun h => hS (by rw [h2, h, add_top])
  unfold Submodule.latticeIndex
  rw [h1, h2, ENat.toNat_add hx hSN', ENat.toNat_add hx hNS']
  push_cast
  ring

end LatticeIndex

namespace LatticeOrd

section Cyclic

variable {R : Type*} [CommRing R] [IsDomain R] {V : Type*} [AddCommGroup V] [Module R V]
  [Module.IsTorsionFree R V]

/-- `ℓ(R•x / R•(a•x)) = Ring.ord R a` for `x ≠ 0` in a torsion-free module: `r ↦ r•x` identifies `R` with `R•x`
and carries the ideal `aR` onto `R•(a•x)`. -/
theorem relLength_span_smul_singleton (x : V) (hx : x ≠ 0) (a : R) :
    relLength (span R {a • x}) (span R {x}) = Ring.ord R a := by
  unfold relLength Ring.ord
  let e := LinearEquiv.toSpanNonzeroSingleton R V x hx
  have hmap : Submodule.map (e : R →ₗ[R] ↥(span R {x})) (Ideal.span {a}) =
      (span R {a • x}).submoduleOf (span R {x}) := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Ideal.mem_span_singleton', Submodule.submoduleOf,
      Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨r, ⟨c, rfl⟩, hr⟩
      refine ⟨c, ?_⟩
      have h := congrArg Subtype.val hr
      simp only [LinearEquiv.coe_coe, e, LinearEquiv.toSpanNonzeroSingleton_apply] at h
      rw [smul_smul]
      exact h
    · rintro ⟨c, hc⟩
      refine ⟨c * a, ⟨c, rfl⟩, ?_⟩
      apply Subtype.ext
      simp only [LinearEquiv.coe_coe, e, LinearEquiv.toSpanNonzeroSingleton_apply]
      rw [mul_smul]
      exact hc
  exact ((Submodule.Quotient.equiv (Ideal.span {a}) _ e hmap).length_eq).symm

end Cyclic

section FractionRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- A `K`-vector space is torsion-free over `R` (restriction of scalars along the injective `R → K`). -/
theorem isTorsionFree_of_isScalarTower (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [Module K V] [IsScalarTower R K V] : Module.IsTorsionFree R V :=
  Module.IsTorsionFree.comap (algebraMap R K)
    (fun r hr => isRegular_iff_ne_zero.2
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).2 (isRegular_iff_ne_zero.1 hr)))
    (fun r m => algebraMap_smul K r m)

/-- **`ordFrac` as a lattice index**: for `t ≠ 0` in `V` and `g ≠ 0` in `K`,
`Ring.ordFrac R g = ofAdd [R•t : R•(g•t)]` (Stacks 02MD: `ord(a/b) = ℓ(R/aR) − ℓ(R/bR)`). -/
theorem ordFrac_eq_latticeIndex {t : V} (ht : t ≠ 0) {g : K} (hg : g ≠ 0) :
    Ring.ordFrac R g =
      ((Multiplicative.ofAdd ((span R {t}).latticeIndex (span R {g • t})) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  haveI : Module.IsTorsionFree R V := isTorsionFree_of_isScalarTower K
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) g
  simp only at hab
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have hkey : (b : R) • (g • t) = a • t := by
    rw [← algebraMap_smul K (b : R) (g • t), smul_smul, ← algebraMap_smul K a t, ← hab, mul_comm,
      IsLocalization.mk'_spec]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hg
    have h0 : (b : R) • (g • t) = 0 := by rw [hkey, zero_smul]
    rw [← algebraMap_smul K (b : R), smul_smul] at h0
    have h2 := (smul_eq_zero.1 h0).resolve_right ht
    exact (mul_eq_zero.1 h2).resolve_left hbK
  have ha : a ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero ha0
  have hgt : g • t ≠ 0 := smul_ne_zero hg ht
  have hCN : span R {a • t} ≤ span R {t} := by
    rw [span_le, Set.singleton_subset_iff]
    exact smul_mem _ _ (mem_span_singleton_self t)
  have hCS : span R {a • t} ≤ span R {g • t} := by
    rw [← hkey, span_le, Set.singleton_subset_iff]
    exact smul_mem _ _ (mem_span_singleton_self _)
  have hN : relLength (span R {a • t}) (span R {t}) = Ring.ord R a :=
    relLength_span_smul_singleton t ht a
  have hS : relLength (span R {a • t}) (span R {g • t}) = Ring.ord R b := by
    rw [← hkey]; exact relLength_span_smul_singleton (g • t) hgt (b : R)
  have hNt : relLength (span R {a • t}) (span R {t}) ≠ ⊤ := by rw [hN]; exact Ring.ord_ne_top ha
  have hSt : relLength (span R {a • t}) (span R {g • t}) ≠ ⊤ := by
    rw [hS]; exact Ring.ord_ne_top b.2
  have hdiv : Ring.ordFrac R g =
      Ring.ordMonoidWithZeroHom R a / Ring.ordMonoidWithZeroHom R (b : R) := by
    rw [← hab]; exact Ring.ordFrac_eq_div R ⟨a, ha⟩ b
  rw [Submodule.latticeIndex_eq_of_le hCN hCS hNt hSt, hN, hS, hdiv,
    Ring.ordMonoidWithZeroHom_eq_coe R ha (ENat.natCast_toNat_eq_self.2 (Ring.ord_ne_top ha)).symm,
    Ring.ordMonoidWithZeroHom_eq_coe R b.2 (ENat.natCast_toNat_eq_self.2 (Ring.ord_ne_top b.2)).symm,
    ofAdd_sub, WithZero.coe_div]

end FractionRing

end LatticeOrd
