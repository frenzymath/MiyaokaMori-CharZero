import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.OrderOfVanishing.LatticeDetOrd

/-! # The order of a norm as a length (Stacks 02MI)

Let `A` be a Noetherian domain of Krull dimension `≤ 1` (not necessarily local), `A ⊆ B` a finite extension of
domains, `K = Frac A`, `L = Frac B`, `y ∈ B ∖ 0`. Then (1) `length_A(B/yB) < ∞`;
(2) `ord_A(Nm_{L/K} y) = length_A(B/yB)`, in Mathlib terms
`Ring.ordFrac A (Algebra.norm K y) = WithZero.exp (length_A(B/yB))`. This is Stacks 02MI (without the
assumption that `A` is local).

Proof:
1. `B` is finite, hence algebraic, over `A`, and `L = B ⊗_A K` (the instance
   `IsLocalization (algebraMapSubmonoid B A⁰) L` from Mathlib's `Algebra.IsAlgebraic` section), so `L/K` is
   finite-dimensional and the image `M` of `B` in `L` is a lattice (finitely generated; every element of `L` is
   of the form `b/a`).
2. `φ :=` multiplication by `y : L → L` is `K`-linear, `det φ = Nm_{L/K}(y) ≠ 0` (`Algebra.norm_apply`,
   `Algebra.norm_ne_zero_iff`), and `φ(M) =` the image of `yB` `⊆ M`.
3. By `LatticeDetOrd`: `ord_A(det φ) = length_A(M/φM) = length_A(B/yB)` (`B → L` injective, `relLength_map`,
   `relLength_top`, `Submodule.Quotient.restrictScalarsEquiv`). Finiteness by `LatticeRelLength` (3).

Reference: Stacks 02MI and the last paragraph of the proof of 02MJ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

noncomputable section

open Submodule

namespace Ring

variable {A B K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
  [Module.Finite A B] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

variable (A B L) in
/-- `B → L` as an `A`-linear map. -/
def toFracLin : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap

lemma toFracLin_apply (b : B) : toFracLin A B L b = algebraMap B L b := rfl

lemma toFracLin_injective : Function.Injective (toFracLin A B L) :=
  IsFractionRing.injective B L

variable (A B K L) in
theorem isLattice_range : IsLattice K ((⊤ : Submodule A B).map (toFracLin A B L)) where
  fg := (Module.Finite.fg_top (R := A) (M := B)).map _
  span_eq_top := by
    rw [eq_top_iff]
    intro l _
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) l
    obtain ⟨a, ha, has⟩ := s.2
    have ha0 : algebraMap A K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero ha)
    have h1 : algebraMap B L (s : B) = algebraMap K L (algebraMap A K a) := by
      rw [← has, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have : l = (algebraMap A K a)⁻¹ • algebraMap B L b := by
      rw [← hs, h1, Algebra.smul_def, map_inv₀, mul_comm l, ← mul_assoc,
        inv_mul_cancel₀ ((map_ne_zero _).mpr ha0), one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, trivial, rfl⟩)

lemma map_mulLeft_range (y : B) :
    ((⊤ : Submodule A B).map (toFracLin A B L)).map
        ((LinearMap.mulLeft K (algebraMap B L y)).restrictScalars A) =
      ((Ideal.span {y} : Ideal B).restrictScalars A).map (toFracLin A B L) := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, -, rfl⟩, rfl⟩
    refine ⟨y * b, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self y), ?_⟩
    simp [toFracLin_apply]
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    exact ⟨algebraMap B L b, ⟨b, trivial, rfl⟩, by simp [toFracLin_apply, mul_comm]⟩

lemma relLength_range_eq (y : B) :
    relLength ((⊤ : Submodule A B).map (toFracLin A B L))
        (((⊤ : Submodule A B).map (toFracLin A B L)).map
          ((LinearMap.mulLeft K (algebraMap B L y)).restrictScalars A)) =
      Module.length A (B ⧸ Ideal.span {y}) := by
  rw [map_mulLeft_range, relLength_map _ toFracLin_injective, relLength_top]
  exact (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {y} : Ideal B)).length_eq

omit [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] in
variable (A) in
/-- `length_A(B/yB) < ∞`. -/
theorem length_quotient_span_singleton_ne_top {y : B} (hy : y ≠ 0) :
    Module.length A (B ⧸ Ideal.span {y}) ≠ ⊤ := by
  let K := FractionRing A
  let L := FractionRing B
  let _ : Algebra K L := FractionRing.liftAlgebra A L
  have h1 := isLattice_range A B K L
  have hbij : Function.Surjective (LinearMap.mulLeft K (algebraMap B L y)) := by
    have hy' : algebraMap B L y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hy
    intro l
    exact ⟨(algebraMap B L y)⁻¹ * l, by
      rw [LinearMap.mulLeft_apply, ← mul_assoc, mul_inv_cancel₀ hy', one_mul]⟩
  have h2 := IsLattice.map' (A := A) _ hbij ((⊤ : Submodule A B).map (toFracLin A B L))
  rw [← relLength_range_eq (K := K) (L := L) y]
  exact IsLattice.relLength_ne_top (K := K) _ _

/-- Stacks 02MI + the end of 02MJ: `ord_A(Nm y) = length_A(B/yB)`. -/
theorem ordFrac_norm_eq_exp_length {y : B} (hy : y ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L y)) =
      WithZero.exp ((Module.length A (B ⧸ Ideal.span {y})).toNat : ℤ) := by
  have : Module.Finite K L := Module.Finite.of_isLocalization A B (nonZeroDivisors A)
  have h1 := isLattice_range A B K L
  have hy' : algebraMap B L y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hy
  have hdet : LinearMap.det (LinearMap.mulLeft K (algebraMap B L y)) ≠ 0 := by
    have := (Algebra.norm_ne_zero_iff (R := K)).mpr hy'
    rwa [Algebra.norm_apply] at this
  have hle : ((⊤ : Submodule A B).map (toFracLin A B L)).map
      ((LinearMap.mulLeft K (algebraMap B L y)).restrictScalars A) ≤
      (⊤ : Submodule A B).map (toFracLin A B L) := by
    rw [map_mulLeft_range]; exact Submodule.map_mono le_top
  have key := ordFrac_det_eq_exp_relLength (A := A) (K := K) _ _ hdet hle
  rw [relLength_range_eq] at key
  rw [Algebra.norm_apply]
  exact key

end Ring

end
