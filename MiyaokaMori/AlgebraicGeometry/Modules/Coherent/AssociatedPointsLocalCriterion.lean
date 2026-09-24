import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModulesAssociatedPoints
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.FromSpecStalkAssociatedPointsBridge
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.RingTheory.Localization.Stacks02m6

/-! # Local criterion for associated points

Associated points of a coherent sheaf `F` on a locally Noetherian scheme are local (Stacks 05AI, 02OI):

* `isAssociatedPoint_fromSpecStalk_iff`: for
  `x : X` and a prime `𝔭` of `O_{X,x}`, the generization `y = fromSpecStalk x 𝔭` of `x` is an associated point
  of `F` iff `𝔭 ∈ Ass_{O_{X,x}} F_x`. It is the coherent special case of the quasi-coherent statement
  `isAssociatedPoint_fromSpecStalk_iff_of_isQuasicoherent` (`FromSpecStalkAssociatedPointsBridge`),
  whose proof is affine-local: over an affine
  open `W ∋ x` with `A = Γ(X, W)` Noetherian, both `O_{X,x}` and `O_{X,y}` are localizations of `A` and both
  stalks are localizations of `Γ(F, W)` (Stacks 01I8), so by Stacks 0310 (3)
  (`preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule`) both sides are equivalent to
  `p_y ∈ Ass_A Γ(F, W)`, where `p_y = 𝔭 ∩ A = 𝔪_y ∩ A` is the prime of `y`.
* `hasNoEmbeddedAssociatedPoints_iff_forall_stalk`: `F` has no embedded associated points iff for every
  `x`, the `O_{X,x}`-module `F_x` has no embedded primes (`Module.HasNoEmbeddedPrimes`, Stacks 02M5).

Proof of the criterion from the dictionary: `range (fromSpecStalk x) = {y | y ⤳ x}` (Mathlib
`range_fromSpecStalk`), `fromSpecStalk x` is a preimmersion, hence an embedding, so it is injective and
`fromSpecStalk 𝔭 ⤳ fromSpecStalk 𝔮 ↔ 𝔭 ⤳ 𝔮 ↔ 𝔭 ≤ 𝔮` (`IsInducing.specializes_iff`,
`PrimeSpectrum.le_iff_specializes`).
(⇒) If `𝔭 ≤ 𝔮` in `Ass(F_x)`, the points `y_𝔭 ⤳ y_𝔮` are associated points, so `y_𝔭 = y_𝔮`, so `𝔭 = 𝔮`.
(⇐) If `y ⤳ y'` are associated points, put `x := y'`, `y = fromSpecStalk x 𝔭` with `𝔭 ∈ Ass(F_x)`, and
`x = fromSpecStalk x 𝔪` (`fromSpecStalk_closedPoint`) with `𝔪 ∈ Ass(F_x)`; `𝔭 ≤ 𝔪` (maximal ideal), so
`𝔭 = 𝔪` and `y = x`.

Edge cases: `F = 0` — both sides hold vacuously (`Ass 0 = ∅`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **Associated points are local** (Stacks 05AI, 02OI): for a coherent `F` on a locally Noetherian `X`, a
prime `𝔭` of `O_{X,x}` and the corresponding generization `y = fromSpecStalk x 𝔭` of `x`,
`y` is an associated point of `F` iff `𝔭 ∈ Ass_{O_{X,x}} F_x`.

Proof: coherent ⇒ quasi-coherent, then `isAssociatedPoint_fromSpecStalk_iff_of_isQuasicoherent`
(affine-local, see the module docstring). -/
theorem isAssociatedPoint_fromSpecStalk_iff [AlgebraicGeometry.IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (x : X) (𝔭 : AlgebraicGeometry.Spec (X.presheaf.stalk x)) :
    F.IsAssociatedPoint ((X.fromSpecStalk x).base 𝔭) ↔
      𝔭.asIdeal ∈ associatedPrimes (X.presheaf.stalk x) (F.stalk x) := by
  have : F.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  exact F.isAssociatedPoint_fromSpecStalk_iff_of_isQuasicoherent 𝔭

/-- **Local criterion for "no embedded associated points"**: for a coherent `F` on a locally Noetherian `X`,
`F` has no embedded associated points iff every stalk `F_x` has no embedded primes over `O_{X,x}`. -/
theorem hasNoEmbeddedAssociatedPoints_iff_forall_stalk [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] :
    F.HasNoEmbeddedAssociatedPoints ↔
      ∀ x : X, Module.HasNoEmbeddedPrimes (X.presheaf.stalk x) (F.stalk x) := by
  constructor
  · intro h x p hp q hq hpq
    let 𝔭 : AlgebraicGeometry.Spec (X.presheaf.stalk x) := ⟨p, hp.isPrime⟩
    let 𝔮 : AlgebraicGeometry.Spec (X.presheaf.stalk x) := ⟨q, hq.isPrime⟩
    have h𝔭 : F.IsAssociatedPoint ((X.fromSpecStalk x).base 𝔭) :=
      (isAssociatedPoint_fromSpecStalk_iff F x 𝔭).mpr hp
    have h𝔮 : F.IsAssociatedPoint ((X.fromSpecStalk x).base 𝔮) :=
      (isAssociatedPoint_fromSpecStalk_iff F x 𝔮).mpr hq
    have hspec : 𝔭 ⤳ 𝔮 := (PrimeSpectrum.le_iff_specializes 𝔭 𝔮).mp hpq
    have heq := h _ _ h𝔭 h𝔮 (hspec.map (X.fromSpecStalk x).base.hom.continuous)
    have hinj : Function.Injective (X.fromSpecStalk x).base :=
      (X.fromSpecStalk x).isEmbedding.injective
    have : 𝔭 = 𝔮 := hinj heq
    exact congrArg PrimeSpectrum.asIdeal this
  · intro h y x hy hx hyx
    have hmem : y ∈ Set.range (X.fromSpecStalk x).base := by
      rw [AlgebraicGeometry.Scheme.range_fromSpecStalk]
      exact hyx
    obtain ⟨𝔭, rfl⟩ := hmem
    have hx' : x = (X.fromSpecStalk x).base (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
      (AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint (X := X) (x := x)).symm
    rw [hx'] at hx
    have hp := (isAssociatedPoint_fromSpecStalk_iff F x 𝔭).mp hy
    have hm := (isAssociatedPoint_fromSpecStalk_iff F x _).mp hx
    have hle : 𝔭.asIdeal ≤ (IsLocalRing.closedPoint (X.presheaf.stalk x)).asIdeal :=
      IsLocalRing.le_maximalIdeal 𝔭.isPrime.ne_top
    have heq : 𝔭.asIdeal = (IsLocalRing.closedPoint (X.presheaf.stalk x)).asIdeal :=
      h x _ hp _ hm hle
    conv_rhs => rw [hx']
    congr 1
    exact PrimeSpectrum.ext heq

end AlgebraicGeometry.Scheme.Modules

end
