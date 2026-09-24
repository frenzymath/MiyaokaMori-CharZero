import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.RegularLocalRing.RegularOfFinitePdResidueField
import MiyaokaMori.RingTheory.Stacks00oc_ProjectiveDimensionResidueField
import MiyaokaMori.RingTheory.RegularLocalRing.RegularLocalGlobalDimension

/-! # Stacks 00OC: Auslander–Buchsbaum–Serre

Stacks 00OC (Auslander–Buchsbaum–Serre): for a Noetherian local ring `(R, 𝔪, κ)` the following are equivalent:
`κ` has finite projective dimension; `R` has finite global dimension (there is `n` such that every `R`-module has
projective dimension `≤ n`); `R` is regular. In that case `pd κ = dim R` and every module has projective dimension
`≤ dim R` (global dimension `= dim R`).

Reference: Stacks 00OC (algebra-proposition-finite-gl-dim-regular), via 00O7, 065T, 00OA, 00OB.

## Route actually formalised

Not the Stacks route (00OA Koszul complex / 00OB Buchsbaum–Eisenbud), but Matsumura, *Commutative Ring Theory*,
Theorem 19.2 with Nagata's lemma; every step is formalised in the imported modules:

* (1) ⇒ (3): `IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField` (module
  `RegularOfFinitePdResidueField`; uses `PdChangeOfRingsQuotient`, `NagataRetraction`,
  `ProjectiveDimensionTools`, Stacks 00NQ, Stacks 00NU).
* (3) ⇒ (2): `IsRegularLocalRing.forall_hasProjectiveDimensionLE_of_ringKrullDim_eq` (module
  `RegularLocalGlobalDimension`: Auslander's theorem Stacks 065T / Weibel 4.1.2 extending `pd M ≤ dim R` from
  finite modules — `Stacks00o7GlobalDimension` — to all modules, via Baer's criterion in `Ext` form and injective
  dimension shifting).
* (2) ⇒ (1): specialise to `M = κ`.
* `pd κ = dim R`: `IsRegularLocalRing.projectiveDimension_residueField` (module
  `Stacks00oc_ProjectiveDimensionResidueField`, via the regular sequence generating `𝔪`, Stacks 00NQ).
* `∀ M, pd M ≤ dim R`: from (3) ⇒ (2) and Mathlib `projectiveDimension_le_iff`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem IsLocalRing.tfae_isRegularLocalRing_finite_globalDimension (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    [∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R (IsLocalRing.ResidueField R)) n,
      ∃ n : ℕ, ∀ M : ModuleCat.{u} R, CategoryTheory.HasProjectiveDimensionLE M n,
      IsRegularLocalRing R].TFAE ∧
    (IsRegularLocalRing R →
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) = ringKrullDim R ∧
      ∀ M : ModuleCat.{u} R, CategoryTheory.projectiveDimension M ≤ ringKrullDim R) := by
  have hdim : ∀ (_ : IsRegularLocalRing R), ∃ d : ℕ, ringKrullDim R = d := fun hR =>
    ⟨(IsLocalRing.maximalIdeal R).spanFinrank, hR.spanFinrank_maximalIdeal.symm⟩
  refine ⟨?_, fun hR => ?_⟩
  · tfae_have 1 → 3 := fun ⟨n, hn⟩ => IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField R n hn
    tfae_have 3 → 2 := fun hR => by
      obtain ⟨d, hd⟩ := hdim hR
      exact ⟨d, IsRegularLocalRing.forall_hasProjectiveDimensionLE_of_ringKrullDim_eq R hd⟩
    tfae_have 2 → 1 := fun ⟨n, hn⟩ => ⟨n, hn _⟩
    tfae_finish
  · obtain ⟨d, hd⟩ := hdim hR
    refine ⟨IsRegularLocalRing.projectiveDimension_residueField R, fun M => ?_⟩
    rw [hd]
    exact (projectiveDimension_le_iff M d).mpr
      (IsRegularLocalRing.forall_hasProjectiveDimensionLE_of_ringKrullDim_eq R hd M)

end
