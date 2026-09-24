import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierRestrictionSequence
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedSubschemeProperOver
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionLinear
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y6
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.Stacks08aa

/-! # Euler characteristic of the restriction to an effective Cartier divisor

Let `X` be proper over a field `k`, `D` an effective Cartier divisor with `ι : D → X`, and `M` a line
bundle on `X`. Then `χ(X, M) − χ(X, M ⊗ O_X(D)^∨) = χ(D, ι^*M)`.

Source: the first step of the proof of Stacks 0BEU (using `0 → O_X(−D) ⊗ M → M → ι_*ι^*M → 0`);
Hartshorne III Ex. 5.1.

Proof:
1. `D.exists_shortExact_restriction M` gives the short exact sequence
   `0 → M ⊗ O_X(D)^∨ → M → ι_*ι^*M → 0`.
2. All three terms are coherent: `X` proper over `k` ⇒ locally Noetherian; `M`, `M ⊗ O_X(D)^∨` are line
   bundles, hence coherent (Stacks 01XZ); `ι^*M` is a line bundle on `D`, `D` is locally Noetherian, `ι`
   is a closed immersion hence finite, so `ι_*ι^*M` is coherent (Stacks 01Y6).
3. `χ` is additive (Stacks 08AA): `χ(M) = χ(M ⊗ O(D)^∨) + χ(ι_*ι^*M)`.
4. A closed immersion does not change cohomology (the `k`-linear form
   `sheafEulerCharacteristic_closedImmersion` of Stacks 02UV): `χ(X, ι_*ι^*M) = χ(D, ι^*M)`. The
   `k`-structure of `D` is `ι ≫ (X → Spec k)`, so `ι` is a `k`-morphism (`⟨rfl⟩`).

Used in the proof of Stacks 0BEU. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

theorem EffectiveCartierDivisor.sheafEulerCharacteristic_sub_tensor_dual {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (D : AlgebraicGeometry.EffectiveCartierDivisor X)
    (M : X.Modules) [M.IsLineBundle] :
    letI : D.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨D.idealSheaf.subschemeι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) X M
        - AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.Scheme.Modules.tensor M (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle))
      = AlgebraicGeometry.sheafEulerCharacteristic (k := k) D.toScheme
          ((AlgebraicGeometry.Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M) := by
  let _ : D.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨D.idealSheaf.subschemeι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have _ : D.idealSheaf.subschemeι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsLocallyNoetherian D.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian D.idealSheaf.subschemeι
  obtain ⟨f, w, hS⟩ := D.exists_shortExact_restriction M
  have hc1 : (AlgebraicGeometry.Scheme.Modules.tensor M
      (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle)).IsCoherent :=
    AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree _
  have hc2 : M.IsCoherent := AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree _
  have hcD : ((AlgebraicGeometry.Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M).IsCoherent :=
    AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree _
  have hc3 : ((AlgebraicGeometry.Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)).IsCoherent :=
    AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite D.idealSheaf.subschemeι _
  have hadd := @AlgebraicGeometry.sheafEulerCharacteristic_additive k _ X _ hX _ hS hc1 hc2 hc3
  have hci := AlgebraicGeometry.sheafEulerCharacteristic_closedImmersion (K := k)
    D.idealSheaf.subschemeι ((AlgebraicGeometry.Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)
  change AlgebraicGeometry.sheafEulerCharacteristic (k := k) X M =
      AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.Scheme.Modules.tensor M (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle)) +
        AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          ((AlgebraicGeometry.Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)) at hadd
  rw [hci, hadd]
  ring

end AlgebraicGeometry

end
