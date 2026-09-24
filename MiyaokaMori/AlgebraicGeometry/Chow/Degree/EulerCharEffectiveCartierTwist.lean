import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierRestrictionSequence
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.EulerCharRestrictionEffectiveCartier
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.Stacks08aa

/-! # Euler characteristic of a twist by an effective Cartier divisor

Let `X` be a proper, integral, one-dimensional scheme over a field `k`, `D` an effective Cartier divisor
on `X`, and `deg_k D := deg [D]_0 = Σ_{x∈D} length(O_{D,x})·[κ(x):k]` (the `k`-degree of
`D.idealSheaf.cycle 0`). Then (a) `χ(X, O_X(D)) = χ(X, O_X) + deg_k D`; (b) for every line bundle `M`
and isomorphism `M' ≅ M ⊗ O_X(D)^∨`, `χ(X, M') = χ(X, M) − deg_k D`.

Proof:
1. (b): the restriction sequence of an effective Cartier divisor gives the short exact sequence
   `0 → M ⊗ O_X(D)^∨ → M → i_*i^*M → 0` (`i : D → X`).
2. All three terms are coherent (line bundles are locally free of finite type, Stacks 01XZ; for
   `i_*i^*M` see `EulerCharEffectiveCartierRestriction.lean`), `X` is proper over `k`, and `χ` is
   additive on short exact sequences (Stacks 08AA): `χ(M) = χ(M ⊗ O(D)^∨) + χ(X, i_*i^*M)`.
3. `χ(X, i_*i^*M) = deg_k D` (`EulerCharEffectiveCartierRestriction.lean`); `χ` is invariant under
   isomorphism (`sheafEulerCharacteristic_eq_of_iso`), hence `χ(M') = χ(M) − deg_k D`.
4. (a): take `M = O_X(D)`, `M' = O_X` in (b); the isomorphism `O_X ≅ O_X(D) ⊗ O_X(D)^∨` is the inverse
   of the contraction `LineBundle.contraction` (`X` proper and integral is a variety; Stacks 01CT)
   composed with `tensorIsoTensorObj`.

Source: Stacks 0AYY (varieties-lemma-degree-effective-Cartier-divisor) + 0AYT + 08AA + 02M0;
used in the Riemann–Roch argument for integral curves.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [IsIntegral X] [IsLocallyNoetherian X]

/-- (b) `χ(M ⊗ O(D)^∨) = χ(M) − deg_k D`. -/
theorem sheafEulerCharacteristic_of_iso_tensor_dual_effectiveCartier (hX : IsProperOver k X)
    (hdim : SchemeIsOneDimensional X) (D : EffectiveCartierDivisor X)
    (M M' : X.Modules) [M.IsLineBundle]
    (e : M' ≅ Scheme.Modules.tensor M (Scheme.Modules.dual D.lineBundle)) :
    sheafEulerCharacteristic (k := k) X M' =
      sheafEulerCharacteristic (k := k) X M - D.degreeOver k := by
  obtain ⟨f, w, hS⟩ := D.exists_shortExact_restriction M
  have hc1 : (Scheme.Modules.tensor M (Scheme.Modules.dual D.lineBundle)).IsCoherent :=
    Scheme.Modules.isCoherent_of_isLocallyFree _
  have hc2 : M.IsCoherent := Scheme.Modules.isCoherent_of_isLocallyFree _
  have hc3 := D.isCoherent_pushforward_pullback M
  have hadd := @sheafEulerCharacteristic_additive k _ X _ hX _ hS hc1 hc2 hc3
  have hD := D.sheafEulerCharacteristic_pushforward_pullback (k := k) hX hdim M
  have he := sheafEulerCharacteristic_eq_of_iso (k := k) e
  have hadd' : sheafEulerCharacteristic (k := k) X M =
      sheafEulerCharacteristic (k := k) X (Scheme.Modules.tensor M (Scheme.Modules.dual D.lineBundle)) +
        sheafEulerCharacteristic (k := k) X
          ((Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
            ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)) := hadd
  rw [hD] at hadd'
  rw [he, hadd']
  ring

/-- (a) χ(O(D)) = χ(O) + deg_k D -/
theorem sheafEulerCharacteristic_effectiveCartier_lineBundle (hX : IsProperOver k X)
    (hdim : SchemeIsOneDimensional X) (D : EffectiveCartierDivisor X) :
    sheafEulerCharacteristic (k := k) X D.lineBundle =
      sheafEulerCharacteristic (k := k) X (SheafOfModules.unit X.ringCatSheaf) + D.degreeOver k := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have : IsOfFiniteType (X ↘ Spec (CommRingCat.of k)) := {}
  let V : Variety k := { carrier := X }
  let LD : LineBundle V := LineBundle.ofModules (X := V) D.lineBundle
  have e : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅
      Scheme.Modules.tensor D.lineBundle (Scheme.Modules.dual D.lineBundle) :=
    LD.contraction.symm ≪≫
      (Scheme.Modules.tensorIsoTensorObj D.lineBundle (Scheme.Modules.dual D.lineBundle)).symm
  have h := sheafEulerCharacteristic_of_iso_tensor_dual_effectiveCartier hX hdim D D.lineBundle _ e
  linarith

end AlgebraicGeometry

end
