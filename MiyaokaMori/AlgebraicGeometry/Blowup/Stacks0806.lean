import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupExceptionalInvertible
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupExistsLift
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupLiftUnique
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.ProjQuotientGivesLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01o4
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks0ag8

/-! # Stacks 0806: the universal property of the blowup

The blowup `b : X' → X` of `X` along an ideal sheaf `I` with support `Z` makes `b⁻¹Z` an effective
Cartier divisor, and it is terminal among such `X`-schemes: every `f : Y → X` for which `f⁻¹Z` is an
effective Cartier divisor factors uniquely through `b`. This is the common input of Stacks 0807,
080E and 0AHI.

The theorem is assembled from one lemma per assertion:
* `blowup_exceptional_isInvertibleIdeal` (Stacks 02OS (2)): the exceptional ideal is invertible;
* `blowup_exists_lift`: existence of the lift, via `relativeProj.lift`;
* `blowup_lift_unique`: uniqueness of the lift, from Stacks 01RH (`ext_of_ker_ι_eq_bot`),
  `relativeProj_isSeparated`, Stacks 07ZU (`IsInvertibleIdeal.ker_ι_support_compl_eq_bot`) and
  Stacks 02OS (1) (`blowup_isIso_morphismRestrict_support_compl`).

Since `EffectiveCartierDivisor Y = Y.EffCartier`, whose second field is `IsInvertibleIdeal`, the
condition "`∃ D, D.idealSheaf = J`" is literally `IsInvertibleIdeal J` (cf. `blowup_isBlowup`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 0806 (universal property of the blowup).** The exceptional ideal of `blowup I` is the
ideal sheaf of an effective Cartier divisor, and every `f : Y ⟶ X` for which `f⁻¹I` is the ideal
sheaf of an effective Cartier divisor factors uniquely through `(blowup I).hom`. -/
theorem AlgebraicGeometry.Scheme.blowup_universalProperty {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) :
    (∃ D : AlgebraicGeometry.EffectiveCartierDivisor (AlgebraicGeometry.Scheme.blowup I).left,
        D.idealSheaf = I.comap (AlgebraicGeometry.Scheme.blowup I).hom) ∧
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X),
      (∃ D : AlgebraicGeometry.EffectiveCartierDivisor Y, D.idealSheaf = I.comap f) →
      ∃! g : Y ⟶ (AlgebraicGeometry.Scheme.blowup I).left, g ≫ (AlgebraicGeometry.Scheme.blowup I).hom = f := by
  refine ⟨⟨⟨I.comap (AlgebraicGeometry.Scheme.blowup I).hom,
    AlgebraicGeometry.Scheme.blowup_exceptional_isInvertibleIdeal I⟩, rfl⟩, ?_⟩
  intro Y f hf
  obtain ⟨D, hD⟩ := hf
  have hf' : MiyaokaMori.Statement.IsInvertibleIdeal (I.comap f) := by
    rw [← hD]
    exact D.isInvertible
  obtain ⟨g, hg⟩ := AlgebraicGeometry.Scheme.blowup_exists_lift I f hf'
  exact ⟨g, hg, fun g' hg' => AlgebraicGeometry.Scheme.blowup_lift_unique I f hf' hg' hg⟩

end
