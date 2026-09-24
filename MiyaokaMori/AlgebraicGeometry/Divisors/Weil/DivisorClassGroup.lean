import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.Divisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.LinearEquivalence
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisorAdditive
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.SchemePrincipalWeilDivisor

/-! # The divisor class group

The divisor class group `Cl(X) = Div(X) / (principal divisors)`, the quotient of the Weil divisors by linear
equivalence.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- "Regular in codimension one" from Hartshorne's condition (*) in II §6: at every point of codimension one
(local ring of Krull dimension `1`) the local ring is regular (hence a DVR). A `Prop`-valued class, with
instances provided e.g. by smooth varieties. -/
class AlgebraicGeometry.Scheme.IsRegularInCodimOne (X : AlgebraicGeometry.Scheme.{u}) : Prop where
  regular_of_ringKrullDim_eq_one : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
    IsRegularLocalRing (X.presheaf.stalk x)

/-- `Cl(X) = Div(X) / (principal divisors)` under Hartshorne's condition (*): Noetherian (locally Noetherian
and quasi-compact), integral, separated, regular in codimension one. -/
noncomputable def AlgebraicGeometry.Scheme.ClassGroup (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X]
    [X.IsSeparated] [X.IsRegularInCodimOne] : Type u :=
  X.WeilDivisor ⧸ Subgroup.toAddSubgroup' X.principalDivisorHom.range

noncomputable instance (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [CompactSpace X] [X.IsSeparated] [X.IsRegularInCodimOne] : AddCommGroup X.ClassGroup :=
  inferInstanceAs (AddCommGroup (X.WeilDivisor ⧸ _))

/-- Two Weil divisors have the same class iff they are linearly equivalent. -/
theorem AlgebraicGeometry.Scheme.ClassGroup.mk_eq_mk_iff (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X]
    [X.IsSeparated] [X.IsRegularInCodimOne] (D D' : X.WeilDivisor) :
    (QuotientAddGroup.mk D : X.ClassGroup) = QuotientAddGroup.mk D' ↔ X.LinearlyEquivalent D D' := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · intro h
    have hm : Multiplicative.ofAdd (D - D') ∈ X.principalDivisorHom.range :=
      (Subgroup.mem_toAddSubgroup' X.principalDivisorHom.range (D - D')).mp h
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hm
    refine ⟨(v : X.functionField), v.ne_zero, ?_⟩
    have hv' := congrArg Multiplicative.toAdd hv
    exact hv'.symm
  · rintro ⟨f, hf, hfd⟩
    have hm : Multiplicative.ofAdd (D - D') ∈ X.principalDivisorHom.range := by
      apply MonoidHom.mem_range.mpr
      refine ⟨Units.mk0 f hf, ?_⟩
      exact congrArg Multiplicative.ofAdd hfd.symm
    exact (Subgroup.mem_toAddSubgroup' X.principalDivisorHom.range (D - D')).mpr hm

end
