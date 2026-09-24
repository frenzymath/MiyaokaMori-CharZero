import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.RegularScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverField
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00tt

/-! # Smooth schemes over a field are regular (Stacks 056S)

Stacks 056S: a scheme smooth over a field is regular.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 056S: a scheme smooth over a field is regular. -/
theorem AlgebraicGeometry.isRegular_of_smoothOver {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (h : IsSmoothOver k X) : AlgebraicGeometry.Scheme.IsRegular X := by
  let pX := X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let : AlgebraicGeometry.Smooth pX := h
  let : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian pX
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ :=
    AlgebraicGeometry.Smooth.exists_isStandardSmooth pX x
  have hUtop : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    have hy : y = pX x := Subsingleton.elim _ _
    rw [hy]
    exact e hx
  subst U
  let ek :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) :=
    (ek.toMulEquiv.isField (Field.toIsField k)).toField
  let : Algebra Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(X, V) :=
    (pX.appLE ⊤ V e).hom.toAlgebra
  let : Algebra.IsStandardSmooth
      Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(X, V) := hs.toAlgebra
  let : Algebra.Smooth
      Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(X, V) := inferInstance
  let q := hV.primeIdealOf ⟨x, hx⟩
  let : q.asIdeal.IsPrime := q.isPrime
  let hq : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
    Algebra.Smooth.isRegularLocalRing_localization
      (k := Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤))
      (S := Γ(X, V)) q.asIdeal
  let : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := hq
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) (X.presheaf.stalk x)).toRingEquiv

end
