import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.ChowRatExtend
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.SeedCycleGeometry
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreePushforward

/-! # The rational degree of zero-cycles is invariant under proper pushforward

The degree of zero-dimensional ℚ-Chow classes is compatible with the pushforward along a proper
`K`-morphism: `deg_Y(f_*α) = deg_X(α)` (the degree is defined as in 0AZ1 by pushing forward to `Spec K`,
then functoriality of the pushforward, 02R5).

Source: Stacks 0AZ1 (lemma-degree-pushforward-zero-cycle), 02R5 (functoriality of the pushforward).

Proof (the descent condition `PushforwardDescends f 0` comes from Stacks 02S2, since `chowPushforward`
is `0` by definition when it fails):
1. reduce ℚ-coefficients to ℤ-coefficients: both sides are `baseChange ℚ` followed by `rid`; use
   `degree_tmul` on pure tensors `q ⊗ c`;
2. with ℤ-coefficients, take a representative `Z ∈ Z_0(X)` in the quotient: `chowPushforward_mk` reduces
   the pushforward to cycles;
3. at the level of cycles, `deg_Y(f_*Z) = deg_X(Z)`: `rawZeroCycleDegree` is an abbrev of
   `AlgebraicCycle.degree` (equal by definition); use
   `AlgebraicGeometry.Intersection.rawZeroCycleDegree_properPushforward` (regrouping by fibers + the
   multiplicativity `[κ(x):κ(y)][κ(y):K] = [κ(x):K]`), then `f ≫ p_Y = p_X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.ChowDegreeRatPushforward

open AlgebraicGeometry

/-- A `K`-morphism between proper `K`-schemes satisfies `FiniteDimensionPreservingResidues` (finite type ⇒
the transcendence degree of the residue field equals the dimension of the closure). -/
theorem finiteDimensionPreservingResidues_of_isProperOver {K : Type u} [Field K]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (hY : IsProperOver K Y) (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of K))] :
    AlgebraicGeometry.Intersection.FiniteDimensionPreservingResidues f := by
  letI : IsProper (X ↘ Spec (CommRingCat.of K)) := hX
  letI : IsProper (Y ↘ Spec (CommRingCat.of K)) := hY
  let X' : AlgebraicGeometry.Proj.SchemeOver K :=
    { scheme := X
      toBase := X ↘ Spec (CommRingCat.of K) }
  let Y' : AlgebraicGeometry.Proj.SchemeOver K :=
    { scheme := Y
      toBase := Y ↘ Spec (CommRingCat.of K) }
  have hf : f ≫ Y'.toBase = X'.toBase := (inferInstance : f.IsOver (Spec (CommRingCat.of K))).1
  haveI : LocallyOfFiniteType X'.toBase := inferInstanceAs (LocallyOfFiniteType (X ↘ _))
  haveI : QuasiCompact X'.toBase := inferInstanceAs (QuasiCompact (X ↘ _))
  haveI : LocallyOfFiniteType Y'.toBase := inferInstanceAs (LocallyOfFiniteType (Y ↘ _))
  haveI : QuasiCompact Y'.toBase := inferInstanceAs (QuasiCompact (Y ↘ _))
  exact AlgebraicGeometry.Intersection.finiteDimensionPreservingResidues_of_finiteType_over_field
    (X := X') (Y := Y') f hf

/-- At the level of cycles: the pushforward along a proper `K`-morphism preserves the degree of
zero-cycles. -/
theorem degree_properPushforward {K : Type u} [Field K]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (hY : IsProperOver K Y) (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of K))] [IsProper f]
    (Z : ↥(cycleSubgroup X 0))
    (hZ' : AlgebraicGeometry.AlgebraicCycle.properPushforward f (Z : AlgebraicCycle X ℤ) ∈ cycleSubgroup Y 0) :
    AlgebraicCycle.degree (k := K) (AlgebraicGeometry.AlgebraicCycle.properPushforward f (Z : AlgebraicCycle X ℤ)) =
      AlgebraicCycle.degree (k := K) (Z : AlgebraicCycle X ℤ) := by
  letI : IsProper (Y ↘ Spec (CommRingCat.of K)) := hY
  -- `rawZeroCycleDegree` is an abbrev of `AlgebraicCycle.degree`: both sides are equal by definition
  have h1 : AlgebraicCycle.degree (k := K) (AlgebraicCycle.properPushforward f (Z : AlgebraicCycle X ℤ)) =
      AlgebraicGeometry.Intersection.rawZeroCycleDegree (Y ↘ Spec (CommRingCat.of K)) ⟨_, hZ'⟩ := rfl
  have h2 : AlgebraicCycle.degree (k := K) (Z : AlgebraicCycle X ℤ) =
      AlgebraicGeometry.Intersection.rawZeroCycleDegree (X ↘ Spec (CommRingCat.of K)) Z := rfl
  have hdim : (⟨_, hZ'⟩ : ↥(cycleSubgroup Y 0)) =
      AlgebraicGeometry.Intersection.dimensionProperPushforward f 0 Z :=
    Subtype.ext rfl
  have hover : f ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K) :=
    (inferInstance : f.IsOver (Spec (CommRingCat.of K))).1
  refine h1.trans ?_
  rw [hdim, AlgebraicGeometry.Intersection.rawZeroCycleDegree_properPushforward
    (Y ↘ Spec (CommRingCat.of K)) f, h2]
  congr 1

/-- ℤ-coefficients: `deg_Y(f_* c) = deg_X(c)` for `c ∈ A_0(X)`. -/
theorem degreeOver_chowPushforward {K : Type u} [Field K]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (hY : IsProperOver K Y) (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of K))] [IsProper f] (c : ChowGroup X 0) :
    ChowGroup.degreeOver K Y hY (chowPushforward f 0 c) = ChowGroup.degreeOver K X hX c := by
  letI : IsProper (X ↘ Spec (CommRingCat.of K)) := hX
  letI : IsProper (Y ↘ Spec (CommRingCat.of K)) := hY
  have hdesc : PushforwardDescends f 0 :=
    AlgebraicCycle.properPushforward_rationallyEquivalent (k := K) f 0
  obtain ⟨Z, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  change ChowGroup.degreeOver K Y hY (chowPushforward f 0 (ChowGroup.mk Z)) =
    ChowGroup.degreeOver K X hX (ChowGroup.mk Z)
  rw [chowPushforward_mk f 0 hdesc]
  exact degree_properPushforward hX hY f Z (cyclePushforwardHom f 0 hdesc Z).2

end MiyaokaMori.ChowDegreeRatPushforward

theorem AlgebraicGeometry.ChowGroupRat.degree_chowPushforwardRat {K : Type u} [Field K]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (hY : IsProperOver K Y) (f : X ⟶ Y)
    [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.IsProper f]
    (α : AlgebraicGeometry.ChowGroupRat X 0) :
    AlgebraicGeometry.ChowGroupRat.degree Y hY (AlgebraicGeometry.chowPushforwardRat f 0 α)
      = AlgebraicGeometry.ChowGroupRat.degree X hX α := by
  revert α
  show ∀ α : TensorProduct ℤ ℚ (AlgebraicGeometry.ChowGroup X 0), _
  intro α
  induction α using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul q c =>
    change AlgebraicGeometry.ChowGroupRat.degree Y hY
      (q ⊗ₜ[ℤ] (AlgebraicGeometry.chowPushforward f 0 c)) = _
    rw [AlgebraicGeometry.ChowGroupRat.degree_tmul, AlgebraicGeometry.ChowGroupRat.degree_tmul,
      MiyaokaMori.ChowDegreeRatPushforward.degreeOver_chowPushforward hX hY f c]
  | add a b ha hb =>
    have e1 := LinearMap.map_add (AlgebraicGeometry.ChowGroupRat.degree Y hY ∘ₗ
      AlgebraicGeometry.chowPushforwardRat f 0) a b
    have e2 := LinearMap.map_add (AlgebraicGeometry.ChowGroupRat.degree X hX) a b
    simp only [LinearMap.comp_apply] at e1
    exact e1.trans ((congrArg₂ (· + ·) ha hb).trans e2.symm)

end
