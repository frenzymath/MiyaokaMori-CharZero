import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicSection
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicDenominatorIdeal
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicDenominatorIdealQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicDenominatorCokernelSupport

/-! # The ideal of denominators of a regular meromorphic section (Stacks 02P0)

Stacks 02P0: for a regular meromorphic section `s` of `L`, the ideal of denominators
`I(V) = {f | f s ∈ L(V)}` is a quasi-coherent ideal sheaf, `1 : I → O_X` and `s : I → L` are injective,
and their cokernels are supported on a closed nowhere-dense subset. Source: Stacks 02P0
(`divisors-lemma-regular-meromorphic-ideal-denominators`).

## Proof

The witnesses are the concrete objects of the three sibling modules:
* `I := denomIdeal s` (`RegularMeromorphicDenominatorIdeal`): the subsheaf
  `I(V) = {g ∈ O(V) | ∃ l ∈ L(V), den i • l = g • num i on every W ≤ V ⊓ U i}` of `O_X`, with
  `a := denomInclusion s` (the inclusion, mono) and `b := mulHom s` (`g ↦ g • s`, mono because `num i` is regular
  on stalks). Clause 8 is `den_smul_mulHom_app`, clause 9 is `exists_app_eq_of_den_smul`.
* `I` is quasi-coherent (`RegularMeromorphicDenominatorIdealQuasicoherent`): the localization
  criterion `isQuasicoherent_of_affine_localizing` on affine opens inside the charts `U i`.
* `T := badSet s = closure (Supp (coker a) ∪ Supp (coker b))` (`RegularMeromorphicDenominatorCokernelSupport`):
  closed, contains both supports, and has empty interior because on each chart the supports avoid the open dense
  set `D(den i) ∩ frameLocusOn (num i)` (`a_x` is onto where `den i` is a unit, `b_x` is onto where `num i` is a
  frame; `D(den i)` is dense since a nilpotent non-zero-divisor is impossible in a nontrivial stalk, and the
  frame locus of `num i` is dense for the same reason applied to its coordinate in a local frame).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 02P0: the ideal of denominators `I` together with `a = (1 : I → O_X)` and `b = (s : I → L)`. The
last two clauses characterize `I` and `b`: on an open `V ⊆ U_i`, `b(h) = a(h)·(num_i/den_i)` (written as
`den_i • b(h) = a(h) • num_i`), and if `g ∈ Γ(V, O)` satisfies `g·s ∈ L(V)` (i.e. there is `l` with
`den_i • l = g • num_i`) then `g ∈ a(I(V))`. -/

theorem AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection.exists_denominatorIdeal
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} [L.IsLineBundle]
    (s : AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L) :
    ∃ (I : X.Modules) (a : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (b : I ⟶ L) (T : Set X),
      I.IsQuasicoherent ∧ CategoryTheory.Mono a ∧ CategoryTheory.Mono b ∧
      IsClosed T ∧ interior T = ∅ ∧
      (CategoryTheory.Limits.cokernel a).support ⊆ T ∧ (CategoryTheory.Limits.cokernel b).support ⊆ T ∧
      (∀ (i : s.ι) (V : X.Opens) (hV : V ≤ s.U i) (h : Γ(I, V)),
        X.presheaf.map (CategoryTheory.homOfLE hV).op (s.den i) •
            AlgebraicGeometry.Scheme.Modules.Hom.app b V h =
          (show Γ(X, V) from AlgebraicGeometry.Scheme.Modules.Hom.app a V h) •
            L.presheaf.map (CategoryTheory.homOfLE hV).op (s.num i)) ∧
      (∀ (i : s.ι) (V : X.Opens) (hV : V ≤ s.U i) (g : Γ(X, V)),
        (∃ l : Γ(L, V), X.presheaf.map (CategoryTheory.homOfLE hV).op (s.den i) • l =
            g • L.presheaf.map (CategoryTheory.homOfLE hV).op (s.num i)) →
          ∃ h : Γ(I, V), (show Γ(X, V) from AlgebraicGeometry.Scheme.Modules.Hom.app a V h) = g) :=
  ⟨s.denomIdeal, s.denomInclusion, s.mulHom, s.badSet, s.denomIdeal_isQuasicoherent, inferInstance,
    inferInstance, s.isClosed_badSet, s.interior_badSet_eq_empty,
    s.support_cokernel_denomInclusion_subset_badSet, s.support_cokernel_mulHom_subset_badSet,
    fun i V hV h => s.den_smul_mulHom_app i hV h,
    fun i V hV g hg => s.exists_app_eq_of_den_smul i hV g hg⟩

end
