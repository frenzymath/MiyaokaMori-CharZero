import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicSectionCore

/-! # Existence of regular meromorphic sections (Stacks 02OZ)

Stacks 02OZ: an invertible sheaf has a regular meromorphic section if (1) `X` is integral, or (3) `X` is
locally Noetherian without embedded points. Source: Stacks 02OZ
(`divisors-lemma-regular-meromorphic-section-exists`); (3) is 0EMI
(`lemma-regular-meromorphic-section-exists-noetherian`).

**Proof.** Both cases are instances of the construction
`GenericData.nonempty_regularMeromorphicSection` (`RegularMeromorphicSectionCore`): choose a generator of the
free rank-one module `L_y` at each "generic point" `y`, express it in local frames as a fraction of
sections, glue the fractions with a Chinese-remainder argument, and check
regularity and compatibility stalkwise. The generic point data are:
* (3) `X` locally Noetherian without embedded points: the minimal points of `X`
  (every point specializes from one, finitely many in an affine,
  and sections of `O_X` over an affine with vanishing germs at all of them are zero — Stacks 0EMI/00LD);
* (1) `X` integral: the single generic point `η` (Stacks 01X5; `Γ(U, O_X) → O_{X,η}` is injective,
  Mathlib `germ_injective_of_isIntegral`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 02OZ(3) = 0EMI: on a locally Noetherian scheme without embedded points, an invertible sheaf has
a regular meromorphic section. -/

theorem AlgebraicGeometry.Scheme.Modules.nonempty_regularMeromorphicSection_of_noEmbeddedPoints
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X] (hX : X.HasNoEmbeddedPoints)
    (L : X.Modules) [L.IsLineBundle] :
    Nonempty (AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L) := by
  let D : AlgebraicGeometry.Scheme.Modules.GenericData X :=
    { G := {y | AlgebraicGeometry.Scheme.IsMinimalPoint y}
      minimal := fun y hy => hy
      spec := fun x => by
        obtain ⟨y, hy, hyx⟩ := AlgebraicGeometry.Scheme.Modules.exists_isMinimalPoint_specializes x
        exact ⟨y, hy, hyx⟩
      finite := fun U hU => AlgebraicGeometry.Scheme.Modules.finite_isMinimalPoint_inter hU
      sections_eq_zero := fun U hU _ _ f hf =>
        AlgebraicGeometry.Scheme.Modules.section_eq_zero_of_germ_isMinimalPoint_eq_zero hX hU f
          (fun y hy hmin => hf y hmin hy) }
  exact D.nonempty_regularMeromorphicSection L

/-- Stacks 02OZ(1): on an integral scheme, an invertible sheaf has a regular meromorphic section. -/

theorem AlgebraicGeometry.Scheme.Modules.nonempty_regularMeromorphicSection_of_isIntegral
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (L : X.Modules) [L.IsLineBundle] :
    Nonempty (AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L) := by
  let D : AlgebraicGeometry.Scheme.Modules.GenericData X :=
    { G := {genericPoint X}
      minimal := fun y hy z hzy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have hz : IsGenericPoint z Set.univ := Set.eq_univ_of_univ_subset
          ((genericPoint_spec X).def ▸ specializes_iff_closure_subset.mp hzy)
        exact hz.eq (genericPoint_spec X)
      spec := fun x => ⟨genericPoint X, rfl, genericPoint_specializes x⟩
      finite := fun U _ => (Set.finite_singleton _).subset Set.inter_subset_left
      sections_eq_zero := fun U _ x hx f hf => by
        have hη : genericPoint X ∈ U := (genericPoint_specializes x).mem_open U.2 hx
        apply AlgebraicGeometry.germ_injective_of_isIntegral X (genericPoint X) hη
        rw [hf (genericPoint X) rfl hη, map_zero] }
  exact D.nonempty_regularMeromorphicSection L

end
