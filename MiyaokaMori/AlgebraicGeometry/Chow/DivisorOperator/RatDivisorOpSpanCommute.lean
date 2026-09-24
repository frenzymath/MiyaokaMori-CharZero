import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Chow.CapCommutes

/-! # Operators in the ℚ-span of line bundle operators commute

The operators in the ℚ-span of the operators of line bundles commute pairwise (the ℚ-linear extension of
Fulton, Intersection Theory, Cor. 2.4.2 / Stacks 02TJ). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `ratExtend` commutes with composition (needed for the generator case below). -/
theorem AddMonoidHom.ratExtend_comp {M N P : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (f : N →+ P) (g : M →+ N) :
    (f.comp g).ratExtend = f.ratExtend.comp g.ratExtend := by
  unfold AddMonoidHom.ratExtend
  rw [← LinearMap.baseChange_comp]
  rfl

/-- Operators in the ℚ-span of line bundle operators commute pairwise (Fulton Cor. 2.4.2 / Stacks 02TJ,
extended ℚ-linearly).

Proof: `Submodule.span_induction` on `D` and on `E`. Generator case: `D = c_1(L)`, `E = c_1(L')`,
`ratDivisorOpOfLineBundle L d = (firstChernClass L (d+1)).ratExtend`; `ratExtend` commutes with composition
(`AddMonoidHom.ratExtend_comp`), which reduces to `AlgebraicGeometry.firstChernClass_comm L L' d`. Zero,
addition and scalar multiplication: `LinearMap.comp` is linear in both variables (`LinearMap.comp_add`,
`add_comp`, `comp_smul`, `smul_comp`); addition and scalar multiplication of `RatDivisorOp` are
componentwise (`Pi`). -/
theorem AlgebraicGeometry.RatDivisorOp.comp_comm_of_mem_span {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (D E : AlgebraicGeometry.RatDivisorOp X)
    (hD : D ∈ Submodule.span ℚ {D' : AlgebraicGeometry.RatDivisorOp X |
        ∃ (L : X.Modules) (_ : L.IsLineBundle), D' = AlgebraicGeometry.ratDivisorOpOfLineBundle L})
    (hE : E ∈ Submodule.span ℚ {D' : AlgebraicGeometry.RatDivisorOp X |
        ∃ (L : X.Modules) (_ : L.IsLineBundle), D' = AlgebraicGeometry.ratDivisorOpOfLineBundle L})
    (d : ℕ) :
    (D d).comp (E (d + 1)) = (E d).comp (D (d + 1)) := by
  set S : Set (AlgebraicGeometry.RatDivisorOp X) := {D' : AlgebraicGeometry.RatDivisorOp X |
    ∃ (L : X.Modules) (_ : L.IsLineBundle), D' = AlgebraicGeometry.ratDivisorOpOfLineBundle L}
    with hS
  -- generator case: the `c_1` of two line bundles; reduce to `firstChernClass_comm` via `ratExtend_comp`
  have hgen : ∀ D' ∈ S, ∀ E' ∈ S, ∀ d : ℕ,
      (D' d).comp (E' (d + 1)) = (E' d).comp (D' (d + 1)) := by
    rintro D' ⟨L, hL, rfl⟩ E' ⟨L', hL', rfl⟩ d
    -- both sides are by definition composites of `ratExtend`; the intermediate Chow group
    -- `ChowGroup X (d + 1 + 1 - 1)` is only defeq to `ChowGroup X (d + 1)`, so `rw` fails and a
    -- term-mode `Eq.trans` chain is used
    exact (AddMonoidHom.ratExtend_comp (AlgebraicGeometry.firstChernClass L (d + 1))
        (AlgebraicGeometry.firstChernClass L' (d + 2))).symm.trans
      ((congrArg AddMonoidHom.ratExtend (AlgebraicGeometry.firstChernClass_comm (k := k) L L' d)).trans
        (AddMonoidHom.ratExtend_comp (AlgebraicGeometry.firstChernClass L' (d + 1))
          (AlgebraicGeometry.firstChernClass L (d + 2))))
  -- first the span induction on `E` (with `D'` a fixed generator)
  have hE' : ∀ D' ∈ S, ∀ E' : AlgebraicGeometry.RatDivisorOp X, E' ∈ Submodule.span ℚ S →
      ∀ d : ℕ, (D' d).comp (E' (d + 1)) = (E' d).comp (D' (d + 1)) := by
    intro D' hD' E' hE'
    induction hE' using Submodule.span_induction with
    | mem x hx => exact hgen D' hD' x hx
    | zero => intro d; simp
    | add x y _ _ hx hy =>
      intro d
      simp only [Pi.add_apply, LinearMap.comp_add, LinearMap.add_comp, hx d, hy d]
    | smul c x _ hx =>
      intro d
      simp only [Pi.smul_apply, LinearMap.comp_smul, LinearMap.smul_comp, hx d]
  -- then the span induction on `D`
  induction hD using Submodule.span_induction with
  | mem x hx => exact hE' x hx E hE d
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, LinearMap.comp_add, LinearMap.add_comp, hx, hy]
  | smul c x _ hx =>
    simp only [Pi.smul_apply, LinearMap.comp_smul, LinearMap.smul_comp, hx]

end
