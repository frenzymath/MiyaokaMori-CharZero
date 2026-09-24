import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Basis
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient

/-! # The monomials `𝔪^n = (pieceIso n ≫ frameHom n)(μ^{⊗n})` of a frame on the total space
(auxiliary to , Lemma 3.1 of the paper)

For a frame `μ` of `L^{-1}` on `U ⊆ C̃`, `μ^{⊗n} = framePow μ n ∈ Γ(U, L^{-n})` and
`𝔪^n := frameHom n (pieceIso μ^{⊗n}) ∈ Γ(Tot(L), p⁻¹U)` is the `n`-th power of the tautological linear
function `𝔪 = 𝔪^1` of `μ` on the total space. The family `n ↦ 𝔪^n` is multiplicative
(`frameMonomial_add`: `frameHom_pieceMul` + `pieceMul_app_framePow`) and unital (`frameMonomial_zero`:
`pieceIso_zero_comp_frameHom_zero`), so it is the "monomial family" fed to `GradedAlgebra.monomialHom`.
We also record that the `𝒪(U)`-action on `Γ(Tot(L), p⁻¹U) = (p_*𝒪_Tot)(U)` is multiplication by `p^♯`
(`pushforward_unit_smul_eq`, definitional).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace jetNeighborhood

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k} {ρ : FiniteCover k C}
  (L : LineBundle ρ.source.toVariety) (U : ρ.source.toScheme.Opens) (μ : Γ((L.zpow (-1)).toModules, U))

/-- `𝔪^n := (pieceIso n ≫ frameHom n)(μ^{⊗n}) ∈ Γ(Tot(L), p⁻¹U)`. -/
def frameMonomial (n : ℕ) :
    Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U) :=
  (((truncatedJetAlgebra.pieceIso L n).hom ≫ BasedJet.frameHom L n).val.app (Opposite.op U)).hom
    (truncatedJetAlgebra.framePow L U μ n)

/-- `𝔪^0 = 1` (`pieceIso_zero_comp_frameHom_zero`: on the weight-`0` piece, `c ↦ c·ξ^0` is `p^♯`). -/
theorem frameMonomial_zero : frameMonomial L U μ 0 = 1 := by
  have h := congrArg (fun g : truncatedJetAlgebra.piece L 0 ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) =>
      (g.val.app (Opposite.op U)).hom (truncatedJetAlgebra.framePow L U μ 0))
    (BasedJet.pieceIso_zero_comp_frameHom_zero L)
  refine h.trans ?_
  exact map_one ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app U).hom

/-- `𝔪^{a+b} = 𝔪^a · 𝔪^b` (`frameHom_pieceMul` and `pieceMul_app_framePow`). -/
theorem frameMonomial_add (a b : ℕ) :
    frameMonomial L U μ (a + b) = frameMonomial L U μ a * frameMonomial L U μ b := by
  unfold frameMonomial
  rw [← truncatedJetAlgebra.pieceMul_app_framePow L U μ a b]
  exact BasedJet.frameHom_pieceMul L a b U _ _

/-- The `𝒪(U)`-action on `(p_*𝒪_{Tot})(U) = Γ(Tot(L), p⁻¹U)` is multiplication by `p^♯ a` (definitional). -/
theorem pushforward_unit_smul_eq (a : Γ(ρ.source.toScheme, U))
    (g : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U)) :
    (show Γ((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf), U) from
      a • (show Γ((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf), U) from g)) =
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app U).hom a * g := rfl

end jetNeighborhood

end
