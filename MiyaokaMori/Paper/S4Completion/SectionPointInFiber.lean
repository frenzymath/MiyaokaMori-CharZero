import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve

/-! # The section meets some fibre component

For a section `σ` of `π : S → C`, the point `σ(y)` lies in the fibre over `y`; if the fibre is covered by
finitely many integral curves `Γᵢ`, then `σ(y)` lies on one of them. This is the starting point of the
chain argument in the proof of Lemma 5.1 of the paper (§5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- If the fibre `π⁻¹(y)` is the union of the curves `Γ i`, the point `σ(y)` of a section `σ` lies on
some `Γ i`. -/
theorem section_mem_fiber_component {k : Type u} [Field k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) (σ : C.toScheme ⟶ S.toScheme)
    (hσ : σ ≫ π = 𝟙 C.toScheme) (y : C.toScheme)
    {ι : Type} [Fintype ι] {Γ : ι → IntegralCurve k S.toScheme}
    (hcov : (⋃ i, Set.range (Γ i).ι.base) = π.base ⁻¹' {y}) :
    ∃ i, σ.base y ∈ Set.range (Γ i).ι.base := by
  have hy : π.base (σ.base y) = y := by
    have hh := congrArg (fun f : C.toScheme ⟶ C.toScheme => f.base y) hσ
    change π.base (σ.base y) = y at hh
    exact hh
  have hmem : σ.base y ∈ π.base ⁻¹' {y} := by
    exact hy
  rw [← hcov] at hmem
  exact Set.mem_iUnion.mp hmem

end
