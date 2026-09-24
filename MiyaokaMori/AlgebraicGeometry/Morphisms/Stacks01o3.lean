import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeComparison

/-! # Relative Proj commutes with base change

Stacks Project, Tag 01O3: for `g : S' → S`, `Proj_{S'}(g^*𝒜) ≅ S' ×_S Proj_S(𝒜)`, compatibly with
`O(d)`: pulling back `O_{Proj 𝒜}(d)` along `Proj(g^*𝒜) → Proj(𝒜)` gives `O_{Proj g^*𝒜}(d)` (the
map `θ` of Stacks 01O3). Used for the fibers of `P(O ⊕ L)` (Lemma 5.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.relativeProj_baseChange {S S' : AlgebraicGeometry.Scheme.{u}}
    (g : S' ⟶ S) (𝒜 : S.GradedQCAlgebra) :
    ∃ e : (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).left ≅
        CategoryTheory.Limits.pullback g (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom,
      e.hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
        (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).hom ∧
      ∀ d : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (e.hom ≫ CategoryTheory.Limits.pullback.snd _ _)).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 d) ≅
          AlgebraicGeometry.Scheme.relativeProj.twist (𝒜.pullback g) d) := by
  obtain ⟨r, hr, htw⟩ :=
    AlgebraicGeometry.Scheme.relativeProj_baseChange_comparison g 𝒜
  let e := hr.isoPullback
  refine ⟨e, hr.isoPullback_hom_fst, ?_⟩
  intro d
  obtain ⟨φ⟩ := htw d
  exact ⟨by simpa only [e, hr.isoPullback_hom_snd] using φ⟩

end
