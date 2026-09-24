import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFreeSheafFree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivNaturality
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection

/-! # The tautological section of `Tot(L)`

The tautological section `ξ` of `p_L^*L` on `Tot(L)` (the fibre coordinate) and the fact that it restricts to
zero along the zero section (§4 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

/-- The tautological section `ξ ∈ Γ(Tot(L), p_L^*L)`, corresponding to the identity of `Tot(L)` under
`totalSpaceHomEquiv`; it assigns to a point `(y, v)` the vector `v` itself. -/
noncomputable def tautologicalSection {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        L.toModules).val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.totalSpaceHomEquiv L.toModules
    (AlgebraicGeometry.Scheme.totalSpace L.toModules) (CategoryTheory.CategoryStruct.id _)

/-- The tautological section restricts to `0` along the zero section. -/
theorem tautologicalSection_zeroSection {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) :
    sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection L.toModules)
      (tautologicalSection L) = 0 := by
  -- Naturality of `totalSpaceHomEquiv` (with `j = σ₀`, `m = 𝟙`) identifies `σ₀^*ξ`, via `pullbackComp`, with the
  -- section corresponding to `σ₀ ≫ 𝟙`; the latter factors through the zero section, hence corresponds to `0`;
  -- `pullbackComp` is an isomorphism, hence injective.
  let σ := AlgebraicGeometry.Scheme.zeroSection L.toModules
  let T := AlgebraicGeometry.Scheme.totalSpace L.toModules
  have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality L.toModules T σ (𝟙 T)
  have hz := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_eq_zero_of_factors_zeroSection L.toModules
    (CategoryTheory.Over.mk (σ ≫ T.hom))
    ((CategoryTheory.Over.homMk σ rfl : CategoryTheory.Over.mk (σ ≫ T.hom) ⟶ T) ≫ 𝟙 T)
    (by
      change σ ≫ 𝟙 _ = (σ ≫ T.hom) ≫ σ
      rw [AlgebraicGeometry.Scheme.zeroSection_comp, Category.comp_id, Category.id_comp])
  rw [hz] at hn
  have hinv := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong σ (tautologicalSection L)))
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp σ T.hom).hom_inv_id_app L.toModules)
  have h0 : (((AlgebraicGeometry.Scheme.Modules.pullbackComp σ T.hom).inv.app L.toModules).val.app
      (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp σ T.hom).hom.app L.toModules).val.app
        (Opposite.op ⊤)).hom (sectionPullbackAlong σ (tautologicalSection L)))
      = sectionPullbackAlong σ (tautologicalSection L) := hinv
  rw [← h0]
  change (((AlgebraicGeometry.Scheme.Modules.pullbackComp σ T.hom).inv.app L.toModules).val.app
      (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp σ T.hom).hom.app L.toModules).val.app
        (Opposite.op ⊤)).hom (sectionPullbackAlong σ
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv L.toModules T (𝟙 T)))) = 0
  rw [← hn]
  exact map_zero _

end
