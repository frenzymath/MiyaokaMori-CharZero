import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedImmersionOpenComplement
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeContainsZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedImmersionOpenComplement
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Morphisms.SectionClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Morphisms.SectionOfSeparatedIsClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineConeAffineHom
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection

/-! # The punctured cone as an open subscheme

The punctured cone `𝒵^× = 𝒵 ∖ (zero section)`, as an open subscheme of `𝒵`
(Definition 2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The punctured cone `𝒵^× ⊂ 𝒵`: the open complement of the vertex (zero) section of the twisted affine cone. -/
noncomputable def puncturedCone {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (hdeg : ∀ j, 0 < deg j)
    (F : ι → MvPolynomial (Fin (N + 1)) k) (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    (twistedAffineCone A N deg F hF).left.Opens :=
  -- The vertex section `σ : C → Z`: the zero section factors through the closed subscheme `Z`
  -- (`ConeContainsZeroSection` gives the inclusion of kernels), lifted by the universal property of
  -- the closed immersion.
  let I : (AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left.IdealSheafData :=
    ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (F j) (hF j))
  let σ : C ⟶ (twistedAffineCone A N deg F hF).left :=
    (AlgebraicGeometry.IsClosedImmersion.lift I.subschemeι
      (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))) (by
        obtain ⟨τ, hτ⟩ := zeroSection_mem_twistedAffineCone A N deg hdeg F hF
        rw [← hτ]
        exact AlgebraicGeometry.Scheme.Hom.le_ker_comp _ _) : C ⟶ I.subscheme)
  haveI : AlgebraicGeometry.IsClosedImmersion σ :=
    AlgebraicGeometry.IsClosedImmersion.of_section (twistedAffineCone A N deg F hF).hom σ (by
      -- σ ≫ ι_Z ≫ π = zeroSection ≫ π = 𝟙
      simp only [σ, twistedAffineCone, CategoryTheory.Over.mk_hom]
      rw [AlgebraicGeometry.IsClosedImmersion.lift_fac_assoc]
      exact AlgebraicGeometry.Scheme.zeroSection_comp _)
  AlgebraicGeometry.Scheme.complementOfClosedImmersion σ

end
