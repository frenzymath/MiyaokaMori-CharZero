import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesPowLocallyFree
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.VarietyChosenEmbedding
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback

/-! # The cone coordinates of a based jet

The `ℓ`-th cone coordinate of a based jet `ȷ`: compose `ȷ` with the cone embedding `𝒵 ↪ Tot(A^{⊕(N+1)})` and
take the `ℓ`-th component; it is a global section of the pullback of `ρ^*A` to the jet neighbourhood
(the coordinates `P_ℓ^{(κ)}` of `ȷ`, §3–§4 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `ℓ`-th cone coordinate `P_ℓ` of a based jet `J`. The composite `J.hom ≫ (𝒵 ↪ Tot(A^{⊕(N+1)}))` is a morphism
`T := (p_L ≫ ρ) ⟶ Tot` in `Over C`; `totalSpaceHomEquiv` turns it into a section of
`(p_L ≫ ρ)^*(A^{⊕(N+1)})` on `C̃_(κ)(L)`, the `ℓ`-th projection gives a global section of `(p_L ≫ ρ)^*A`, and
`pullbackComp` together with `A = f^*(e.oX 1) = f^*(X.OX 1).toModules` (`OX_toModules`) transports it to the bundle
in the signature. -/
noncomputable def BasedJet.coneCoordinate {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      (LineBundle.pullback (X := ρ.source.toVariety) ρ.hom
        (LineBundle.pullback (X := C.toVariety) f (X.OX 1))).toModules).val.obj
        (Opposite.op ⊤) : Type u) :=
  let D : MMSetup f := inferInstance
  let A := seedLineBundle X.embedding f
  let V := AlgebraicGeometry.Scheme.Modules.pow A (X.embDim + 1)
  let p := jetNeighborhood.proj L κ
  let T : CategoryTheory.Over C.toScheme := CategoryTheory.Over.mk (p ≫ ρ.hom)
  let coneι : (MMSetup.cone f).left ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left :=
    (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A X.embDim (D.E.F j) (D.E.homogeneous j))).subschemeι
  have hcone : coneι ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = (MMSetup.cone f).hom := by
    rfl
  let toTot : T ⟶ AlgebraicGeometry.Scheme.totalSpace V :=
    CategoryTheory.Over.homMk
      (J.hom ≫ coneι)
      (by
        change (J.hom ≫ coneι) ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom =
          p ≫ ρ.hom
        rw [Category.assoc, hcone]
        exact J.over)
  let z := AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T toTot
  let z₁ := (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (X.embDim + 1) => A) ℓ)).val.app
        (Opposite.op ⊤)).hom z
  let z₂ := (((AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ.hom).inv.app A).val.app
      (Opposite.op ⊤)).hom z₁
  (((AlgebraicGeometry.Scheme.Modules.pullback p).map
      ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).map
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1).symm)))).val.app (Opposite.op ⊤)).hom z₂

end
