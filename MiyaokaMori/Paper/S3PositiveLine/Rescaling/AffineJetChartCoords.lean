import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetGenericChartCoords

/-! # Coordinates of an affine jet `ĵ : Spec κ(η_{C̃}) → J_κ^s` in a jet chart
(base definitions)

Lemma 3.1 of the paper: the generic affine jet is one `K`-point of the affine jet scheme
`J_κ^s ×_C Spec K`, and `b_{α,i,q} ∈ K` is "the value of the local jet-coordinate function
`x_{α,i,q}` on this representative". This module defines that value (`affineJetCoord`), so that the
lemmas of the construction can state their hypotheses in terms of it without importing the assembled theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- The value in `K(C̃)` of a chart coordinate `x = (chart).coords p ∈ S_{w p}(V)` on a
`κ(η_{C̃})`-point `ĵ` of the affine jet scheme `J_κ^s` lying over `V`: `x` is put into
`Γ(J_κ^s, π⁻¹V)` by `BasedJet.partι`, pulled back along `ĵ` to `Γ(Spec κ(η_{C̃}), ⊤) ≅ κ(η_{C̃})`
(`ΓSpecIso`) and read in `K(C̃)` through `functionFieldIsoResidueField`. -/
def affineJetCoord {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ} (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece V m) : ρ.source.toScheme.functionField :=
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).hom.hom
      ((ĵ.appLE _ ⊤ hV).hom
        (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
            (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V) from
          ((BasedJet.partι f κ m).val.app (Opposite.op V)).hom x)))

end
