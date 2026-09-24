import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalIsLocal
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SpecNormalOfIntegrallyClosed
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks0358

/-! # The relative normalization in a normal scheme is normal (Stacks 035L)

Stacks 035L: if the source is a normal integral scheme (e.g. the spectrum of a field), the
normalization of `X` in it is a normal scheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 035L: the normalization of `X` in a normal integral scheme is normal. -/
theorem AlgebraicGeometry.Scheme.Hom.normalization_isNormal {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    [AlgebraicGeometry.IsIntegral X] [X.IsNormal] : f.normalization.IsNormal := by
  apply isNormal_of_openCover f.normalizationOpenCover
  intro U
  let := (f.app U.1).hom.toAlgebra
  dsimp [AlgebraicGeometry.Scheme.Hom.normalizationOpenCover,
    AlgebraicGeometry.Scheme.Hom.normalizationGlueData,
    AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData]
  change (AlgebraicGeometry.Spec ((f.normalizationDiagram).obj (.op U.1))).IsNormal
  by_cases hV : Nonempty (f ⁻¹ᵁ U.1)
  · let : Nonempty (f ⁻¹ᵁ U.1) := hV
    let : AlgebraicGeometry.IsIntegral (f ⁻¹ᵁ U.1) := inferInstance
    let : AlgebraicGeometry.Scheme.IsNormal (f ⁻¹ᵁ U.1).toScheme := by
      constructor
      · intro x
        let e := ((f ⁻¹ᵁ U.1).stalkIso x).commRingCatIsoToRingEquiv
        exact e.toMulEquiv.isDomain _
      · intro x
        let e := ((f ⁻¹ᵁ U.1).stalkIso x).commRingCatIsoToRingEquiv
        let : IsIntegrallyClosed (X.presheaf.stalk x.1) :=
          AlgebraicGeometry.Scheme.IsNormal.integrallyClosed x.1
        exact IsIntegrallyClosed.of_equiv e.symm
    let : IsDomain Γ(X, f ⁻¹ᵁ U.1) :=
      AlgebraicGeometry.IsIntegral.component_integral (f ⁻¹ᵁ U.1)
    let : IsIntegrallyClosed Γ(f ⁻¹ᵁ U.1, ⊤) :=
      AlgebraicGeometry.Scheme.isIntegrallyClosed_Γ_of_isNormal (f ⁻¹ᵁ U.1)
    let : IsIntegrallyClosed Γ(X, f ⁻¹ᵁ U.1) := IsIntegrallyClosed.of_equiv
      (f ⁻¹ᵁ U.1).topIso.commRingCatIsoToRingEquiv
    let hClosedIntegralClosure :
        IsIntegrallyClosed (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)) :=
      .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ Γ(X, f ⁻¹ᵁ U.1)
    let : IsDomain ((f.normalizationDiagram).obj (.op U.1)) := by
      dsimp [AlgebraicGeometry.Scheme.Hom.normalizationDiagram]
      exact Subtype.val_injective.isDomain
        (CommRingCat.ofHom
          (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom).hom
    let : IsIntegrallyClosed ((f.normalizationDiagram).obj (.op U.1)) := by
      dsimp [AlgebraicGeometry.Scheme.Hom.normalizationDiagram]
      exact hClosedIntegralClosure
    exact AlgebraicGeometry.Spec_isNormal_of_isIntegrallyClosed _
  · have hVbot : f ⁻¹ᵁ U.1 = ⊥ := by
      apply SetLike.ext'
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      exact hV ⟨⟨x, hx⟩⟩
    have : Subsingleton Γ(X, f ⁻¹ᵁ U.1) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hVbot)
    let : Subsingleton ((f.normalizationDiagram).obj (.op U.1)) := by
      dsimp [AlgebraicGeometry.Scheme.Hom.normalizationDiagram]
      infer_instance
    constructor <;> intro x <;>
      exact (x.isPrime.ne_top (Subsingleton.elim x.asIdeal ⊤)).elim

end
