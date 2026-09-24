import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentability
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme

/-! # The jet scheme is affine over the base

`J_k^s ⟶ C` is an affine morphism (hence `J_k^s = Spec_C S`; §2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance relativeJetScheme_isAffineHom {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    AlgebraicGeometry.IsAffineHom (relativeJetScheme (k := k) Z s hs r).hom := by
  constructor
  intro U hU
  let U' : C.AffineZariskiSite := ⟨U, hU⟩
  change AlgebraicGeometry.IsAffineOpen
    ((relativeJetScheme.gluingData Z s hs r).toBase ⁻¹ᵁ U'.toOpens)
  rw [← AlgebraicGeometry.Scheme.Opens.opensRange_ι U'.toOpens]
  have hpre :
      (relativeJetScheme.gluingData Z s hs r).toBase ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover C).f U').opensRange =
        ((relativeJetScheme.gluingData Z s hs r).cover.f U').opensRange := by
    simpa using!
      (relativeJetScheme.gluingData Z s hs r).toBase_preimage_eq_opensRange_ι U'
  rw [hpre]
  letI : AlgebraicGeometry.IsAffine
      ((relativeJetScheme.gluingData Z s hs r).cover.X U') := by
    change AlgebraicGeometry.IsAffine (AlgebraicGeometry.Spec _)
    infer_instance
  letI : AlgebraicGeometry.IsOpenImmersion
      ((relativeJetScheme.gluingData Z s hs r).cover.f U') :=
    relativeJetScheme.chart_isOpenImmersion Z s hs r U'
  exact AlgebraicGeometry.isAffineOpen_opensRange _

end
