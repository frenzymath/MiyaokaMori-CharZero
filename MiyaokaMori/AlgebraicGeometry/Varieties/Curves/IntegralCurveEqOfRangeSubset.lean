import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim

/-! # Integral curves with nested supports coincide

If two integral curves `Γ`, `Γ'` in the same variety satisfy `supp Γ ⊆ supp Γ'`, then the supports
are equal and the curves coincide as closed subschemes (there is an isomorphism
`Γ.carrier ≅ Γ'.carrier` compatible with the closed immersions): the only one-dimensional
irreducible closed subset of a one-dimensional irreducible space is the whole space, and a
reduced closed subscheme is determined by its support.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem closed_immersion_range_univ_of_dim_one
    {W X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsIntegral X]
    (w : W ⟶ X) [AlgebraicGeometry.IsClosedImmersion w]
    (hW : topologicalKrullDim W = 1)
    (hX : topologicalKrullDim X = 1)
    (hne : Set.range w.base ≠ Set.univ) : False := by
  let eW : IrreducibleCloseds W ≃o W :=
    @irreducibleSetEquivPoints W _ _ _
  have hkrW : (1 : WithBot ℕ∞) ≤ Order.krullDim (IrreducibleCloseds W) := by
    rw [show Order.krullDim (IrreducibleCloseds W) = topologicalKrullDim W by rfl, hW]
  obtain ⟨A, B, hAB⟩ := Order.one_le_krullDim_iff.mp hkrW
  let a : W := eW A
  let b : W := eW B
  have hab : a < b := by
    exact eW.strictMono hAB
  have hwlt : w.base a < w.base b := by
    exact w.lt_iff_of_isClosedImmersion a b |>.mpr hab
  have hbtop : w.base b < (⊤ : X) := by
    have hne_top : w.base b ≠ (⊤ : X) := by
      intro heq
      apply hne
      rw [Set.eq_univ_iff_forall]
      intro z
      have hcl : IsClosed (Set.range w.base) := w.isClosedEmbedding.isClosed_range
      have htop : (⊤ : X) ∈ Set.range w.base := ⟨b, heq⟩
      have hz : (⊤ : X) ⤳ z := (le_top : z ≤ (⊤ : X))
      exact hz.mem_closed hcl htop
    letI : PartialOrder X := specializationOrder X
    exact lt_of_le_of_ne (show w.base b ≤ (⊤ : X) from le_top) hne_top
  let eX : IrreducibleCloseds X ≃o X :=
    @irreducibleSetEquivPoints X _ _ _
  let A' : IrreducibleCloseds X := eX.symm (w.base a)
  let B' : IrreducibleCloseds X := eX.symm (w.base b)
  let C' : IrreducibleCloseds X := eX.symm (⊤ : X)
  have hA'B' : A' < B' := by exact eX.symm.strictMono hwlt
  have hB'C' : B' < C' := by exact eX.symm.strictMono hbtop
  have h2 : (2 : ℕ) ≤ Order.krullDim (IrreducibleCloseds X) := by
    apply (Order.le_krullDim_iff).2
    refine ⟨⟨2, ![A', B', C'], ?_⟩, rfl⟩
    intro i
    fin_cases i
    · exact hA'B'
    · exact hB'C'
  have hkrX : Order.krullDim (IrreducibleCloseds X) = 1 := by
    rw [show Order.krullDim (IrreducibleCloseds X) = topologicalKrullDim X by rfl, hX]
  rw [hkrX] at h2
  norm_num at h2

theorem IntegralCurve.iso_of_range_subset {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Γ Γ' : IntegralCurve k X)
    (h : Set.range Γ.ι.base ⊆ Set.range Γ'.ι.base) :
    ∃ e : Γ.carrier ≅ Γ'.carrier, e.hom ≫ Γ'.ι = Γ.ι := by
  have hΓqc : AlgebraicGeometry.QuasiCompact Γ.ι := inferInstance
  have hΓ'qc : AlgebraicGeometry.QuasiCompact Γ'.ι := inferInstance
  have hsupp : Γ.ι.ker.support ≤ Γ'.ι.ker.support := by
    change (Γ.ι.ker.support : Set X) ⊆ (Γ'.ι.ker.support : Set X)
    rw [Γ.ι.support_ker, Γ'.ι.support_ker]
    exact closure_mono h
  have hrad {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsClosedImmersion f]
      [AlgebraicGeometry.IsReduced Y] : f.ker = f.ker.radical := by
    ext U x
    have hr : (f.ker.ideal U).IsRadical := by
      rw [AlgebraicGeometry.Scheme.Hom.ker_apply]
      exact (RingHom.ker_isRadical_iff_reduced_of_surjective
        (AlgebraicGeometry.Scheme.Hom.app_surjective f U U.2)).mpr inferInstance
    rw [AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal]
    rw [Ideal.radical_eq_iff.mpr hr]
  have hker : Γ'.ι.ker ≤ Γ.ι.ker := by
    calc
      Γ'.ι.ker ≤ AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Γ'.ι.ker.support :=
        (AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal).mp le_rfl
      _ ≤ AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Γ.ι.ker.support :=
        AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_antimono hsupp
      _ = Γ.ι.ker.radical :=
        AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support
      _ = Γ.ι.ker := hrad Γ.ι |>.symm
  let f : Γ.carrier ⟶ Γ'.carrier :=
    AlgebraicGeometry.IsClosedImmersion.lift Γ'.ι Γ.ι hker
  have hf : f ≫ Γ'.ι = Γ.ι := AlgebraicGeometry.IsClosedImmersion.lift_fac Γ'.ι Γ.ι hker
  letI : AlgebraicGeometry.IsClosedImmersion (f ≫ Γ'.ι) := by
    rw [hf]
    infer_instance
  letI : AlgebraicGeometry.IsClosedImmersion f :=
    AlgebraicGeometry.IsClosedImmersion.of_comp f Γ'.ι
  have hrange : Set.range f.base = Set.univ := by
    by_contra hne
    have hWdim : topologicalKrullDim Γ.carrier = 1 := Γ.dim_eq_one
    have hW'dim : topologicalKrullDim Γ'.carrier = 1 := Γ'.dim_eq_one
    exact closed_immersion_range_univ_of_dim_one f hWdim hW'dim hne
  letI : AlgebraicGeometry.Surjective f := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso f :=
    AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective f
  exact ⟨asIso f, by simpa [f] using hf⟩

end
