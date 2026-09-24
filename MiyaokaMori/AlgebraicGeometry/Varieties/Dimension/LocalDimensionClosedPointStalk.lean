import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimensionOpenEmbedding
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00ot
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension

/-! # Local dimension at a closed point equals the dimension of the stalk

For a `k`-scheme locally of finite type, the local dimension at a closed point equals the Krull
dimension of the local ring at that point (the meaning of `dim_[f]` in Debarre, 6.11/6.12).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For a `k`-scheme locally of finite type, the (untruncated) infimum of the dimensions of the open
neighbourhoods of a closed point `p` equals the Krull dimension of the stalk. -/
private theorem iInf_topologicalKrullDim_opens_eq_ringKrullDim_stalk {k : Type u} [Field k]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : Z) (hp : IsClosed {p}) :
    (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) = ringKrullDim (Z.presheaf.stalk p) ∧
      ringKrullDim (Z.presheaf.stalk p) ≠ ⊤ := by
  -- take an affine open neighbourhood `V = Spec A` of `p`, with `A` a finitely generated `k`-algebra
  obtain ⟨_, ⟨V, hV0, rfl⟩, hpV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  have hV : AlgebraicGeometry.IsAffineOpen V := hV0
  let f := Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let φ : k →+* Γ(Z, V) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (f.appLE ⊤ V le_top).hom.FiniteType :=
      f.finiteType_appLE (AlgebraicGeometry.isAffineOpen_top _) hV _
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let _ : Algebra k Γ(Z, V) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(Z, V) := hφ
  have hNoeth : IsNoetherianRing Γ(Z, V) := Algebra.FiniteType.isNoetherianRing k Γ(Z, V)
  have hopen : AlgebraicGeometry.IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let _ : Algebra Γ(Z, V) (Z.presheaf.stalk p) := Z.presheaf.algebra_section_stalk ⟨p, hpV⟩
  let y : PrimeSpectrum Γ(Z, V) := hV.primeIdealOf ⟨p, hpV⟩
  have hy : hV.fromSpec y = p := hV.fromSpec_primeIdealOf ⟨p, hpV⟩
  -- `y` is a closed point, i.e. a maximal ideal
  have hymax : y.asIdeal.IsMaximal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    have hpre : ({y} : Set (PrimeSpectrum Γ(Z, V))) = hV.fromSpec ⁻¹' {p} := by
      ext z
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl
        exact hy
      · intro hz
        exact hV.fromSpec.isOpenEmbedding.injective (hz.trans hy.symm)
    rw [hpre]
    exact hp.preimage hV.fromSpec.continuous
  have hloc : IsLocalization.AtPrime (Z.presheaf.stalk p) y.asIdeal := hV.isLocalization_stalk ⟨p, hpV⟩
  have hstalk : ringKrullDim (Z.presheaf.stalk p) = ringKrullDim (Localization.AtPrime y.asIdeal) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal (Z.presheaf.stalk p),
      IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal (Localization.AtPrime y.asIdeal)]
  refine ⟨?_, ?_⟩
  · have hinf := hV.fromSpec.isOpenEmbedding.iInf_topologicalKrullDim_opens_eq y
    rw [hy] at hinf
    rw [hstalk]
    refine hinf.symm.trans (((stacks_00OT (k := k) Γ(Z, V) y).2).trans ?_)
    apply le_antisymm
    · exact iInf_le_of_le y (iInf_le_of_le hymax (iInf_le_of_le le_rfl le_rfl))
    · refine le_iInf fun m => le_iInf fun _ => le_iInf fun hym => ?_
      have hmy : m = y := by
        apply PrimeSpectrum.ext
        exact (hymax.eq_of_le m.2.ne_top hym).symm
      rw [hmy]
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal (Z.presheaf.stalk p)]
    intro h
    exact Ideal.height_ne_top_of_isPrime (I := y.asIdeal) (WithBot.coe_injective h)

/-- The local dimension at a closed point equals the Krull dimension of the stalk. -/
theorem localDimension_eq_ringKrullDim_stalk {k : Type u} [Field k]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : Z) (hp : IsClosed {p}) :
    ((localDimension Z p : ℕ∞) : WithBot ℕ∞) = ringKrullDim (Z.presheaf.stalk p) := by
  obtain ⟨hI, htop⟩ := iInf_topologicalKrullDim_opens_eq_ringKrullDim_stalk (k := k) Z p hp
  unfold localDimension
  rw [hI]
  have hbot : ringKrullDim (Z.presheaf.stalk p) ≠ ⊥ := by
    intro h
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (Z.presheaf.stalk p) := ringKrullDim_nonneg_of_nontrivial
    rw [h] at h0
    exact absurd h0 (by simp)
  generalize ringKrullDim (Z.presheaf.stalk p) = d at hbot htop
  cases d with
  | bot => exact (hbot rfl).elim
  | coe a =>
    have ha : a ≠ ⊤ := by
      rintro rfl
      exact htop rfl
    rw [WithBot.unbotD_coe]
    exact congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) (ENat.natCast_toNat ha)

end
