import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.FinitePrimesOverHeightOne
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.DominantAffineAlgebraic

/-! # Finiteness of a proper dominant morphism over a codimension-one point

Stacks Project, Tag 02RM: let `X`, `Y` be integral with `Y` locally Noetherian, `f` proper and dominant
with `R(X)/R(Y)` finite, and `dim O_{Y,ξ} = 1`; then `ξ` has an open neighbourhood `V` such that
`f⁻¹(V) → V` is finite. Used in Stacks 02RU: a dominant proper morphism from an integral curve to `P¹`
is finite.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry in
/-- Only finitely many points of an affine open `V ⊆ f⁻¹U` map to `ξ` (Stacks 02MA). -/
private theorem finite_fiber_inter_affine {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : f.base (genericPoint X) = genericPoint Y)
    (hfin : (f.residueFieldMap (genericPoint X)).hom.Finite) (ξ : Y)
    (hξ : ringKrullDim (Y.presheaf.stalk ξ) = 1) {U : Y.Opens} (hU : IsAffineOpen U) (hξU : ξ ∈ U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    (f.base ⁻¹' {ξ} ∩ (V : Set X)).Finite := by
  classical
  by_cases hne : (V : Set X).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.inter_empty]; exact Set.finite_empty
  have hηV : genericPoint X ∈ V := genericPoint_mem_of_nonempty V hne
  have : Nonempty U := ⟨⟨ξ, hξU⟩⟩
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  have hinj := appLE_injective_of_genericPoint f hf U V e hηV
  have halg := appLE_isAlgebraic_of_genericPoint f hfin hU V e hηV
  have hft : (f.appLE U V e).hom.FiniteType := f.finiteType_appLE hU hV e
  have hnoeth : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  algebraize [(f.appLE U V e).hom]
  have : FaithfulSMul Γ(Y, U) Γ(X, V) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let p : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal
  have hp : p.height = 1 := by
    letI := Y.presheaf.algebra_section_stalk ⟨ξ, hξU⟩
    have hloc := hU.isLocalization_stalk ⟨ξ, hξU⟩
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height p (Y.presheaf.stalk ξ)
    rw [hξ] at h1
    exact_mod_cast h1.symm
  obtain ⟨hfinite, -⟩ := Ideal.finite_primesOver_and_height_eq_one (B := Γ(X, V)) p hp
  let φ : X → Ideal Γ(X, V) := fun x ↦
    if h : x ∈ V then (hV.primeIdealOf ⟨x, h⟩).asIdeal else ⊥
  refine Set.Finite.of_injOn (f := φ) (t := p.primesOver Γ(X, V)) ?_ ?_ hfinite
  · rintro x ⟨hxξ, hxV⟩
    have hxV' : x ∈ V := hxV
    simp only [φ, dif_pos hxV']
    refine ⟨(hV.primeIdealOf ⟨x, hxV'⟩).isPrime, ⟨?_⟩⟩
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) U hU V hV e hxV'
    have hxξ' : f.base x = ξ := hxξ
    subst hxξ'
    exact congr($(h1).asIdeal).symm
  · rintro x ⟨-, hxV⟩ x' ⟨-, hxV'⟩ hxx'
    have hxV₁ : x ∈ V := hxV
    have hxV₂ : x' ∈ V := hxV'
    simp only [φ, dif_pos hxV₁, dif_pos hxV₂] at hxx'
    have h2 : hV.primeIdealOf ⟨x, hxV₁⟩ = hV.primeIdealOf ⟨x', hxV₂⟩ := PrimeSpectrum.ext hxx'
    have h3 := hV.fromSpec_primeIdealOf ⟨x, hxV₁⟩
    rw [h2, hV.fromSpec_primeIdealOf] at h3
    exact h3.symm

theorem AlgebraicGeometry.exists_isFinite_restrict_of_dim_one {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsLocallyNoetherian Y] (f : X ⟶ Y) [AlgebraicGeometry.IsProper f]
    (hf : f.base (genericPoint X) = genericPoint Y)
    (hfin : (f.residueFieldMap (genericPoint X)).hom.Finite) (ξ : Y)
    (hξ : ringKrullDim (Y.presheaf.stalk ξ) = 1) :
    ∃ V : Y.Opens, ξ ∈ V ∧ AlgebraicGeometry.IsFinite (f ∣_ V) := by
  apply exists_isFinite_morphismRestrict_of_finite_preimage_singleton
  obtain ⟨_, ⟨U, hU, rfl⟩, hξU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ξ) isOpen_univ
  have hc : IsCompact (f ⁻¹ᵁ U : Set X) :=
    QuasiCompact.isCompact_preimage (f := f) _ U.2 hU.isCompact
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := f ⁻¹ᵁ U)).mp hc
  have hle : ∀ V ∈ s, (V : X.Opens) ≤ f ⁻¹ᵁ U := fun V hV ↦ by
    rw [hsU]; exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) ↦ (i : X.Opens)) V hV
  refine (hs.biUnion fun V hV ↦ finite_fiber_inter_affine f hf hfin ξ hξ hU hξU V.2
    (hle V hV)).subset ?_
  intro x hx
  have hxU : x ∈ f ⁻¹ᵁ U := by
    have : f.base x = ξ := hx
    show f.base x ∈ U
    rw [this]; exact hξU
  rw [hsU] at hxU
  simp only [Opens.mem_iSup] at hxU
  obtain ⟨V, hVs, hxV⟩ := hxU
  exact Set.mem_biUnion hVs ⟨hx, hxV⟩

end
