import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Irreducible

/-! # A connected normal Noetherian scheme is integral (Stacks 033M)

Stacks 033M: a Noetherian scheme is normal iff it is a finite disjoint union of normal integral
schemes; in particular a nonempty connected normal Noetherian scheme is integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Set
open scoped AlgebraicGeometry

noncomputable section

private theorem unique_minimalPrime_below_of_localization_domain
    {R : Type*} [CommRing R] (q : PrimeSpectrum R)
    [hdom : IsDomain (Localization.AtPrime q.asIdeal)]
    {p p' : Ideal R}
    (hp : p ∈ minimalPrimes R) (hp' : p' ∈ minimalPrimes R)
    (hpq : p ≤ q.asIdeal) (hp'q : p' ≤ q.asIdeal) : p = p' := by
  let A := Localization.AtPrime q.asIdeal
  let f : R →+* A := algebraMap R A
  have hmap : Ideal.map f (⊥ : Ideal R) = (⊥ : Ideal A) := by simp [f]
  have hmin := IsLocalization.minimalPrimes_map q.asIdeal.primeCompl A (⊥ : Ideal R)
  have hmem : Ideal.map f p ∈ minimalPrimes A := by
    have hm : Ideal.map f p ∈ (Ideal.map f (⊥ : Ideal R)).minimalPrimes := by
      rw [hmin]
      change Ideal.under R (Ideal.map f p) ∈ minimalPrimes R
      rw [IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A hp.1.1]
      · exact hp
      · simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
    simpa [hmap] using hm
  have hmem' : Ideal.map f p' ∈ minimalPrimes A := by
    have hm : Ideal.map f p' ∈ (Ideal.map f (⊥ : Ideal R)).minimalPrimes := by
      rw [hmin]
      change Ideal.under R (Ideal.map f p') ∈ minimalPrimes R
      rw [IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A hp'.1.1]
      · exact hp'
      · simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hp'q]
    simpa [hmap] using hm
  rw [IsDomain.minimalPrimes_eq_singleton_bot A] at hmem hmem'
  have hzero : Ideal.map f p = (⊥ : Ideal A) := by simpa using hmem
  have hzero' : Ideal.map f p' = (⊥ : Ideal A) := by simpa using hmem'
  have hunder : Ideal.under R (Ideal.map f p) = p := by
    apply IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A hp.1.1
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  have hunder' : Ideal.under R (Ideal.map f p') = p' := by
    apply IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A hp'.1.1
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hp'q]
  calc
    p = Ideal.under R (Ideal.map f p) := hunder.symm
    _ = Ideal.under R (Ideal.map f p') := by rw [hzero, hzero']
    _ = p' := hunder'

private theorem affine_local_irreducible_of_stalk_domains
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (hdom : ∀ q : PrimeSpectrum R, IsDomain (Localization.AtPrime q.asIdeal))
    (q : PrimeSpectrum R) :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ q ∈ U ∧ IsIrreducible U := by
  let α := PrimeSpectrum R
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal) bot_le
  let Z : Set α := PrimeSpectrum.zeroLocus (p : Set R)
  have hZcomp : Z ∈ irreducibleComponents α := by
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
    exact ⟨p, hp, rfl⟩
  have hqZ : q ∈ Z := by
    exact hpq
  have huniq : ∀ W ∈ irreducibleComponents α, W ≠ Z → q ∉ W := by
    intro W hW hWZ hqW
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hW
    obtain ⟨p', hp', rfl⟩ := hW
    have hp'q : p' ≤ q.asIdeal := by
      exact hqW
    have heq : p = p' := unique_minimalPrime_below_of_localization_domain q hp hp' hpq hp'q
    exact hWZ (heq ▸ rfl)
  let U : Set α := (⋃₀ (irreducibleComponents α \ {Z}))ᶜ
  have hUopen : IsOpen U := by
    rw [isOpen_compl_iff]
    rw [Set.sUnion_eq_biUnion]
    have hfin : (irreducibleComponents α \ {Z}).Finite :=
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)).sdiff
    exact hfin.isClosed_biUnion (fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1)
  have hqU : q ∈ U := by
    intro hq
    simp only [U, mem_compl_iff, mem_sUnion] at hq
    obtain ⟨W, hW, hqW⟩ := hq
    exact huniq W hW.1 hW.2 hqW
  have hUZ : U ⊆ Z := by
    have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton
      (X := α) (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)) Z hZcomp
    exact subset_closure.trans (hcl ▸ subset_rfl)
  refine ⟨U, hUopen, hqU, ?_⟩
  have hZirr : IsIrreducible Z := by
    rw [PrimeSpectrum.isIrreducible_zeroLocus_iff]
    simpa [hp.1.1.radical] using hp.1.1
  apply IsPreirreducible.subset_irreducible (t := Z) hZirr.2
  · exact ⟨q, hqU⟩
  · exact hUopen
  · exact subset_rfl
  · exact hUZ

private theorem normal_scheme_local_irreducible
    {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsNoetherian X]
    [X.IsNormal] :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U := by
  letI : AlgebraicGeometry.IsReduced X := by
    letI : ∀ x : X, IsReduced (X.presheaf.stalk x) := fun x => by
      letI : IsDomain (X.presheaf.stalk x) :=
        AlgebraicGeometry.Scheme.IsNormal.isDomain (X := X) x
      infer_instance
    exact AlgebraicGeometry.isReduced_of_isReduced_stalk X
  intro x
  obtain ⟨W, hW, hxW, _⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let R := Γ(X, W)
  letI : IsNoetherianRing R :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : IsReduced R := AlgebraicGeometry.IsReduced.component_reduced W
  let q : PrimeSpectrum R := hW.primeIdealOf ⟨x, hxW⟩
  have hdom : ∀ p : PrimeSpectrum R, IsDomain (Localization.AtPrime p.asIdeal) := by
    intro p
    let y : X := hW.fromSpec p
    have hy : y ∈ W := by
      have hy' : hW.fromSpec p ∈ Set.range hW.fromSpec := ⟨p, rfl⟩
      rwa [hW.range_fromSpec] at hy'
    letI : Algebra R (X.presheaf.stalk y) :=
      X.presheaf.algebra_section_stalk ⟨y, hy⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal :=
      hW.isLocalization_stalk' p hy
    letI : IsDomain (X.presheaf.stalk y) :=
      AlgebraicGeometry.Scheme.IsNormal.isDomain (X := X) y
    exact (IsLocalization.algEquiv p.asIdeal.primeCompl
      (X.presheaf.stalk y) (Localization.AtPrime p.asIdeal)).symm.toMulEquiv.isDomain _
  obtain ⟨V, hVopen, hqV, hVirr⟩ :=
    affine_local_irreducible_of_stalk_domains hdom q
  refine ⟨hW.fromSpec '' V, hW.fromSpec.isOpenEmbedding.isOpenMap V hVopen,
    ?_, hVirr.image hW.fromSpec hW.fromSpec.continuous.continuousOn⟩
  refine ⟨q, hqV, ?_⟩
  exact hW.fromSpec_primeIdealOf ⟨x, hxW⟩

private theorem locally_irreducible_connected_irreducible
    {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [ConnectedSpace α]
    (hlocal : ∀ x : α, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) :
    IrreducibleSpace α := by
  have hopen_comp : ∀ Z ∈ irreducibleComponents α, IsOpen Z := by
    intro Z hZ
    apply (subset_interior_iff_isOpen).mp
    intro x hxZ
    obtain ⟨U, hUopen, hxU, hUirr⟩ := hlocal x
    obtain ⟨V, hVcomp, hUV⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible U hUirr
    have hZV : Z ⊆ V := by
      apply (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 hUopen
        ⟨x, hxZ, hxU⟩).trans
      exact closure_minimal (fun y hy => hUV hy.2)
        (isClosed_of_mem_irreducibleComponents V hVcomp)
    have hZeqV : Z = V := hZ.eq_of_subset hVcomp.1 hZV
    have hVZ : V ⊆ Z := hZeqV ▸ subset_rfl
    exact mem_interior.mpr ⟨U, hUV.trans hVZ, hUopen, hxU⟩
  have hopen_clopen : ∀ Z ∈ irreducibleComponents α, IsClopen Z := by
    intro Z hZ
    exact ⟨isClosed_of_mem_irreducibleComponents Z hZ, hopen_comp Z hZ⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty α)
  let Z := irreducibleComponent x
  have hZcomp : Z ∈ irreducibleComponents α :=
    irreducibleComponent_mem_irreducibleComponents x
  have hZclopen : IsClopen Z := hopen_clopen Z hZcomp
  have hZnonempty : Z.Nonempty := ⟨x, mem_irreducibleComponent⟩
  have hZeq : Z = Set.univ := IsClopen.eq_univ hZclopen hZnonempty
  apply (irreducibleSpace_def α).mpr
  change IsIrreducible (Set.univ : Set α)
  rw [← hZeq]
  exact isIrreducible_irreducibleComponent (x := x)

/-- Stacks 033M: a nonempty connected normal Noetherian scheme is integral. -/
theorem AlgebraicGeometry.isIntegral_of_isNormal_of_connected {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] [X.IsNormal] [ConnectedSpace X] :
    AlgebraicGeometry.IsIntegral X := by
  letI : AlgebraicGeometry.IsReduced X := by
    letI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      letI : IsDomain (X.presheaf.stalk x) :=
        AlgebraicGeometry.Scheme.IsNormal.isDomain (X := X) x
      infer_instance
    exact AlgebraicGeometry.isReduced_of_isReduced_stalk X
  letI : IrreducibleSpace X :=
    locally_irreducible_connected_irreducible (normal_scheme_local_irreducible (X := X))
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced X

end
