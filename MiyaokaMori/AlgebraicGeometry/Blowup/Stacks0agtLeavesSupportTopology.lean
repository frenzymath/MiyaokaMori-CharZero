import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agq
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass

/-! # Topological lemmas for the support step of Stacks 0AGT

Two lemmas used by `blowup_improve_support_finite` (Stacks 0AGT, second paragraph):

* `ProjectiveLine.finite_of_isClosed_of_ne_univ`: a proper closed subset of `P¹_k` is a finite set of
  closed points (via the Noetherian property and topological Krull dimension `1`);
* `blowup_regularLocalRing_dimTwo_exceptional_support_closedEmbedding`: the exceptional divisor of
  `Bl_𝔪 Spec A` (`A` regular local of dimension `2`) is, as a topological subspace of the blowup, the
  image of a closed embedding `P¹_κ → X` (Stacks 0AGQ + closed immersions are stable under base change).

Source: Stacks 0AGT proof, second paragraph ("supported in finitely many closed points"); Stacks 0AGQ(1);
Stacks 01IU / 01QO (base change of closed immersions); Hartshorne I, Ex. 1.1 / II Ex. 3.20 (closed
subsets of a curve).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- In a T0 space of topological Krull dimension `≤ 1`, a proper irreducible closed subset is a
singleton. -/
theorem IsIrreducible.eq_singleton_of_topologicalKrullDim_le_one {X : Type u} [TopologicalSpace X]
    [T0Space X] [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1)
    {T : Set X} (hTc : IsClosed T) (hTirr : IsIrreducible T) (hTne : T ≠ Set.univ) :
    ∃ t, T = {t} := by
  obtain ⟨t, ht⟩ := hTirr.nonempty
  have hcl : ∀ s ∈ T, closure {s} = T := by
    intro s hs
    by_contra hne'
    have hlt1 : closure {s} ⊂ T :=
      ssubset_of_subset_of_ne (closure_minimal (Set.singleton_subset_iff.mpr hs) hTc) hne'
    have hlt2 : T ⊂ Set.univ := Set.ssubset_univ_iff.mpr hTne
    let a : IrreducibleCloseds X := ⟨closure {s}, isIrreducible_singleton.closure, isClosed_closure⟩
    let b : IrreducibleCloseds X := ⟨T, hTirr, hTc⟩
    let c : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hab : a < b := hlt1
    have hbc : b < c := hlt2
    let p : LTSeries (IrreducibleCloseds X) :=
      ⟨2, ![a, b, c], fun i => by fin_cases i <;> assumption⟩
    have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X := Order.LTSeries.length_le_krullDim p
    have h3 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := h2.trans hdim
    have h4 : (2 : ℕ) ≤ 1 := by exact_mod_cast h3
    omega
  refine ⟨t, ?_⟩
  ext s
  constructor
  · intro hs
    have h1 : t ∈ closure ({s} : Set X) := (hcl s hs).symm ▸ ht
    have h2 : s ∈ closure ({t} : Set X) := (hcl t ht).symm ▸ hs
    exact Set.mem_singleton_iff.mpr
      ((specializes_iff_mem_closure.mpr h2).antisymm (specializes_iff_mem_closure.mpr h1)).eq.symm
  · rintro rfl
    exact ht

/-- **A proper closed subset of `P¹_k` is a finite set of closed points.**

Proof (purely topological). `P¹_k` is a Noetherian space (`Variety.isNoetherian` for the curve `P¹`,
Stacks 01OZ), so `Z` is a finite union of irreducible closed sets
(`NoetherianSpace.exists_finite_set_isClosed_irreducible`); each of them is a proper irreducible
closed subset of the irreducible T0 space `P¹_k` of topological Krull dimension `1`
(`SmoothProjectiveCurve.dim_one`), hence a closed singleton
(`IsIrreducible.eq_singleton_of_topologicalKrullDim_le_one`: a chain `closure{s} ⊊ T ⊊ P¹` of
irreducible closed sets would have length `2`).

`blowup_improve_support_finite` (Stacks 0AGT, second paragraph, "supported in finitely many closed
points of `X`") applies this to `Z = f⁻¹(supp I')` for the closed embedding `f : P¹_κ → X` below,
with `Z ≠ univ` coming from `supp E ⊄ supp I'`, over the residue field `κ` of `A` (an arbitrary
field, possibly finite). Edge cases: `Z = ∅` (both conjuncts trivial); the hypothesis `Z ≠ univ`
cannot be dropped (the generic point of `P¹_k` is not closed). -/
theorem ProjectiveLine.finite_of_isClosed_of_ne_univ (k : Type u) [Field k]
    (Z : Set (ProjectiveLine k)) (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    Z.Finite ∧ ∀ z ∈ Z, IsClosed ({z} : Set (ProjectiveLine k)) := by
  have hN : AlgebraicGeometry.IsNoetherian (ProjectiveLine k) :=
    Variety.isNoetherian (ProjectiveLine.asSmoothProjectiveCurve k).toVariety
  have : IrreducibleSpace (ProjectiveLine k) :=
    AlgebraicGeometry.Proj.ProjectiveLineIrreducible.projectiveLine_irreducible k
  have hdim : topologicalKrullDim (ProjectiveLine k) ≤ 1 := by
    have h : topologicalKrullDim (ProjectiveLine k) = 1 :=
      (ProjectiveLine.asSmoothProjectiveCurve k).dim_one
    exact h.le
  obtain ⟨S, hSfin, hScl, hSirr, hZS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have hsing : ∀ T ∈ S, ∃ t, T = {t} := by
    intro T hT
    refine IsIrreducible.eq_singleton_of_topologicalKrullDim_le_one hdim (hScl T hT) (hSirr T hT) ?_
    intro hTu
    apply hne
    rw [hZS]
    exact Set.univ_subset_iff.mp (hTu ▸ Set.subset_sUnion_of_mem hT)
  constructor
  · rw [hZS]
    refine Set.Finite.sUnion hSfin fun T hT => ?_
    obtain ⟨t, rfl⟩ := hsing T hT
    exact Set.finite_singleton t
  · intro z hz
    rw [hZS] at hz
    obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.mp hz
    obtain ⟨t, rfl⟩ := hsing T hT
    rw [Set.mem_singleton_iff] at hzT
    subst hzT
    exact hScl _ hT


/-- **The exceptional divisor of `Bl_𝔪 Spec A` is a closed copy of `P¹_κ`** (topologically):
there is a closed embedding `f : P¹_κ → X` whose range is the support of the exceptional ideal
`E = 𝔪·O_X`.

Natural-language proof (complete).
1. Stacks 0AGQ (`blowup_regularLocalRing_dimTwo_exceptional_over_residueField`):
   `P := X ×_{Spec A} Spec κ ≅ P¹_κ`, where `g : Spec κ → Spec A` is `Spec` of the residue
   map. Let `f := ε.inv ≫ pullback.fst b g : P¹_κ → X` (on underlying spaces).
2. `g` is a closed immersion (`IsClosedImmersion.spec_of_surjective`, the residue map is surjective),
   closed immersions are stable under base change (`IsClosedImmersion.isStableUnderBaseChange`), so
   `pullback.fst b g` is a closed immersion, i.e. a closed embedding on underlying spaces
   (`Scheme.Hom.isClosedEmbedding`); composing with the homeomorphism `ε.inv` keeps it a closed
   embedding (`Topology.IsClosedEmbedding.comp`, `Homeomorph.isClosedEmbedding`).
3. `range (pullback.fst b g) = b⁻¹(range g)` (`Scheme.Pullback.range_fst`), and `range g` is the closed
   point `𝔪` of `Spec A` (`Spec.map_apply`, `PrimeSpectrum.comap_asIdeal`, the unique prime of `κ` is
   `⊥` and `(algebraMap A κ)⁻¹(⊥) = 𝔪` by `IsLocalRing.residue_eq_zero_iff`); so
   `range f = b⁻¹{𝔪} = b⁻¹(supp J) = supp E` (`support_comap`, `coe_support_ofIdealTop`,
   `Spec_zeroLocus`; the last computation is the one in
   `blowup_regularLocalRing_dimTwo_exceptional_support_nonempty`, `Stacks0agtLeavesExponentCore.lean`,
   which does the `⊆` direction pointwise).

Edge cases: none (`A` has dimension `2`, so `κ ≠ 0` and `P¹_κ ≠ ∅`). -/
theorem AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptional_support_closedEmbedding
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    let e := (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    let J : (AlgebraicGeometry.Spec (CommRingCat.of A)).IdealSheafData :=
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop ((IsLocalRing.maximalIdeal A).map e)
    ∃ f : ProjectiveLine (IsLocalRing.ResidueField A) → (AlgebraicGeometry.Scheme.blowup J).left,
      Topology.IsClosedEmbedding f ∧
      Set.range f = ((AlgebraicGeometry.Scheme.blowup.exceptionalIdeal J).support : Set _) := by
  intro e J
  obtain ⟨ε, -⟩ := AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptional_over_residueField A hdim
  let b := (AlgebraicGeometry.Scheme.blowup J).hom
  let g := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)))
  have hsurj : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hg : AlgebraicGeometry.IsClosedImmersion g :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ hsurj
  have hfst : AlgebraicGeometry.IsClosedImmersion (pullback.fst b g) := inferInstance
  let h := AlgebraicGeometry.Scheme.homeoOfIso ε.symm
  refine ⟨fun p => pullback.fst b g (h p), ?_, ?_⟩
  · exact (pullback.fst b g).isClosedEmbedding.comp h.isClosedEmbedding
  · have hr : Set.range (fun p => pullback.fst b g (h p)) = Set.range (pullback.fst b g) :=
      h.surjective.range_comp (pullback.fst b g)
    rw [hr, AlgebraicGeometry.Scheme.Pullback.range_fst]
    show b ⁻¹' Set.range g = ((J.comap b).support : Set _)
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    show b ⁻¹' Set.range g = b ⁻¹' (J.support : Set _)
    congr 1
    rw [AlgebraicGeometry.Scheme.IdealSheafData.coe_support_ofIdealTop, AlgebraicGeometry.Spec_zeroLocus]
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      refine (PrimeSpectrum.mem_zeroLocus _ _).mpr ?_
      intro a ha
      rw [Set.mem_preimage, SetLike.mem_coe] at ha
      have hbot : (w : AlgebraicGeometry.Spec (CommRingCat.of (IsLocalRing.ResidueField A))).asIdeal = ⊥ := by
        rcases Ideal.eq_bot_or_top w.asIdeal with h | h
        · exact h
        · exact absurd h w.isPrime.ne_top
      show a ∈ Ideal.comap (algebraMap A (IsLocalRing.ResidueField A))
        (w : AlgebraicGeometry.Spec (CommRingCat.of (IsLocalRing.ResidueField A))).asIdeal
      rw [hbot, Ideal.mem_comap, Ideal.mem_bot]
      obtain ⟨a', ha', haa⟩ := Ideal.mem_map_iff_of_surjective _
        (ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
        |>.mp ha
      have hinj := (ConcreteCategory.bijective_of_isIso
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv).1 haa
      rw [← hinj]
      show algebraMap A (IsLocalRing.ResidueField A) a' = 0
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
      exact ha'
    · intro hz
      have hz' := (PrimeSpectrum.mem_zeroLocus _ _).mp hz
      have hle : IsLocalRing.maximalIdeal A ≤ (z : PrimeSpectrum A).asIdeal := by
        intro m hm
        exact hz' (Set.mem_preimage.mpr (Ideal.mem_map_of_mem _ hm))
      have hz'' : (z : PrimeSpectrum A).asIdeal = IsLocalRing.maximalIdeal A :=
        ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le z.isPrime.ne_top hle).symm
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap A (IsLocalRing.ResidueField A)) ⊥ = (z : PrimeSpectrum A).asIdeal
      rw [hz'', ← RingHom.ker_eq_comap_bot, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]


end
