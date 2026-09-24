import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.Stacks00i7

/-! # Irreducible schemes over a separably closed field are geometrically irreducible

Stacks 020J: if `k` is separably closed and `X` is an irreducible scheme over `k`, then `X_K` is
irreducible for every field extension `K/k`. The algebraic input is Stacks 00I7
(`irreducibleSpace_tensor_of_isSepClosed`).

Proof sketch:
let `g : Spec K ⟶ Spec k`, `q = pullback.fst p g : X_K ⟶ X`, and let `𝒰 = X.affineOpenCover`
(pieces `Spec Rᵢ`). `X_K` is covered by the open immersions `𝒱ᵢ = (Spec Rᵢ) ×_{Spec k} Spec K`
(`Scheme.Pullback.openCoverOfLeft`), whose ranges are `q⁻¹(range 𝒰ᵢ)` (`Scheme.Pullback.range_map`).
1. Each nonempty `𝒱ᵢ` is irreducible: `Spec Rᵢ` is a nonempty open of the irreducible `X`, so
   `Spec Rᵢ` is irreducible; `𝒱ᵢ ≅ Spec (Rᵢ ⊗_k K)` by `pullbackSpecIso` (after writing
   `𝒰ᵢ ≫ p = Spec.map φ` with `Spec.map_surjective` and putting the `k`-algebra structure `φ` on
   `Rᵢ`), and `Spec (Rᵢ ⊗_k K)` is irreducible by 00I7.
2. Two nonempty ranges meet: `range 𝒰ᵢ ∩ range 𝒰ⱼ ≠ ∅` since `X` is irreducible, and `q` is
   surjective (`Spec K ⟶ Spec k` is surjective as `Spec k` is a point and `Spec K ≠ ∅`;
   surjectivity is stable under base change).
3. The purely topological gluing lemma `preirreducibleSpace_of_isOpen_cover_pairwise_inter`
   (a space covered by preirreducible opens, any two nonempty ones of which meet, is
   preirreducible) then gives `X_K` preirreducible; it is nonempty because `q` is surjective.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Topological gluing lemma: a space covered by preirreducible open sets, any two nonempty ones of
which intersect, is preirreducible.

Proof: given nonempty opens `s ∋ x`, `t ∋ y`, pick pieces `U i ∋ x`, `U j ∋ y`. `U i ∩ U j` is a
nonempty open subset of the preirreducible `U i`, hence preirreducible. Preirreducibility of `U i`
gives a point of `s ∩ (U i ∩ U j)`, that of `U j` a point of `t ∩ (U i ∩ U j)`, and
preirreducibility of `U i ∩ U j` gives a point of `s ∩ t`. -/
theorem preirreducibleSpace_of_isOpen_cover_pairwise_inter {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    (hirr : ∀ i, IsPreirreducible (U i))
    (hpair : ∀ i j, (U i).Nonempty → (U j).Nonempty → (U i ∩ U j).Nonempty) :
    PreirreducibleSpace X := by
  refine PreirreducibleSpace.of_forall_nonempty_inter ?_
  intro s t hs ht hsne htne
  obtain ⟨x, hxs⟩ := hsne
  obtain ⟨y, hyt⟩ := htne
  obtain ⟨i, hxi⟩ := hcov x
  obtain ⟨j, hyj⟩ := hcov y
  have hij : IsPreirreducible (U i ∩ U j) :=
    (hirr i).open_subset ((hopen i).inter (hopen j)) Set.inter_subset_left
  obtain ⟨z, hzi, hzs, hzj⟩ :=
    hirr i s (U j) hs (hopen j) ⟨x, hxi, hxs⟩ (hpair i j ⟨x, hxi⟩ ⟨y, hyj⟩)
  obtain ⟨w, hwj, hwt, hwi⟩ :=
    hirr j t (U i) ht (hopen i) ⟨y, hyj, hyt⟩ (hpair j i ⟨y, hyj⟩ ⟨x, hxi⟩)
  obtain ⟨v, -, hvs, hvt⟩ := hij s t hs ht ⟨z, ⟨hzi, hzj⟩, hzs⟩ ⟨w, ⟨hwi, hwj⟩, hwt⟩
  exact ⟨v, hvs, hvt⟩

/-- Stacks 020J: an irreducible scheme over a separably closed field `k` stays irreducible after
base change to any field extension `K/k`. Route: see the module docstring. The only unproved
input is Stacks 00I7 (`irreducibleSpace_tensor_of_isSepClosed`). -/
theorem AlgebraicGeometry.irreducibleSpace_pullback_of_isSepClosed {k K : Type u} [Field k] [IsSepClosed k]
    [Field K] [Algebra k K] (X : AlgebraicGeometry.Scheme.{u})
    (p : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [IrreducibleSpace X] :
    IrreducibleSpace (CategoryTheory.Limits.pullback p
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : AlgebraicGeometry.Scheme.{u}) := by
  set g : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)) with hg
  let 𝒰 : X.OpenCover := X.affineOpenCover.openCover
  let 𝒱 : (pullback p g).OpenCover := AlgebraicGeometry.Scheme.Pullback.openCoverOfLeft 𝒰 p g
  -- the first projection `X_K ⟶ X` is surjective
  have : Nonempty (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    (inferInstance : Nonempty (PrimeSpectrum K))
  have : Subsingleton (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (inferInstance : Subsingleton (PrimeSpectrum k))
  have : AlgebraicGeometry.Surjective g := inferInstance
  have hsurj : Function.Surjective (pullback.fst p g) := (pullback.fst p g).surjective
  have hopen : ∀ i : 𝒰.I₀, IsOpen (Set.range (𝒰.f i)) :=
    fun i => (𝒰.f i).isOpenEmbedding.isOpen_range
  -- the range of each piece of the cover of `X_K`
  have hrange : ∀ i, Set.range (𝒱.f i) = pullback.fst p g ⁻¹' Set.range (𝒰.f i) := by
    intro i
    change Set.range (pullback.map (𝒰.f i ≫ p) g p g (𝒰.f i) (𝟙 _) (𝟙 _) (by simp) (by simp)) = _
    rw [AlgebraicGeometry.Scheme.Pullback.range_map]
    simp
  -- each nonempty piece `Spec Rᵢ ×_k Spec K ≅ Spec (Rᵢ ⊗_k K)` is irreducible (Stacks 00I7)
  have hpiece : ∀ i : 𝒰.I₀, Nonempty (pullback (𝒰.f i ≫ p) g : AlgebraicGeometry.Scheme.{u}) →
      IrreducibleSpace (pullback (𝒰.f i ≫ p) g : AlgebraicGeometry.Scheme.{u}) := by
    intro i hne
    have hne' : Nonempty (𝒰.X i) := ⟨pullback.fst (𝒰.f i ≫ p) g hne.some⟩
    have : IrreducibleSpace (𝒰.X i) := (𝒰.f i).isOpenEmbedding.irreducibleSpace
    obtain ⟨φ, hφ⟩ := AlgebraicGeometry.Spec.map_surjective (𝒰.f i ≫ p)
    let _ : Algebra k (X.affineOpenCover.X i) := φ.hom.toAlgebra
    have : IrreducibleSpace (PrimeSpectrum (X.affineOpenCover.X i)) := ‹IrreducibleSpace (𝒰.X i)›
    have hT : IrreducibleSpace (PrimeSpectrum (TensorProduct k (X.affineOpenCover.X i) K)) :=
      irreducibleSpace_tensor_of_isSepClosed
    have hT' : IrreducibleSpace
        (AlgebraicGeometry.Spec (CommRingCat.of (TensorProduct k (X.affineOpenCover.X i) K))) := hT
    have e : (pullback (𝒰.f i ≫ p) g : AlgebraicGeometry.Scheme.{u}) ≅
        AlgebraicGeometry.Spec (CommRingCat.of (TensorProduct k (X.affineOpenCover.X i) K)) := by
      refine (pullback.congrHom (f₁ := 𝒰.f i ≫ p) (f₂ := AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k (X.affineOpenCover.X i)))) (g₁ := g) (g₂ := g)
        ?_ rfl) ≪≫ AlgebraicGeometry.pullbackSpecIso k (X.affineOpenCover.X i) K
      exact hφ.symm
    exact (e.hom.homeomorph.irreducibleSpace_iff).mpr hT'
  have hpre : PreirreducibleSpace (pullback p g : AlgebraicGeometry.Scheme.{u}) := by
    refine preirreducibleSpace_of_isOpen_cover_pairwise_inter (fun i => Set.range (𝒱.f i))
      (fun i => (𝒱.f i).isOpenEmbedding.isOpen_range) (fun z => ⟨𝒱.idx z, 𝒱.covers z⟩) ?_ ?_
    · intro i
      rcases isEmpty_or_nonempty (𝒱.X i) with hE | hne
      · have : Set.range (𝒱.f i) = ∅ := Set.range_eq_empty _
        rw [this]
        exact isPreirreducible_empty
      · have hI : IrreducibleSpace (𝒱.X i) := hpiece i hne
        have := (IrreducibleSpace.isIrreducible_univ (𝒱.X i)).image (𝒱.f i)
          (𝒱.f i).continuous.continuousOn
        rw [Set.image_univ] at this
        exact this.2
    · intro i j hi hj
      rw [hrange, hrange, ← Set.preimage_inter]
      rw [hrange] at hi hj
      have hi' : (Set.range (𝒰.f i)).Nonempty := by
        obtain ⟨z, hz⟩ := hi
        exact ⟨_, hz⟩
      have hj' : (Set.range (𝒰.f j)).Nonempty := by
        obtain ⟨z, hz⟩ := hj
        exact ⟨_, hz⟩
      obtain ⟨x, hx⟩ := nonempty_preirreducible_inter (hopen i) (hopen j) hi' hj'
      obtain ⟨z, hz⟩ := hsurj x
      exact ⟨z, by rw [Set.mem_preimage, hz]; exact hx⟩
  have hne : Nonempty (pullback p g : AlgebraicGeometry.Scheme.{u}) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨z, -⟩ := hsurj x
    exact ⟨z⟩
  exact { toPreirreducibleSpace := hpre, toNonempty := hne }

end
