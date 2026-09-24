import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.OrderOfVanishing.LatticeRelLength

/-! # The distance between two lattices (Stacks 02MG–02MH)

Let `A` be a Noetherian domain of Krull dimension `≤ 1`, `K = Frac A`, `V` a `K`-vector space. For two
lattices `M`, `M′` in `V` define the distance `d(M, M′) := length_A(M/M∩M′) − length_A(M′/M∩M′) ∈ ℤ`
(Stacks 02MG). Then
(1) `M∩M′` is again a lattice; for every lattice `N ⊆ M∩M′`, `d(M, M′) = length(M/N) − length(M′/N)`;
(2) `d(M, M″) = d(M, M′) + d(M′, M″)` (Stacks 02MH), `d(M, M) = 0`, `d(M, M′) = −d(M′, M)`; for `N ⊆ M`,
    `d(M, N) = length(M/N)`;
(3) a `K`-linear injection `φ : V → W` sends lattices to lattices (of the span of the image) and
    `d(φM, φM′) = d(M, M′)`;
(4) for a `K`-linear bijection `φ : V → V`, `e(φ) := d(M, φM)` does not depend on the lattice `M`, and
    `e(φ∘ψ) = e(φ) + e(ψ)` (first paragraph of the proof of Stacks 02MI).

Proof:
1. `M∩M′` is finitely generated since `A` is Noetherian; it spans: for `v ∈ V` there are nonzero `a`, `b` with
   `av ∈ M`, `bv ∈ M′` (the common-denominator lemma of `LatticeRelLength`), so `abv ∈ M∩M′`.
2. (1): by additivity along chains, `length(M/N) = length(M/M∩M′) + length(M∩M′/N)`, likewise for `M′`;
   subtract; all terms are finite (`LatticeRelLength` (3)), so the subtraction is in `ℤ`.
3. (2): take `N = M∩M′∩M″`, write the three distances via (1) as differences of `length(−/N)` and add.
4. (3): `φ` is injective, so `φ(M∩M′) = φM∩φM′`, and `relLength` is invariant under injections
   (`LatticeRelLength` (2)).
5. (4): `d(M, φM) = d(M, M′) + d(M′, φM′) + d(φM′, φM)`, and by (3) `d(φM′, φM) = d(M′, M) = −d(M, M′)`.
   `d(M, φψM) = d(M, φM) + d(φM, φψM) = d(M, φM) + d(M, ψM)`.

References: Stacks 02MG, 02MH, 02MI (first paragraph of the proof of algebra-lemma-order-vanishing-determinant).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

noncomputable section

namespace Submodule

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {V : Type*} [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
variable {W : Type*} [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]

omit [Ring.KrullDimLE 1 A] in
/-- The intersection of two lattices over a Noetherian domain is a lattice. -/
theorem IsLattice.inf' (M N : Submodule A V) [IsLattice K M] [IsLattice K N] :
    IsLattice K (M ⊓ N) where
  fg := by
    have : IsNoetherian A ↥(M ⊓ N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨a, ha, hav⟩ := IsLattice.exists_smul_mem (K := K) M v
    obtain ⟨b, hb, hbv⟩ := IsLattice.exists_smul_mem (K := K) N v
    have hab : algebraMap A K (a * b) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (mul_ne_zero ha hb)
    have hmem : (a * b) • v ∈ M ⊓ N := by
      refine ⟨?_, ?_⟩
      · rw [mul_comm, mul_smul]; exact M.smul_mem b hav
      · rw [mul_smul]; exact N.smul_mem a hbv
    have : v = (algebraMap A K (a * b))⁻¹ • ((a * b) • v) := by
      rw [← algebraMap_smul K (a * b) v, smul_smul, inv_mul_cancel₀ hab, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsDomain A] [IsFractionRing A K] in
/-- A `K`-linear surjection sends lattices to lattices. -/
theorem IsLattice.map' (φ : V →ₗ[K] W) (hφ : Function.Surjective φ) (M : Submodule A V)
    [IsLattice K M] : IsLattice K (M.map (φ.restrictScalars A)) where
  fg := (IsLattice.fg (A := K) (M := M)).map _
  span_eq_top := by
    have h : ((M.map (φ.restrictScalars A) : Submodule A W) : Set W) = φ '' (M : Set V) := rfl
    rw [h, Submodule.span_image, IsLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr hφ]

/-- The distance between lattices (Stacks 02MG). -/
def latDist (M M' : Submodule A V) : ℤ :=
  ((relLength M (M ⊓ M')).toNat : ℤ) - ((relLength M' (M ⊓ M')).toNat : ℤ)

/-- Computing the distance via any common sublattice. -/
theorem latDist_eq_of_le (M M' N : Submodule A V) [IsLattice K M] [IsLattice K M']
    [IsLattice K N] (h : N ≤ M) (h' : N ≤ M') :
    latDist M M' = ((relLength M N).toNat : ℤ) - ((relLength M' N).toNat : ℤ) := by
  have : IsLattice K (M ⊓ M') := IsLattice.inf' M M'
  have hN : N ≤ M ⊓ M' := le_inf h h'
  unfold latDist
  rw [relLength_add (inf_le_left : M ⊓ M' ≤ M) hN, relLength_add (inf_le_right : M ⊓ M' ≤ M') hN,
    ENat.toNat_add (IsLattice.relLength_ne_top (K := K) _ _)
      (IsLattice.relLength_ne_top (K := K) _ _),
    ENat.toNat_add (IsLattice.relLength_ne_top (K := K) _ _)
      (IsLattice.relLength_ne_top (K := K) _ _)]
  push_cast
  ring

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem latDist_self (M : Submodule A V) : latDist M M = 0 := by
  simp [latDist]

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem latDist_comm (M M' : Submodule A V) : latDist M M' = - latDist M' M := by
  unfold latDist
  rw [inf_comm]
  ring

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem latDist_of_le {M N : Submodule A V} (h : N ≤ M) :
    latDist M N = ((relLength M N).toNat : ℤ) := by
  unfold latDist
  rw [inf_eq_right.mpr h, relLength_self]
  simp

/-- The triangle identity (Stacks 02MH). -/
theorem latDist_triangle (M M' M'' : Submodule A V) [IsLattice K M] [IsLattice K M']
    [IsLattice K M''] : latDist M M'' = latDist M M' + latDist M' M'' := by
  have h1 : IsLattice K (M ⊓ M') := IsLattice.inf' M M'
  have h2 : IsLattice K (M ⊓ M' ⊓ M'') := IsLattice.inf' (M ⊓ M') M''
  have hM : M ⊓ M' ⊓ M'' ≤ M := inf_le_left.trans inf_le_left
  have hM' : M ⊓ M' ⊓ M'' ≤ M' := inf_le_left.trans inf_le_right
  have hM'' : M ⊓ M' ⊓ M'' ≤ M'' := inf_le_right
  rw [latDist_eq_of_le (K := K) M M'' _ hM hM'', latDist_eq_of_le (K := K) M M' _ hM hM',
    latDist_eq_of_le (K := K) M' M'' _ hM' hM'']
  ring

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsFractionRing A K] in
/-- `K`-linear injections preserve the distance. -/
theorem latDist_map (φ : V →ₗ[K] W) (hφ : Function.Injective φ) (M M' : Submodule A V) :
    latDist (M.map (φ.restrictScalars A)) (M'.map (φ.restrictScalars A)) = latDist M M' := by
  unfold latDist
  have hφ' : Function.Injective (φ.restrictScalars A) := hφ
  rw [← Submodule.map_inf _ hφ', relLength_map _ hφ', relLength_map _ hφ']

/-- `e(φ) = d(M, φM)` does not depend on the lattice (first paragraph of the proof of Stacks 02MI). -/
theorem latDist_map_indep (φ : V →ₗ[K] V) (hφ : Function.Bijective φ) (M M' : Submodule A V)
    [IsLattice K M] [IsLattice K M'] :
    latDist M (M.map (φ.restrictScalars A)) = latDist M' (M'.map (φ.restrictScalars A)) := by
  have h1 : IsLattice K (M.map (φ.restrictScalars A)) := IsLattice.map' φ hφ.2 M
  have h2 : IsLattice K (M'.map (φ.restrictScalars A)) := IsLattice.map' φ hφ.2 M'
  rw [latDist_triangle (K := K) M M' (M.map (φ.restrictScalars A)),
    latDist_triangle (K := K) M' (M'.map (φ.restrictScalars A)) (M.map (φ.restrictScalars A)),
    latDist_map φ hφ.1 M' M, latDist_comm M' M]
  ring

/-- `e(φ∘ψ) = e(φ) + e(ψ)`. -/
theorem latDist_map_comp (φ ψ : V →ₗ[K] V) (hφ : Function.Bijective φ)
    (hψ : Function.Bijective ψ) (M : Submodule A V) [IsLattice K M] :
    latDist M (M.map ((φ ∘ₗ ψ).restrictScalars A)) =
      latDist M (M.map (φ.restrictScalars A)) + latDist M (M.map (ψ.restrictScalars A)) := by
  have h1 : IsLattice K (M.map (φ.restrictScalars A)) := IsLattice.map' φ hφ.2 M
  have h2 : IsLattice K (M.map (ψ.restrictScalars A)) := IsLattice.map' ψ hψ.2 M
  have h3 : IsLattice K (M.map ((φ ∘ₗ ψ).restrictScalars A)) :=
    IsLattice.map' (φ ∘ₗ ψ) (hφ.2.comp hψ.2) M
  have hcomp : M.map ((φ ∘ₗ ψ).restrictScalars A) =
      (M.map (ψ.restrictScalars A)).map (φ.restrictScalars A) := by
    rw [← Submodule.map_comp]; rfl
  rw [latDist_triangle (K := K) M (M.map (φ.restrictScalars A)) _, hcomp,
    latDist_map φ hφ.1 M (M.map (ψ.restrictScalars A))]

end Submodule

end
