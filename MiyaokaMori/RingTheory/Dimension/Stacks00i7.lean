import MiyaokaMori.Prelude
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-! # Stacks 00I7: irreducibility of the spectrum after base change of the field

Stacks 00I7: let `k` be separably closed and `R` a `k`-algebra with `Spec R` irreducible. Then for
every field extension `K/k`, `Spec(R ⊗_k K)` is irreducible.

Reference: Stacks 00I7 (needed for Stacks 020J).

Route, all inside this file and Mathlib:
1. mod out the (prime) nilradical of `R` — the tensored quotient map detects nilpotents;
2. reduce a domain `R₀` to its finitely generated `k`-subalgebras (elements of `R₀ ⊗[k] K` involve
   finitely many left factors; flatness over `k` gives injectivity);
3. finite type case via Stacks 00I6/004Z: `Spec (A ⊗[k] K) → Spec A` is open (Stacks 037G,
   `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`), closed points are dense
   (Jacobson, `isJacobsonRing_of_finiteType`), residue fields at closed points are finite over `k`
   (Zariski's lemma 0CY7, `finite_of_finite_type_of_isJacobsonRing`), hence purely inseparable over
   the separably closed `k` (`Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`), and purely
   inseparable base change is a homeomorphism on `Spec` (Stacks 0BRA,
   `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`), so every closed fibre is irreducible
   and `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber` (Stacks 004Z) concludes.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open TensorProduct

noncomputable section

namespace Stacks00i7

section NilradicalTransfer

variable {A B : Type*} [CommRing A] [CommRing B]

/-- If `f : A →+* B` detects nilpotents and the nilradical of `B` is prime, so is that of `A`. -/
theorem isPrime_nilradical_of_ringHom (f : A →+* B) (h : ∀ x, IsNilpotent (f x) → IsNilpotent x)
    (hB : (nilradical B).IsPrime) : (nilradical A).IsPrime := by
  have : nilradical A = (nilradical B).comap f := by
    ext x
    simp only [mem_nilradical, Ideal.mem_comap]
    exact ⟨fun hx ↦ hx.map f, h x⟩
  rw [this]
  exact hB.comap f

/-- A ring map whose kernel consists of nilpotents detects nilpotents. -/
theorem isNilpotent_of_map_of_ker_le_nilradical (f : A →+* B)
    (hker : RingHom.ker f ≤ nilradical A) (x : A) (hx : IsNilpotent (f x)) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hx
  have hmem : x ^ n ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_pow]; exact hn
  obtain ⟨m, hm⟩ := mem_nilradical.mp (hker hmem)
  exact ⟨n * m, by rw [pow_mul]; exact hm⟩

end NilradicalTransfer

section PurelyInseparableFibre

variable {k L K : Type*} [Field k] [Field L] [Algebra k L] [Field K] [Algebra k K]

/-- Stacks 0BRA/0BR8: for `L/k` purely inseparable and `K/k` any field, `Spec (L ⊗[k] K)` is
homeomorphic to `Spec K`, hence irreducible. -/
theorem irreducibleSpace_tensor_of_isPurelyInseparable [IsPurelyInseparable k L] :
    IrreducibleSpace (PrimeSpectrum (L ⊗[k] K)) := by
  have h1 : IsHomeomorph (PrimeSpectrum.comap (algebraMap K (K ⊗[k] L))) :=
    PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k L K
  have h2 : IsHomeomorph (PrimeSpectrum.comap
      (Algebra.TensorProduct.comm k K L : K ⊗[k] L ≃ₐ[k] L ⊗[k] K).toRingEquiv.toRingHom) :=
    PrimeSpectrum.isHomeomorph_comap_of_bijective (Algebra.TensorProduct.comm k K L).bijective
  rw [(IsHomeomorph.homeomorph _ h2).irreducibleSpace_iff,
    (IsHomeomorph.homeomorph _ h1).irreducibleSpace_iff]
  infer_instance

end PurelyInseparableFibre

section FiniteTypeCore

variable {k A K : Type*} [Field k] [CommRing A] [Algebra k A] [Field K] [Algebra k K]

/-- The fibre of `Spec (A ⊗[k] K) → Spec A` over a maximal ideal `m` is the image of
`Spec ((A ⧸ m) ⊗[k] K)`. -/
theorem range_comap_map_quotient_eq_fiber (x : PrimeSpectrum A) (hx : x.asIdeal.IsMaximal) :
    Set.range (PrimeSpectrum.comap
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k x.asIdeal) (AlgHom.id k K)).toRingHom) =
      PrimeSpectrum.comap (algebraMap A (A ⊗[k] K)) ⁻¹' {x} := by
  rw [range_comap_of_surjective _ _
    (Algebra.TensorProduct.map_surjective _ _ Ideal.Quotient.mk_surjective Function.surjective_id),
    AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom,
    Algebra.TensorProduct.map_ker _ _ Ideal.Quotient.mk_surjective Function.surjective_id]
  ext q
  simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_preimage, Set.mem_singleton_iff,
    SetLike.coe_subset_coe, sup_le_iff, Ideal.map_le_iff_le_comap]
  have hid : RingHom.ker (AlgHom.id k K) = ⊥ := by
    ext y; simp [RingHom.mem_ker]
  have hmk : RingHom.ker (Ideal.Quotient.mkₐ k x.asIdeal) = x.asIdeal := by
    ext y; simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  rw [hid, hmk]
  simp only [bot_le, and_true]
  constructor
  · intro h
    ext1
    exact (hx.eq_of_le (Ideal.comap_isPrime _ q.asIdeal).ne_top h).symm
  · intro h
    rw [← h]
    intro y hy
    exact hy

variable [IsSepClosed k] [IsDomain A] [Algebra.FiniteType k A]

/-- Stacks 00I7, finite type case: `k` separably closed, `A` a domain of finite type over `k`,
`K/k` a field; then `Spec (A ⊗[k] K)` is irreducible.  Route (Stacks 00I6 / 004Z): the projection
`Spec (A ⊗[k] K) → Spec A` is open (Stacks 037G), `Spec A` is irreducible, closed points of
`Spec A` are dense (Jacobson), and the fibre over a closed point `m` is the image of
`Spec ((A ⧸ m) ⊗[k] K)`, which is irreducible because `A ⧸ m` is finite (Zariski's lemma, 0CY7),
hence purely inseparable over the separably closed `k`. -/
theorem irreducibleSpace_tensor_of_finiteType : IrreducibleSpace (PrimeSpectrum (A ⊗[k] K)) := by
  let π : PrimeSpectrum (A ⊗[k] K) → PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A (A ⊗[k] K))
  have hπ : IsOpenMap π := PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hfib : ∀ x : PrimeSpectrum A, IsClosed ({x} : Set (PrimeSpectrum A)) →
      IsPreirreducible (π ⁻¹' {x}) := by
    intro x hx
    have hm : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx
    let _ : Field (A ⧸ x.asIdeal) := Ideal.Quotient.field x.asIdeal
    have : Algebra.FiniteType k (A ⧸ x.asIdeal) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k x.asIdeal) Ideal.Quotient.mk_surjective
    have : Module.Finite k (A ⧸ x.asIdeal) := finite_of_finite_type_of_isJacobsonRing k _
    have hL : IrreducibleSpace (PrimeSpectrum ((A ⧸ x.asIdeal) ⊗[k] K)) :=
      irreducibleSpace_tensor_of_isPurelyInseparable
    rw [← range_comap_map_quotient_eq_fiber (K := K) x hm, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.image _
      (PrimeSpectrum.continuous_comap _).continuousOn
  have hV : IsPreirreducible (Set.univ : Set (PrimeSpectrum A)) :=
    PreirreducibleSpace.isPreirreducible_univ
  have hdense : Set.univ ⊆ closure (Set.univ ∩ {x | IsPreirreducible (π ⁻¹' {x})}) := by
    rw [Set.univ_inter, ← closure_closedPoints (X := PrimeSpectrum A)]
    exact closure_mono fun x hx ↦ hfib x hx
  have hpre := hV.preimage_of_dense_isPreirreducible_fiber π hπ hdense
  rw [Set.preimage_univ] at hpre
  have : Nontrivial (A ⊗[k] K) := inferInstance
  exact { isPreirreducible_univ := hpre, toNonempty := inferInstance }

end FiniteTypeCore

section FiniteGeneratedReduction

variable {k R K : Type*} [Field k] [CommRing R] [Algebra k R] [CommRing K] [Algebra k K]

/-- The canonical map `A ⊗[k] K → R ⊗[k] K` for a `k`-subalgebra `A ≤ R`. -/
abbrev subalgebraTensorMap (A : Subalgebra k R) : A ⊗[k] K →ₐ[k] R ⊗[k] K :=
  Algebra.TensorProduct.map A.val (AlgHom.id k K)

theorem subalgebraTensorMap_injective (A : Subalgebra k R) :
    Function.Injective (subalgebraTensorMap (K := K) A) := by
  have h : ⇑(subalgebraTensorMap (K := K) A) =
      ⇑(TensorProduct.map A.val.toLinearMap (AlgHom.id k K).toLinearMap) := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [subalgebraTensorMap]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h]
  exact TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Function.injective_id

/-- A finite sum of pure tensors whose left factors lie in a finset `s` comes from
`(adjoin k s) ⊗[k] K`. -/
theorem sum_tmul_mem_range_subalgebraTensorMap (S : Finset (R × K)) (s : Finset R)
    (hS : ∀ i ∈ S, i.1 ∈ s) :
    (∑ i ∈ S, i.1 ⊗ₜ[k] i.2) ∈
      Set.range (subalgebraTensorMap (K := K) (Algebra.adjoin k (s : Set R))) := by
  refine ⟨∑ i ∈ S.attach, (⟨i.1.1, Algebra.subset_adjoin (hS i.1 i.2)⟩ :
      Algebra.adjoin k (s : Set R)) ⊗ₜ[k] i.1.2, ?_⟩
  rw [map_sum, ← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [subalgebraTensorMap]

/-- Any two elements of `R ⊗[k] K` come from `A ⊗[k] K` for a common finitely generated
`k`-subalgebra `A = adjoin k s`, `s` finite (Stacks 00I3-style limit argument, elementary form). -/
theorem exists_finset_mem_range_subalgebraTensorMap (x y : R ⊗[k] K) :
    ∃ s : Finset R,
      x ∈ Set.range (subalgebraTensorMap (K := K) (Algebra.adjoin k (s : Set R))) ∧
      y ∈ Set.range (subalgebraTensorMap (K := K) (Algebra.adjoin k (s : Set R))) := by
  classical
  obtain ⟨Sx, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨Sy, rfl⟩ := TensorProduct.exists_finset y
  refine ⟨(Sx ∪ Sy).image Prod.fst, ?_, ?_⟩
  · exact sum_tmul_mem_range_subalgebraTensorMap _ _ fun i hi ↦
      Finset.mem_image_of_mem _ (Finset.mem_union_left _ hi)
  · exact sum_tmul_mem_range_subalgebraTensorMap _ _ fun i hi ↦
      Finset.mem_image_of_mem _ (Finset.mem_union_right _ hi)

end FiniteGeneratedReduction

section DomainCase

variable {k R K : Type*} [Field k] [IsSepClosed k] [CommRing R] [IsDomain R] [Algebra k R]
  [Field K] [Algebra k K]

/-- Stacks 00I7 for a domain `R`: `k` separably closed, `R` a `k`-domain, `K/k` a field; then the
nilradical of `R ⊗[k] K` is prime. Reduction to the finite type case
`irreducibleSpace_tensor_of_finiteType` via `exists_finset_mem_range_subalgebraTensorMap`. -/
theorem isPrime_nilradical_tensor_of_isDomain : (nilradical (R ⊗[k] K)).IsPrime := by
  have key : ∀ s : Finset R,
      (nilradical ((Algebra.adjoin k (s : Set R)) ⊗[k] K)).IsPrime := fun s ↦ by
    have : Algebra.FiniteType k (Algebra.adjoin k (s : Set R)) :=
      Algebra.FiniteType.adjoin_of_finite s.finite_toSet
    exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp
      irreducibleSpace_tensor_of_finiteType
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_nilradical]
    intro h1
    obtain ⟨s, ⟨x', hx'⟩, -⟩ := exists_finset_mem_range_subalgebraTensorMap (K := K) (1 : R ⊗[k] K) 1
    have hinj := subalgebraTensorMap_injective (K := K) (Algebra.adjoin k (s : Set R))
    have h1' : IsNilpotent (subalgebraTensorMap (K := K) (Algebra.adjoin k (s : Set R)) 1) := by
      rw [map_one]; exact h1
    exact (key s).ne_top (Ideal.eq_top_iff_one _ |>.mpr (mem_nilradical.mpr
      ((IsNilpotent.map_iff hinj).mp h1')))
  · intro x y hxy
    obtain ⟨s, ⟨x', rfl⟩, ⟨y', rfl⟩⟩ := exists_finset_mem_range_subalgebraTensorMap (K := K) x y
    have hinj := subalgebraTensorMap_injective (K := K) (Algebra.adjoin k (s : Set R))
    rw [← map_mul, mem_nilradical, IsNilpotent.map_iff hinj, ← mem_nilradical] at hxy
    rcases (key s).mem_or_mem hxy with h | h
    · exact Or.inl (mem_nilradical.mpr ((mem_nilradical.mp h).map _))
    · exact Or.inr (mem_nilradical.mpr ((mem_nilradical.mp h).map _))

end DomainCase

end Stacks00i7

open Stacks00i7 in
/-- **Stacks 00I7** (Algebra, Lemma `lemma-separably-closed-irreducible`): let `k` be a separably
closed field, `R` a `k`-algebra with `Spec R` irreducible, and `K/k` any field extension. Then
`Spec (R ⊗[k] K)` is irreducible.

Proof (all steps formalized in this file, no external input):
1. `Spec R` irreducible means `nilradical R` is prime (`irreducibleSpace_iff_isPrime_nilradical`);
   `R₀ := R ⧸ nilradical R` is a domain, and `R ⊗[k] K → R₀ ⊗[k] K` is surjective with kernel
   generated by nilpotents (`Algebra.TensorProduct.map_ker`), so it detects nilpotents and
   primality of the nilradical passes from `R₀ ⊗[k] K` to `R ⊗[k] K`
   (`isPrime_nilradical_of_ringHom`).
2. For a domain `R₀`, any two elements of `R₀ ⊗[k] K` lie in `A ⊗[k] K ⊆ R₀ ⊗[k] K` for a finitely
   generated subalgebra `A` (flatness over `k` gives injectivity), reducing to `A` of finite type
   (`isPrime_nilradical_tensor_of_isDomain`).
3. Finite type case (Stacks 00I6 / 004Z / 037G / 0CY7 / 0BRA): the open map
   `Spec (A ⊗[k] K) → Spec A` has irreducible fibres over the dense set of closed points, since
   the residue field at a closed point is finite, hence purely inseparable, over `k`, and purely
   inseparable base change is a homeomorphism on `Spec` (`irreducibleSpace_tensor_of_finiteType`). -/
theorem irreducibleSpace_tensor_of_isSepClosed {k R K : Type u} [Field k] [IsSepClosed k] [CommRing R]
    [Algebra k R] [Field K] [Algebra k K] [IrreducibleSpace (PrimeSpectrum R)] :
    IrreducibleSpace (PrimeSpectrum (TensorProduct k R K)) := by
  have hnil : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp ‹_›
  let f : R ⊗[k] K →ₐ[k] (R ⧸ nilradical R) ⊗[k] K :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (nilradical R)) (AlgHom.id k K)
  have hker : RingHom.ker f ≤ nilradical (R ⊗[k] K) := by
    rw [Algebra.TensorProduct.map_ker _ _ Ideal.Quotient.mk_surjective Function.surjective_id]
    have hid : RingHom.ker (AlgHom.id k K) = ⊥ := by
      ext y; simp [RingHom.mem_ker]
    have hmk : RingHom.ker (Ideal.Quotient.mkₐ k (nilradical R)) = nilradical R := by
      ext y; simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hid, hmk, Ideal.map_bot, sup_bot_eq, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_nilradical]
    exact (mem_nilradical.mp hx).map _
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  exact isPrime_nilradical_of_ringHom f.toRingHom
    (isNilpotent_of_map_of_ker_le_nilradical f.toRingHom hker) isPrime_nilradical_tensor_of_isDomain

end
