import MiyaokaMori.Prelude

/-! # Relative length of submodules and finiteness for lattices

Let `A` be a commutative ring, `V` an `A`-module, `M`, `N` submodules of `V`. Define the relative length
`relLength M N := length_A(M/(N∩M))` (for `N ≤ M` this is `length_A(M/N)`).
(1) Additivity along chains: for `P ≤ N ≤ M`, `relLength M P = relLength M N + relLength N P`;
(2) an `A`-linear injection `φ` preserves relative length: `relLength (φM) (φN) = relLength M N`;
(3) if `A` is a Noetherian domain of Krull dimension `≤ 1`, `K = Frac A`, `V` a `K`-vector space, `M`, `N`
    lattices in `V` (finitely generated and spanning `V` over `K`, Mathlib `Submodule.IsLattice`), `N ≤ M`,
    then `relLength M N < ⊤` (Stacks 02MF(1)(2)).

Proof:
1. (1): the short exact sequence `0 → N/P → M/P → M/N → 0` (the first map induced by the inclusion `N ⊆ M`,
   the second is `Submodule.factor`), and Mathlib `Module.length_eq_add_of_exact`.
2. (2): `φ` restricts to an `A`-linear isomorphism `M ≃ φM` matching `N∩M` with `φN∩φM`;
   `Submodule.Quotient.equiv` gives the isomorphism of quotients, `LinearEquiv.length_eq`.
3. (3): `M` is finitely generated, with generators `m_1..m_r`; `N` spans `V`, so every `m_i` is a `K`-linear
   combination of elements of `N`; clearing denominators gives a nonzero `a ∈ A` with `a·m_i ∈ N` for all `i`
   (`IsLocalization.exist_integer_multiples`), i.e. `aM ⊆ N`. Then `M/N` is a quotient of `M/aM`; `M/aM` is a
   finitely generated `A/(a)`-module; `A/(a)` has finite length as an `A`-module (Mathlib
   `isFiniteLength_quotient_span_singleton`, using `A` Noetherian, dimension `≤ 1`, `a` a nonzerodivisor), so
   `(A/(a))^r` has finite length, and so do its quotients `M/aM`, `M/N`.

References: Stacks 02ME, 02MF (algebra-lemma-lattice-finite-length).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

noncomputable section

namespace Submodule

section General

variable {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]

/-- The relative length `length_A (M / (N ∩ M))`; for `N ≤ M` this is `length_A (M/N)`. -/
def relLength (M N : Submodule A V) : ℕ∞ :=
  Module.length A (↥M ⧸ N.submoduleOf M)

lemma relLength_self (M : Submodule A V) : relLength M M = 0 := by
  unfold relLength
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]
  exact eq_top_iff.mpr fun x _ => x.2

/-- Additivity along chains. -/
theorem relLength_add {M N P : Submodule A V} (hNM : N ≤ M) (hPN : P ≤ N) :
    relLength M P = relLength M N + relLength N P := by
  unfold relLength
  let f : (↥N ⧸ P.submoduleOf N) →ₗ[A] (↥M ⧸ P.submoduleOf M) :=
    Submodule.mapQ (P.submoduleOf N) (P.submoduleOf M) (Submodule.inclusion hNM)
      (fun x hx => hx)
  have hle : P.submoduleOf M ≤ N.submoduleOf M := fun x hx => hPN hx
  let g : (↥M ⧸ P.submoduleOf M) →ₗ[A] (↥M ⧸ N.submoduleOf M) := Submodule.factor hle
  have hfmk : ∀ x : ↥N, f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion hNM x) := fun _ => rfl
  have hgmk : ∀ y : ↥M, g (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := fun _ => rfl
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [hfmk, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx
  have hg : Function.Surjective g := Submodule.factor_surjective hle
  have hex : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        rw [hgmk, Submodule.Quotient.mk_eq_zero] at hy
        exact ⟨Submodule.Quotient.mk ⟨(y : V), hy⟩, by rw [hfmk]; rfl⟩
    · rintro ⟨x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [hfmk, hgmk, Submodule.Quotient.mk_eq_zero]
        exact x.2
  rw [Module.length_eq_add_of_exact f g hf hg hex, add_comm]

/-- Injective linear maps preserve relative length. -/
theorem relLength_map {W : Type*} [AddCommGroup W] [Module A W] (φ : V →ₗ[A] W)
    (hφ : Function.Injective φ) (M N : Submodule A V) :
    relLength (M.map φ) (N.map φ) = relLength M N := by
  unfold relLength
  symm
  refine (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective φ hφ M) ?_).length_eq
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, Subtype.exists]
  constructor
  · rintro ⟨x, hxM, hxN, hxy⟩
    have : φ x = y := congrArg Subtype.val hxy
    exact ⟨x, hxN, this⟩
  · rintro ⟨x, hxN, rfl⟩
    obtain ⟨x', hx'M, hx'⟩ := hy
    have : x' = x := hφ hx'
    subst this
    exact ⟨x', hx'M, hxN, rfl⟩

lemma relLength_mono_right {M N P : Submodule A V} (hNM : N ≤ M) (hPN : P ≤ N) :
    relLength M N ≤ relLength M P := by
  rw [relLength_add hNM hPN]; exact le_self_add

end General

section Lattice

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {V : Type*} [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem IsLattice.exists_smul_mem (N : Submodule A V) [IsLattice K N] (v : V) :
    ∃ a : A, a ≠ 0 ∧ a • v ∈ N := by
  have hv : v ∈ span K (N : Set V) := by rw [IsLattice.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem b hax
    · rw [mul_smul]; exact N.smul_mem a hby
  | smul k x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    have hd0 : algebraMap A K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero hd)
    refine ⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero hd) ha, ?_⟩
    have : (d * a) • ((algebraMap A K c / algebraMap A K d) • x) = c • (a • x) := by
      rw [← algebraMap_smul K (d * a), ← algebraMap_smul K c, ← algebraMap_smul K a, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact N.smul_mem c hax

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- Between two lattices there is a nonzero `a ∈ A` with `a • M ≤ N`. -/
theorem IsLattice.exists_smul_le (M N : Submodule A V) [IsLattice K M] [IsLattice K N] :
    ∃ a : A, a ≠ 0 ∧ ∀ m ∈ M, a • m ∈ N := by
  obtain ⟨s, hs⟩ := IsLattice.fg (A := K) (M := M)
  have key : ∀ t : Finset V, ∃ a : A, a ≠ 0 ∧ ∀ m ∈ t, a • m ∈ N := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert x t _ ih =>
      obtain ⟨a, ha, hat⟩ := ih
      obtain ⟨b, hb, hbx⟩ := IsLattice.exists_smul_mem (K := K) N x
      refine ⟨a * b, mul_ne_zero ha hb, fun m hm => ?_⟩
      rcases Finset.mem_insert.mp hm with rfl | hm
      · rw [mul_smul]; exact N.smul_mem a hbx
      · rw [mul_comm, mul_smul]; exact N.smul_mem b (hat m hm)
  obtain ⟨a, ha, has⟩ := key s
  refine ⟨a, ha, fun m hm => ?_⟩
  rw [← hs] at hm
  induction hm using Submodule.span_induction with
  | mem x hx => exact has x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact N.smul_mem c hx

/-- The relative length between two lattices is finite (Stacks 02MF). -/
theorem IsLattice.relLength_ne_top (M N : Submodule A V) [IsLattice K M] [IsLattice K N] :
    relLength M N ≠ ⊤ := by
  obtain ⟨a, ha, haM⟩ := IsLattice.exists_smul_le (K := K) M N
  unfold relLength
  set Q := ↥M ⧸ N.submoduleOf M
  have htors : Module.IsTorsionBySet A Q (Ideal.span {a} : Ideal A) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact haM m m.2
  let _ := htors.module
  have hfl : IsFiniteLength A (A ⧸ Ideal.span {a}) :=
    isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  have : IsArtinianRing (A ⧸ Ideal.span {a}) := isArtinian_of_tower A hfl.2
  have : Module.Finite A Q := inferInstance
  have : Module.Finite (A ⧸ Ideal.span {a}) Q := Module.Finite.of_restrictScalars_finite A _ Q
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ Ideal.span {a}) (M := Q)
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end Lattice

end Submodule

end
