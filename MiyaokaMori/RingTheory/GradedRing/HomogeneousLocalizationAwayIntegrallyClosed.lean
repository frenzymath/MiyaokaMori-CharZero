import MiyaokaMori.Prelude

/-! # The degree-zero homogeneous localization of an integrally closed graded domain

If `A` is an `ℕ`-graded integrally closed domain and `f` is homogeneous of degree `d > 0` with
`f ≠ 0`, then `HomogeneousLocalization.Away 𝒜 f` (written `A_(f)`) is integrally closed.

There is no single literature tag for this statement (Stacks has no separate entry for
"`R` normal ⇒ `R_(f)` normal"; EGA II 2.1 / Hartshorne II.2 only give the construction of `R_(f)`);
the self-contained proof is given below, including the edge cases (powers of `f` being zero,
non-homogeneous numerators, the zero ring).

## Proof

Write `B := A_(f)` (elements of `Away 𝒜 f` have the form `a/f^p` with `a ∈ 𝒜 (p*d)`), `L := A_f`
(the localization at the powers of `f`), `K := Frac A`. `A` a domain and `f ≠ 0` ⇒ `L` is a domain,
`B ⊆ L ⊆ K`, and both `L` and `K` are localizations of `A` at submonoids of `A⁰`, so `K` is also the
fraction field of `L`.

Let `α ∈ Frac B` be integral over `B`. Lift `Frac B` along `B ↪ K` to `Frac B ↪ K`
(`IsFractionRing.liftAlgHom`, `B → K` injective) and regard `α ∈ K`.

1. **`α ∈ L`**: `α` integral over `B` ⇒ integral over `L` (`B ⊆ L`, `IsIntegral.tower_top`). `A` is an
   integrally closed domain and `Submonoid.powers f ≤ A⁰` ⇒ `L` is integrally closed (Mathlib
   `isIntegrallyClosed_of_isLocalization`), and `K` is the fraction field of `L`, so `α ∈ L`:
   `α = r / f^n` for some `r ∈ A`, `n ∈ ℕ`.
2. **Fraction form of `α`**: `α = a / b` with `a b : B`, `b ≠ 0` (`IsFractionRing.div_surjective`).
   `a = a'/f^q`, `b = b'/f^p` with `a' ∈ 𝒜 (q*d)`, `b' ∈ 𝒜 (p*d)` (the shape of elements of `Away`:
   `num` and `den` have the same degree, `den` is a power of `f`, and `f^p ≠ 0` forces `deg = p*d`).
   `b ≠ 0` ⇒ `b' ≠ 0`.
3. **Clear denominators**: `b * α = a` holds in `K`; substituting, `(b'/f^p)(r/f^n) = a'/f^q`; since
   `A` is a domain and `f ≠ 0`, this simplifies in `A` to **`b' * r * f^q = a' * f^(n+p)`**.
4. **Determine the degree**: the right-hand side is homogeneous of degree `N := q*d + (n+p)*d`;
   `h := b' * f^q` is homogeneous nonzero of degree `M := p*d + q*d`. By
   `homogeneous_of_mul_homogeneous` below (in a graded domain, `h` homogeneous nonzero and `h*r`
   homogeneous ⇒ `r` homogeneous), `r ∈ 𝒜 (N - M) = 𝒜 (n*d)`.
5. **Conclude**: `r ∈ 𝒜 (n*d)` and `f^n ∈ 𝒜 (n*d)`, so `r/f^n` is an element of `B` whose image in `K`
   is `α`; `Frac B ↪ K` is injective, so `α` lies in the image of `B`. ∎

Edge cases: for `n = 0`, `α = r ∈ 𝒜 0` and the argument is unchanged; likewise for `p = q = 0`
(`a b ∈ 𝒜 0`); the zero ring is excluded by `IsDomain A`; the powers of `f` are nonzero by
`IsDomain A` and `f ≠ 0`; `d > 0` is used only in "`f^p ∈ 𝒜 (p*d)` and `f^p ∈ 𝒜 deg` ⇒ `deg = p*d`",
where the graded components meet only in `0` — in fact `d > 0` is not necessary (for `d = 0`, `B` is
the degree-zero part of `A_f` and the argument goes through); it is kept to match the call sites.

## Formalization

The Lean proof follows steps 1–5 with ambient field `Frac L` (`L := A_f`) instead of `Frac A`: the
`Localization` instances give `Algebra B (Frac L)` and `IsScalarTower B L (Frac L)` automatically,
`Frac B → Frac L` is `IsFractionRing.lift` (`B → Frac L` injective), `L` is integrally closed by
Mathlib's `isIntegrallyClosed_of_isLocalization`, and the fraction equations in `Frac L` descend to `A`
via `IsFractionRing.injective`, `IsLocalization.mk'_eq_iff_eq`, `IsLocalization.injective`, followed by
`homogeneous_of_mul_homogeneous`. Do not add a local `Algebra B` instance on `Frac L`: it would form a
diamond with the `Localization` instances.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

open DirectSum

/-- "Cancelling a homogeneous factor" in a graded domain: `h` homogeneous nonzero and `h * r`
homogeneous ⇒ `r` is homogeneous (of the difference of the degrees).

Proof: for every `e`, the component of degree `M + e` of `h * r` equals `h * r_e`
(`DirectSum.coe_decompose_mul_add_of_left_mem`); `h * r ∈ 𝒜 N` forces this component to vanish
whenever `M + e ≠ N`; `A` is a domain and `h ≠ 0`, so `r_e = 0`. Hence the decomposition of `r` has
only the term of degree `N - M`, i.e. `r ∈ 𝒜 (N - M)`. -/
theorem homogeneous_of_mul_homogeneous {R A : Type u} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {M N : ℕ} {h r : A}
    (hh : h ∈ 𝒜 M) (hh0 : h ≠ 0) (hmul : h * r ∈ 𝒜 N) (hMN : M ≤ N) :
    r ∈ 𝒜 (N - M) := by
  classical
  have key : ∀ e : ℕ, e ≠ N - M → ((DirectSum.decompose 𝒜 r e : 𝒜 e) : A) = 0 := by
    intro e he
    have h1 : ((DirectSum.decompose 𝒜 (h * r) (M + e) : 𝒜 (M + e)) : A)
        = h * ((DirectSum.decompose 𝒜 r e : 𝒜 e) : A) :=
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hh
    have hne : M + e ≠ N := by omega
    have h2 : ((DirectSum.decompose 𝒜 (h * r) (M + e) : 𝒜 (M + e)) : A) = 0 :=
      DirectSum.decompose_of_mem_ne 𝒜 hmul (Ne.symm hne)
    rw [h2] at h1
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd h3 hh0
    · exact h3
  have hsub : (DirectSum.decompose 𝒜 r).support ⊆ ({N - M} : Finset ℕ) := by
    intro e he
    rw [Finset.mem_singleton]
    by_contra hne
    exact (DFinsupp.mem_support_iff.mp he) (Submodule.coe_eq_zero.mp (key e hne))
  have hsum : (∑ i ∈ (DirectSum.decompose 𝒜 r).support,
        ((DirectSum.decompose 𝒜 r i : 𝒜 i) : A))
      = ∑ i ∈ ({N - M} : Finset ℕ), ((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) := by
    refine Finset.sum_subset hsub ?_
    intro x _ hx
    rw [DFinsupp.notMem_support_iff.mp hx]
    rfl
  rw [Finset.sum_singleton] at hsum
  have hr : r = ((DirectSum.decompose 𝒜 r (N - M) : 𝒜 (N - M)) : A) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 r]
    exact hsum
  rw [hr]
  exact SetLike.coe_mem _

/-- `A_(f)` is a domain: it embeds via `HomogeneousLocalization.val` into `A_f`, which is a domain
(`A` a domain and `f ≠ 0` ⇒ `Submonoid.powers f ≤ A⁰`, and localization preserves domains). -/
theorem HomogeneousLocalization.Away.isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A} (_hf0 : f ≠ 0) :
    IsDomain (HomogeneousLocalization.Away 𝒜 f) := by
  have : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (powers_le_nonZeroDivisors_of_noZeroDivisors _hf0)
  exact (HomogeneousLocalization.val_injective _).isDomain
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))

/-- **The degree-zero homogeneous localization of an integrally closed graded domain is integrally
closed**: `A` an `ℕ`-graded integrally closed domain, `f` homogeneous, `deg f = d > 0`, `f ≠ 0` ⇒
`A_(f)` is integrally closed.

For the proof see the module docstring; step 4 (the only mathematical content) is
`homogeneous_of_mul_homogeneous`, the rest is transport along `Frac B ↪ Frac L` (`L := A_f`). The
ambient field in Lean is `Frac L` (rather than `Frac A`), so that `Algebra B (Frac L)` and
`IsScalarTower B L (Frac L)` are the ready-made `Localization` instances. (`_hd : 0 < d` is in fact
not used, see the module docstring; it is kept to match the call sites.) -/
theorem HomogeneousLocalization.Away.isIntegrallyClosed_of_isIntegrallyClosed
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {d : ℕ} (_hd : 0 < d) {f : A} (_hf : f ∈ 𝒜 d)
    (_hf0 : f ≠ 0) :
    IsIntegrallyClosed (HomogeneousLocalization.Away 𝒜 f) := by
  classical
  have hle : Submonoid.powers f ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors _hf0
  have hLdom : IsDomain (Localization.Away f) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hBdom : IsDomain (HomogeneousLocalization.Away 𝒜 f) :=
    HomogeneousLocalization.Away.isDomain 𝒜 _hf0
  have hLic : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers f) hle
  -- `B → L → Frac L`
  let ι : HomogeneousLocalization.Away 𝒜 f →+* FractionRing (Localization.Away f) :=
    (algebraMap (Localization.Away f) (FractionRing (Localization.Away f))).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  have hι : Function.Injective ι :=
    (IsFractionRing.injective (Localization.Away f) _).comp
      (HomogeneousLocalization.val_injective _)
  -- `Algebra B (Frac L)` and `IsScalarTower B L (Frac L)` are supplied by the `Localization`
  -- instances; their `algebraMap` is definitionally `ι`.
  have : IsScalarTower (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)
      (FractionRing (Localization.Away f)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- `Frac B → Frac L`
  let j : FractionRing (HomogeneousLocalization.Away 𝒜 f) →+* FractionRing (Localization.Away f) :=
    IsFractionRing.lift hι
  have hj : Function.Injective j := j.injective
  let jA : FractionRing (HomogeneousLocalization.Away 𝒜 f) →ₐ[HomogeneousLocalization.Away 𝒜 f]
      FractionRing (Localization.Away f) :=
    { j with commutes' := fun b => IsFractionRing.lift_algebraMap hι b }
  rw [isIntegrallyClosed_iff (FractionRing (HomogeneousLocalization.Away 𝒜 f))]
  intro x hx
  -- Step 1: `j x` is integral over `L`, `L` is integrally closed, so `j x` comes from `L`
  have h1 : IsIntegral (Localization.Away f) (j x) := (hx.map jA).tower_top
  obtain ⟨l, hl⟩ := (isIntegrallyClosed_iff (FractionRing (Localization.Away f))).mp hLic h1
  -- Step 2: the fraction form
  obtain ⟨⟨r, y⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) l
  obtain ⟨n, hn⟩ := y.2
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (HomogeneousLocalization.Away 𝒜 f)) x
  dsimp only at hl ⊢
  obtain ⟨q, a', ha', hb₁⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 _hf b₁
  obtain ⟨p, b', hb', hb₂⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 _hf (b₂ : _)
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    apply nonZeroDivisors.ne_zero b₂.2
    rw [← hb₂]
    ext
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]
  -- Step 3: clear denominators to get an equation in `A`
  have hι2 : ι b₂ ≠ 0 := fun h => nonZeroDivisors.ne_zero b₂.2 (hι (by rw [h, map_zero]))
  have h3 : (b₂ : HomogeneousLocalization.Away 𝒜 f).val *
      IsLocalization.mk' (Localization.Away f) r y = b₁.val := by
    apply IsFractionRing.injective (Localization.Away f) (FractionRing (Localization.Away f))
    have := (eq_div_iff hι2).mp (hl.trans (IsFractionRing.lift_mk' hι b₁ b₂))
    rw [map_mul, mul_comm]
    exact this
  rw [← hb₁, ← hb₂, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', ← IsLocalization.mk'_mul,
    IsLocalization.mk'_eq_iff_eq] at h3
  have hA := IsLocalization.injective (Localization.Away f) hle h3
  simp only [Submonoid.coe_mul, ← hn] at hA
  -- `hA : f ^ q * (b' * r) = f ^ p * f ^ n * a'`
  have hA' : b' * f ^ q * r = a' * f ^ (n + p) := by
    rw [pow_add]
    linear_combination hA
  -- Step 4: determine the degree
  have hh : b' * f ^ q ∈ 𝒜 (p • d + q • d) :=
    SetLike.mul_mem_graded hb' (SetLike.pow_mem_graded q _hf)
  have hh0 : b' * f ^ q ≠ 0 := mul_ne_zero hb'0 (pow_ne_zero q _hf0)
  have hmul : b' * f ^ q * r ∈ 𝒜 (q • d + (n + p) • d) := by
    rw [hA']
    exact SetLike.mul_mem_graded ha' (SetLike.pow_mem_graded (n + p) _hf)
  have hMN : p • d + q • d ≤ q • d + (n + p) • d :=
    calc p • d + q • d = q • d + p • d := add_comm _ _
      _ ≤ q • d + (n + p) • d :=
        Nat.add_le_add_left (by rw [add_smul]; exact Nat.le_add_left _ _) _
  have hr : r ∈ 𝒜 (n • d) := by
    have hsub : q • d + (n + p) • d - (p • d + q • d) = n • d := by
      simp only [smul_eq_mul, add_mul]
      omega
    rw [← hsub]
    exact homogeneous_of_mul_homogeneous 𝒜 hh hh0 hmul hMN
  -- Step 5: conclude
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 _hf n r hr, hj ?_⟩
  rw [IsFractionRing.lift_algebraMap, ← hl]
  show algebraMap (Localization.Away f) _ (Localization.mk r _) = _
  rw [Localization.mk_eq_mk']
  congr 2
  exact Subtype.ext hn

end
