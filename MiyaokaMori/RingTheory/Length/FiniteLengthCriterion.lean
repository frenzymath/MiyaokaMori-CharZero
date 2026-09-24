import MiyaokaMori.Prelude

/-! # A finiteness criterion for the length of a module over a finite algebra

Let `A` be Noetherian, `B` a finite `A`-algebra, `𝔭 ⊂ B` a prime, and suppose `length_A(B/(𝔭+yB)) < ∞` for
all `y ∉ 𝔭`. Then every finite `B`-module `N` annihilated by some `s ∉ 𝔭` and by some `𝔭^n` has finite
`A`-length.

References: the case "supported in `{𝔪}` ⇒ finite length" in the proofs of Stacks 00L5 / 02QF; Stacks 00L0
(`𝔭`-adic filtration).
-/

set_option autoImplicit false

universe u

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] (𝔭 : Ideal B) [𝔭.IsPrime]

omit [IsNoetherianRing A] [Module.Finite A B] in
/-- A finite `B`-module killed by an ideal `J` with `B ⧸ J` Artinian over `A` is Artinian over `A`:
it is the image of the `A`-linear surjection `(Fin n → B ⧸ J) → M` induced by a finite generating
family, and `Fin n → B ⧸ J` is Artinian over `A` (`isArtinian_pi'`). -/
theorem isArtinian_of_isArtinian_quotient_of_smul_eq_zero (J : Ideal B) (hJ : IsArtinian A (B ⧸ J))
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] (hM : ∀ x ∈ J, ∀ m : M, x • m = 0) : IsArtinian A M := by
  classical
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := B) (M := M)
  -- `f i : B ⧸ J → M`, `x̄ ↦ x • v i`.
  let f : Fin n → (B ⧸ J) →ₗ[B] M := fun i =>
    Submodule.liftQ J (LinearMap.toSpanSingleton B M (v i)) (fun x hx => hM x hx (v i))
  let φ : (Fin n → B ⧸ J) →ₗ[B] M := LinearMap.lsum B (fun _ : Fin n => B ⧸ J) ℕ f
  have hφ : Function.Surjective φ := by
    intro m
    have hm : m ∈ Submodule.span B (Set.range v) := hv ▸ Submodule.mem_top
    rw [← Fintype.range_linearCombination] at hm
    obtain ⟨x, rfl⟩ := hm
    refine ⟨fun i => Submodule.Quotient.mk (x i), ?_⟩
    simp only [φ, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      f, Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  exact isArtinian_of_surjective _ (φ.restrictScalars A) hφ

omit [𝔭.IsPrime] in
/-- Induction on `n`: a finite `B`-module `M` killed by `s` and `𝔭 ^ n` is Artinian over `A`, given
that `B ⧸ (𝔭 ⊔ sB)` is Artinian over `A`. Step: `0 → 𝔭M → M → M/𝔭M → 0`; `𝔭M` is killed by `𝔭 ^ (n-1)`
(induction hypothesis), `M/𝔭M` is killed by `𝔭 ⊔ sB` (previous lemma), and Artinian is closed under
extensions (`isArtinian_of_range_eq_ker`). -/
theorem isArtinian_of_pow_smul_eq_zero (s : B) (hL : IsArtinian A (B ⧸ (𝔭 ⊔ Ideal.span {s}))) (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
      [Module.Finite B M], (∀ x ∈ 𝔭 ^ n, ∀ m : M, x • m = 0) → (∀ m : M, s • m = 0) →
      IsArtinian A M := by
  induction n with
  | zero =>
    intro M _ _ _ _ _ hM _
    have : Subsingleton M := ⟨fun a b => by
      have ha := hM 1 (by simp) a
      have hb := hM 1 (by simp) b
      rw [one_smul] at ha hb
      rw [ha, hb]⟩
    infer_instance
  | succ k ih =>
    intro M _ _ _ _ _ hM hs
    have hB : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    let M' : Submodule B M := 𝔭 • ⊤
    have h1 : IsArtinian A M' := by
      have : Module.Finite B M' := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian M')
      refine ih M' ?_ ?_
      · intro x hx m
        refine Subtype.ext ?_
        change x • (m : M) = 0
        refine Submodule.smul_induction_on m.2 ?_ ?_
        · intro y hy z _
          rw [smul_smul]
          exact hM _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hx hy) z
        · intro a b ha hb
          rw [smul_add, ha, hb, add_zero]
      · intro m
        exact Subtype.ext (hs (m : M))
    have h2 : IsArtinian A (M ⧸ M') := by
      refine isArtinian_of_isArtinian_quotient_of_smul_eq_zero (𝔭 ⊔ Ideal.span {s}) hL (M ⧸ M') ?_
      intro x hx m
      obtain ⟨p, hp, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ht
      induction m using Submodule.Quotient.induction_on with
      | H m =>
        rw [← Submodule.Quotient.mk_smul, add_smul, mul_smul, hs, smul_zero, add_zero,
          Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hp Submodule.mem_top
    exact isArtinian_of_range_eq_ker (M'.subtype.restrictScalars A) (M'.mkQ.restrictScalars A)
      (by rw [LinearMap.range_restrictScalars, LinearMap.ker_restrictScalars, Submodule.range_subtype,
        Submodule.ker_mkQ])

/-- Proof. Let `C := B ⧸ (𝔭^n ⊔ span {s})`; `N` is a finite `C`-module, hence a quotient of some `C^k`, so it
suffices that `length_A C < ∞`. By induction on `n`:
`0 → (𝔭^i ⊔ sB)/(𝔭^{i+1} ⊔ sB) → B/(𝔭^{i+1} ⊔ sB) → B/(𝔭^i ⊔ sB) → 0`, where the left term is killed by `𝔭`
and `s`, hence a finite module over `B/(𝔭 ⊔ sB)` (`B` Noetherian: `IsNoetherianRing.of_finite A B`), and
`length_A(B/(𝔭 ⊔ sB)) < ∞` is the hypothesis `hfl`. Use `Module.length_eq_add_of_exact`,
`Module.length_le_of_surjective`, and the length of finite free modules (`Module.length_pi` /
`length_finsupp`). Edge case `n = 0`: `𝔭^0 = ⊤`, `N = 0`.

The actual route uses Artinianness instead of length arithmetic: `hfl` at `y = s` gives
`length_A(B/(𝔭 ⊔ sB)) ≠ ⊤`, i.e. `B/(𝔭 ⊔ sB)` is an Artinian `A`-module (`Module.length_ne_top_iff` +
`isFiniteLength_iff_isNoetherian_isArtinian`); `isArtinian_of_pow_smul_eq_zero` proves by induction on `n`
(filtration `N ⊇ 𝔭N ⊇ … ⊇ 𝔭^n N = 0`) that `N` is an Artinian `A`-module; `N` is also a finite `A`-module
(`Module.Finite.trans B N`), hence Noetherian; conclude with `Module.length_ne_top`. -/
theorem length_ne_top_of_smul_eq_zero
    (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤)
    (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] [Module.Finite B N]
    (s : B) (hs : s ∉ 𝔭) (n : ℕ) (hN : ∀ x ∈ 𝔭 ^ n, ∀ m : N, x • m = 0) (hsN : ∀ m : N, s • m = 0) :
    Module.length A N ≠ ⊤ := by
  have hL : IsArtinian A (B ⧸ (𝔭 ⊔ Ideal.span {s})) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp (hfl s hs))).2
  have : IsArtinian A N := isArtinian_of_pow_smul_eq_zero 𝔭 s hL n N hN hsN
  have : Module.Finite A N := Module.Finite.trans B N
  have : IsNoetherian A N := inferInstance
  exact Module.length_ne_top

end KeyLemma

end
