import MiyaokaMori.Prelude

/-! # Lengths of the cohomology of `2`-periodic complexes

Let `R` be a ring. A `2`-periodic complex `(M, N, φ : M → N, ψ : N → M)` (`φψ = 0`, `ψφ = 0`) has cohomology
`H⁰ = Ker φ / Im ψ`, `H¹ = Ker ψ / Im φ` (`PeriodicComplex.H φ ψ`, `PeriodicComplex.H ψ φ`).
(1) (The `ℕ∞` form of Stacks 0EA7.) For a short exact sequence `0 → A → B → C → 0` of `2`-periodic
    complexes there are `a b c d a' c' ∈ ℕ∞` with `l H⁰A = b + a`, `l H⁰B = a + c`, `l H⁰C = c + d`,
    `l H¹A = d + a'`, `l H¹B = a' + c'`, `l H¹C = c' + b`; hence unconditionally
    `l H⁰A + l H⁰C + l H¹B = l H⁰B + l H¹A + l H¹C`, if two of the three have finite-length cohomology so does
    the third, and `e(B) = e(A) + e(C)` where `e = l H⁰ − l H¹` (`PeriodicComplex.herbrand`).
(2) (0EA8) `l M + l H¹ = l N + l H⁰`; in particular a `(2,1)`-periodic complex with `M` of finite length has
    `e = 0`.
(3) (Formula 0EA6) `e(M, 0, ψ) = l Coker ψ − l Ker ψ`.
(4) (0EA9) For a morphism `f : (M, φ, ψ) → (M', φ', ψ')` of `(2,1)`-periodic complexes with `Ker f`, `Coker f`
    of finite length, one side has finite-length cohomology iff the other does, and the `e`s agree.

Proof:
1. Relative length `relLength A B = l(B/A∩B)` (`A`, `B` submodules of the same module). Additivity along
   chains (`0 → B/A → C/A → C/B → 0` and Mathlib `Module.length_eq_add_of_exact`), the second isomorphism
   theorem (Mathlib `LinearMap.quotientInfEquivSupQuotient`), `l(fB/fA) = l(B/A)` under a linear map `f`
   (when `Ker f ∩ B ≤ A`; `LinearMap.quotKerEquivOfSurjective`) and its consequence
   `l(f⁻¹B/f⁻¹A) = l(B ∩ Im f / A ∩ Im f)`.
2. Rewrite the short exact sequence in lattice language: `M' = i(M₁) ≤ M = M₂`, `N' = j(N₁) ≤ N = N₂`,
   `φ = φ₂`, `ψ = ψ₂`; then (`i`, `j` injective, `p`, `q` surjective, exactness)
   `l H⁰A = l((Ker φ ∩ M')/ψN')`, `l H⁰B = l(Ker φ/ψN)`, `l H⁰C = l(φ⁻¹N'/(ψN + M'))`.
3. Take the chains `ψN' ≤ ψN ∩ M' ≤ Ker φ ∩ M'`; `ψN ≤ ψN + Ker φ ∩ M' ≤ Ker φ`;
   `ψN + M' ≤ Ker φ + M' ≤ φ⁻¹N'`. Write `a = l((Ker φ ∩ M')/(ψN ∩ M'))`, `b = l((ψN ∩ M')/ψN')`,
   `c = l(Ker φ/(ψN + Ker φ ∩ M'))`, `d = l((N' ∩ φM)/φM')`. Second isomorphism theorem + modular law give
   `l((ψN + Ker φ∩M')/ψN) = a`, `l((Ker φ + M')/(ψN + M')) = c`; the `comap` formula of step 1 gives
   `l(φ⁻¹N'/(Ker φ + M')) = d` (`Ker φ + M' = φ⁻¹(φM')`). Exchanging `φ`, `ψ` gives `a'`, `b' = d`, `c'`,
   `d' = b`. No connecting homomorphism needs to be constructed.
4. (2): `l M = l Ker φ + l Im φ`, `l Ker φ = l Im ψ + l H⁰`, likewise for `N`. (3): `Ker 0 = ⊤`, `Im 0 = ⊥`.
   (4): apply (1) to `0 → Ker f → M → Im f → 0` and `0 → Im f → M' → Coker f → 0`; the cohomology of
   `Ker f`, `Coker f` has finite length and `e = 0` by (2).

References: Stacks 02PG, 02PH (definitions), 0EA6, 0EA7, 0EA8, 0EA9; the `ℕ∞` form and the lattice proof
are our own.
-/

set_option autoImplicit false

open Submodule

namespace PeriodicComplex

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-! ## Relative length -/

/-- The relative length `l(B/(A ∩ B))`; for `A ≤ B` this is `l(B/A)`. -/
noncomputable def relLength (A B : Submodule R M) : ℕ∞ :=
  Module.length R (↥B ⧸ A.submoduleOf B)

theorem length_eq_relLength {P : Type*} [AddCommGroup P] [Module R P] {A B : Submodule R M}
    (g : ↥B →ₗ[R] P) (hg : Function.Surjective g) (hk : LinearMap.ker g = A.submoduleOf B) :
    Module.length R P = relLength A B := by
  unfold relLength
  rw [← hk]
  exact (LinearMap.quotKerEquivOfSurjective g hg).length_eq.symm

theorem relLength_congr_inf (A B : Submodule R M) : relLength (A ⊓ B) B = relLength A B := by
  unfold relLength
  have : (A ⊓ B).submoduleOf B = A.submoduleOf B := by
    ext x; simp [Submodule.submoduleOf]
  rw [this]

theorem relLength_self (A : Submodule R M) : relLength A A = 0 := by
  unfold relLength
  rw [Submodule.submoduleOf_self]
  exact Module.length_eq_zero

theorem relLength_bot (B : Submodule R M) : relLength ⊥ B = Module.length R B := by
  refine (length_eq_relLength (LinearMap.id : ↥B →ₗ[R] ↥B) Function.surjective_id ?_).symm
  ext x; simp [Submodule.submoduleOf]

theorem relLength_top (A : Submodule R M) : relLength A ⊤ = Module.length R (M ⧸ A) := by
  refine (length_eq_relLength (A.mkQ ∘ₗ (⊤ : Submodule R M).subtype) ?_ ?_).symm
  · intro y
    obtain ⟨x, rfl⟩ := A.mkQ_surjective y
    exact ⟨⟨x, trivial⟩, rfl⟩
  · ext x; simp [Submodule.submoduleOf]

/-- Additivity along chains: for `A ≤ B ≤ C`, `l(C/A) = l(B/A) + l(C/B)`. -/
theorem relLength_add {A B C : Submodule R M} (hAB : A ≤ B) (hBC : B ≤ C) :
    relLength A C = relLength A B + relLength B C := by
  have hle : A.submoduleOf C ≤ B.submoduleOf C := fun x hx => hAB hx
  -- `S` = the image of `B/A` in `C/A`
  let S : Submodule R (↥C ⧸ A.submoduleOf C) := (B.submoduleOf C).map (A.submoduleOf C).mkQ
  have h1 : Module.length R S = relLength A B := by
    let g : ↥B →ₗ[R] ↥S :=
      ((A.submoduleOf C).mkQ.submoduleMap (B.submoduleOf C)) ∘ₗ
        (Submodule.submoduleOfEquivOfLe hBC).symm.toLinearMap
    refine length_eq_relLength g ?_ ?_
    · exact (LinearMap.submoduleMap_surjective _ _).comp (LinearEquiv.surjective _)
    · ext x
      simp only [LinearMap.mem_ker, g, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← Subtype.coe_inj]
      change (A.submoduleOf C).mkQ ((Submodule.submoduleOfEquivOfLe hBC).symm x : ↥C) = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      rfl
  have h2 : Module.length R ((↥C ⧸ A.submoduleOf C) ⧸ S) = relLength B C := by
    refine length_eq_relLength (S.mkQ ∘ₗ (A.submoduleOf C).mkQ)
      ((Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)) ?_
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, S, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y - x ∈ A.submoduleOf C := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hyx, sub_self]
      have hx : x = y - (y - x) := by abel
      rw [hx]
      exact Submodule.sub_mem _ hy (hle this)
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [← h1, ← h2]
  unfold relLength
  exact Module.length_eq_add_of_exact S.subtype S.mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ S)

/-- Second isomorphism theorem: `l((A + B)/A) = l(B/(A ∩ B))`. -/
theorem relLength_sup_left (A B : Submodule R M) : relLength A (A ⊔ B) = relLength A B := by
  unfold relLength
  have e := LinearMap.quotientInfEquivSupQuotient B A
  have h1 : Submodule.comap B.subtype (B ⊓ A) = A.submoduleOf B := by
    ext x; simp [Submodule.submoduleOf]
  have h2 : relLength A (B ⊔ A) = relLength A B := by
    unfold relLength
    rw [← h1]
    exact e.length_eq.symm
  rw [sup_comm]
  exact h2

/-- `l(fB/fA) = l(B/A)` whenever `Ker f ∩ B ≤ A ≤ B`. -/
theorem relLength_map (f : M →ₗ[R] N) {A B : Submodule R M} (hAB : A ≤ B)
    (hker : LinearMap.ker f ⊓ B ≤ A) :
    relLength (A.map f) (B.map f) = relLength A B := by
  symm
  refine (length_eq_relLength (((A.map f).submoduleOf (B.map f)).mkQ ∘ₗ f.submoduleMap B)
    ((Submodule.mkQ_surjective _).comp (LinearMap.submoduleMap_surjective _ _)) ?_).symm
  ext x
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change f x ∈ A.map f ↔ (x : M) ∈ A
  constructor
  · rintro ⟨a, ha, hax⟩
    have hk : (x : M) - a ∈ LinearMap.ker f ⊓ B :=
      Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr (by rw [map_sub, hax, sub_self]),
        B.sub_mem x.2 (hAB ha)⟩
    have hx : (x : M) = a + ((x : M) - a) := by abel
    rw [hx]
    exact A.add_mem ha (hker hk)
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem relLength_map_of_injective (f : M →ₗ[R] N) (hf : Function.Injective f)
    {A B : Submodule R M} (hAB : A ≤ B) :
    relLength (A.map f) (B.map f) = relLength A B :=
  relLength_map f hAB (by rw [LinearMap.ker_eq_bot.mpr hf]; simp)

/-- `l(f⁻¹B/f⁻¹A) = l((B ∩ Im f)/(A ∩ Im f))`. -/
theorem relLength_comap (f : M →ₗ[R] N) {A B : Submodule R N} (hAB : A ≤ B) :
    relLength (A.comap f) (B.comap f) = relLength (A ⊓ LinearMap.range f) (B ⊓ LinearMap.range f) := by
  rw [← relLength_map f (Submodule.comap_mono hAB), Submodule.map_comap_eq, Submodule.map_comap_eq,
    inf_comm, inf_comm (LinearMap.range f)]
  exact inf_le_of_left_le (fun x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker.mp hx]; exact A.zero_mem)

theorem relLength_comap_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    {A B : Submodule R N} (hAB : A ≤ B) :
    relLength (A.comap f) (B.comap f) = relLength A B := by
  rw [relLength_comap f hAB, LinearMap.range_eq_top.mpr hf, inf_top_eq, inf_top_eq]

/-! ## The lattice version of the six-term decomposition -/

/-- Half of the decomposition: `M' ≤ M`, `N' ≤ N`, `φ(M') ≤ N'`, `ψ(N') ≤ M'`, `Im ψ ≤ Ker φ`. -/
theorem lattice_half (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) (M' : Submodule R M) (N' : Submodule R N)
    (hψφ : LinearMap.range ψ ≤ LinearMap.ker φ) (hφ' : M'.map φ ≤ N') (hψ' : N'.map ψ ≤ M') :
    relLength (N'.map ψ) (LinearMap.ker φ ⊓ M') =
        relLength (N'.map ψ) (M' ⊓ LinearMap.range ψ) +
          relLength (LinearMap.range ψ ⊓ M') (LinearMap.ker φ ⊓ M') ∧
      relLength (LinearMap.range ψ) (LinearMap.ker φ) =
        relLength (LinearMap.range ψ ⊓ M') (LinearMap.ker φ ⊓ M') +
          relLength (LinearMap.range ψ ⊔ LinearMap.ker φ ⊓ M') (LinearMap.ker φ) ∧
      relLength (LinearMap.range ψ ⊔ M') (N'.comap φ) =
        relLength (LinearMap.range ψ ⊔ LinearMap.ker φ ⊓ M') (LinearMap.ker φ) +
          relLength (M'.map φ) (N' ⊓ LinearMap.range φ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [inf_comm M']
    exact relLength_add (le_inf (LinearMap.map_le_range) hψ') (inf_le_inf_right _ hψφ)
  · rw [relLength_add (le_sup_left : LinearMap.range ψ ≤ LinearMap.range ψ ⊔ LinearMap.ker φ ⊓ M')
      (sup_le hψφ inf_le_left), relLength_sup_left, ← relLength_congr_inf, ← inf_assoc,
      inf_eq_left.mpr hψφ]
  · have h1 : LinearMap.range ψ ⊔ M' ≤ LinearMap.ker φ ⊔ M' := sup_le_sup_right hψφ _
    have h2 : LinearMap.ker φ ⊔ M' ≤ N'.comap φ := by
      refine sup_le (fun x hx => ?_) (Submodule.map_le_iff_le_comap.mp hφ')
      rw [Submodule.mem_comap, LinearMap.mem_ker.mp hx]; exact N'.zero_mem
    rw [relLength_add h1 h2]
    congr 1
    · have e1 : LinearMap.ker φ ⊔ M' = (LinearMap.range ψ ⊔ M') ⊔ LinearMap.ker φ := by
        rw [sup_comm (LinearMap.range ψ), sup_assoc, sup_eq_right.mpr hψφ, sup_comm]
      rw [e1, relLength_sup_left, ← relLength_congr_inf, sup_inf_assoc_of_le _ hψφ,
        inf_comm M']
    · have e2 : LinearMap.ker φ ⊔ M' = (M'.map φ).comap φ := by
        rw [Submodule.comap_map_eq, sup_comm]
      rw [e2, relLength_comap φ hφ', inf_eq_left.mpr (LinearMap.map_le_range)]

/-! ## Cohomology of `2`-periodic complexes and short exact sequences -/

/-- `H(φ, ψ) = Ker φ / Im ψ`. For a `2`-periodic complex `(M, N, φ, ψ)`, `H⁰ = H φ ψ` and `H¹ = H ψ φ`. -/
abbrev H (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) : Type _ :=
  ↥(LinearMap.ker φ) ⧸ (LinearMap.range ψ).submoduleOf (LinearMap.ker φ)

theorem length_H (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) :
    Module.length R (H φ ψ) = relLength (LinearMap.range ψ) (LinearMap.ker φ) := rfl

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]

/-- A short exact sequence of `2`-periodic complexes `0 → (M₁,N₁,φ₁,ψ₁) → (M₂,N₂,φ₂,ψ₂) → (M₃,N₃,φ₃,ψ₃) → 0`
(the middle term is a complex; that the outer terms are complexes follows). -/
structure ShortExact (φ₁ : M₁ →ₗ[R] N₁) (ψ₁ : N₁ →ₗ[R] M₁) (φ₂ : M₂ →ₗ[R] N₂) (ψ₂ : N₂ →ₗ[R] M₂)
    (φ₃ : M₃ →ₗ[R] N₃) (ψ₃ : N₃ →ₗ[R] M₃)
    (i : M₁ →ₗ[R] M₂) (j : N₁ →ₗ[R] N₂) (p : M₂ →ₗ[R] M₃) (q : N₂ →ₗ[R] N₃) : Prop where
  i_inj : Function.Injective i
  j_inj : Function.Injective j
  p_surj : Function.Surjective p
  q_surj : Function.Surjective q
  exact_M : Function.Exact i p
  exact_N : Function.Exact j q
  comm_φi : φ₂ ∘ₗ i = j ∘ₗ φ₁
  comm_ψj : ψ₂ ∘ₗ j = i ∘ₗ ψ₁
  comm_φp : φ₃ ∘ₗ p = q ∘ₗ φ₂
  comm_ψq : ψ₃ ∘ₗ q = p ∘ₗ ψ₂
  φψ : φ₂ ∘ₗ ψ₂ = 0
  ψφ : ψ₂ ∘ₗ φ₂ = 0

namespace ShortExact

variable {φ₁ : M₁ →ₗ[R] N₁} {ψ₁ : N₁ →ₗ[R] M₁} {φ₂ : M₂ →ₗ[R] N₂} {ψ₂ : N₂ →ₗ[R] M₂}
  {φ₃ : M₃ →ₗ[R] N₃} {ψ₃ : N₃ →ₗ[R] M₃}
  {i : M₁ →ₗ[R] M₂} {j : N₁ →ₗ[R] N₂} {p : M₂ →ₗ[R] M₃} {q : N₂ →ₗ[R] N₃}

theorem symm (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) :
    ShortExact ψ₁ φ₁ ψ₂ φ₂ ψ₃ φ₃ j i q p :=
  ⟨h.j_inj, h.i_inj, h.q_surj, h.p_surj, h.exact_N, h.exact_M, h.comm_ψj, h.comm_φi,
    h.comm_ψq, h.comm_φp, h.ψφ, h.φψ⟩

theorem range_le_ker₂ (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) :
    LinearMap.range ψ₂ ≤ LinearMap.ker φ₂ :=
  LinearMap.range_le_ker_iff.mpr h.φψ

theorem range_le_ker₁ (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) :
    LinearMap.range ψ₁ ≤ LinearMap.ker φ₁ := by
  rintro _ ⟨n, rfl⟩
  rw [LinearMap.mem_ker]
  apply h.j_inj
  have e1 : j (φ₁ (ψ₁ n)) = φ₂ (i (ψ₁ n)) := (LinearMap.congr_fun h.comm_φi (ψ₁ n)).symm
  have e2 : i (ψ₁ n) = ψ₂ (j n) := (LinearMap.congr_fun h.comm_ψj n).symm
  rw [e1, e2, map_zero]
  exact LinearMap.congr_fun h.φψ (j n)

theorem range_le_ker₃ (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) :
    LinearMap.range ψ₃ ≤ LinearMap.ker φ₃ := by
  rintro _ ⟨n, rfl⟩
  obtain ⟨n, rfl⟩ := h.q_surj n
  rw [LinearMap.mem_ker]
  have e1 : ψ₃ (q n) = p (ψ₂ n) := LinearMap.congr_fun h.comm_ψq n
  have e2 : φ₃ (p (ψ₂ n)) = q (φ₂ (ψ₂ n)) := LinearMap.congr_fun h.comm_φp (ψ₂ n)
  have e3 : φ₂ (ψ₂ n) = 0 := LinearMap.congr_fun h.φψ n
  rw [e1, e2, e3, map_zero]

theorem length_H₁ (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) :
    Module.length R (H φ₁ ψ₁) =
      relLength ((LinearMap.range j).map ψ₂) (LinearMap.ker φ₂ ⊓ LinearMap.range i) := by
  rw [length_H, ← relLength_map_of_injective i h.i_inj h.range_le_ker₁]
  congr 1
  · rw [← LinearMap.range_comp, ← LinearMap.range_comp, h.comm_ψj]
  · ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, LinearMap.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine ⟨?_, m, rfl⟩
      have e1 : φ₂ (i m) = j (φ₁ m) := LinearMap.congr_fun h.comm_φi m
      rw [e1, hm, map_zero]
    · rintro ⟨hx, m, rfl⟩
      refine ⟨m, h.j_inj ?_, rfl⟩
      have e1 : φ₂ (i m) = j (φ₁ m) := LinearMap.congr_fun h.comm_φi m
      rw [map_zero, ← e1, hx]

theorem length_H₃ (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) :
    Module.length R (H φ₃ ψ₃) =
      relLength (LinearMap.range ψ₂ ⊔ LinearMap.range i) ((LinearMap.range j).comap φ₂) := by
  rw [length_H, ← relLength_comap_of_surjective p h.p_surj h.range_le_ker₃]
  congr 1
  · have e1 : LinearMap.range ψ₃ = (LinearMap.range ψ₂).map p := by
      rw [← LinearMap.range_comp, ← h.comm_ψq, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr h.q_surj, Submodule.map_top]
    rw [e1, Submodule.comap_map_eq, LinearMap.exact_iff.mp h.exact_M]
  · rw [← LinearMap.ker_comp, h.comm_φp, LinearMap.ker_comp, LinearMap.exact_iff.mp h.exact_N]

/-- The `ℕ∞` form of Stacks 0EA7 (six-term decomposition). -/
theorem exists_length_decomp (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) :
    ∃ a b c d a' c' : ℕ∞,
      Module.length R (H φ₁ ψ₁) = b + a ∧ Module.length R (H φ₂ ψ₂) = a + c ∧
      Module.length R (H φ₃ ψ₃) = c + d ∧ Module.length R (H ψ₁ φ₁) = d + a' ∧
      Module.length R (H ψ₂ φ₂) = a' + c' ∧ Module.length R (H ψ₃ φ₃) = c' + b := by
  have hM : (LinearMap.range i).map φ₂ ≤ LinearMap.range j := by
    rw [← LinearMap.range_comp, h.comm_φi, LinearMap.range_comp]; exact LinearMap.map_le_range
  have hN : (LinearMap.range j).map ψ₂ ≤ LinearMap.range i := by
    rw [← LinearMap.range_comp, h.comm_ψj, LinearMap.range_comp]; exact LinearMap.map_le_range
  obtain ⟨e1, e2, e3⟩ := lattice_half φ₂ ψ₂ _ _ h.range_le_ker₂ hM hN
  obtain ⟨f1, f2, f3⟩ := lattice_half ψ₂ φ₂ _ _ h.symm.range_le_ker₂ hN hM
  exact ⟨_, _, _, _, _, _, h.length_H₁.trans e1, (length_H _ _).trans e2, h.length_H₃.trans e3,
    h.symm.length_H₁.trans f1, (length_H _ _).trans f2, h.symm.length_H₃.trans f3⟩

/-- The unconditional six-term identity. -/
theorem length_add_eq (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) :
    Module.length R (H φ₁ ψ₁) + Module.length R (H φ₃ ψ₃) + Module.length R (H ψ₂ φ₂) =
      Module.length R (H φ₂ ψ₂) + Module.length R (H ψ₁ φ₁) + Module.length R (H ψ₃ φ₃) := by
  obtain ⟨a, b, c, d, a', c', h1, h2, h3, h4, h5, h6⟩ := h.exists_length_decomp
  rw [h1, h2, h3, h4, h5, h6]
  ac_rfl

end ShortExact

/-! ## The Herbrand quotient `e = l H⁰ − l H¹` -/

/-- The cohomology has finite length. -/
def FiniteCohomology (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) : Prop :=
  Module.length R (H φ ψ) ≠ ⊤ ∧ Module.length R (H ψ φ) ≠ ⊤

/-- The (additive) Herbrand quotient `e_R(M, N, φ, ψ) = l H⁰ − l H¹` (Stacks 02PH; meaningful only when the
cohomology has finite length). -/
noncomputable def herbrand (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) : ℤ :=
  ((Module.length R (H φ ψ)).toNat : ℤ) - ((Module.length R (H ψ φ)).toNat : ℤ)

theorem FiniteCohomology.symm {φ : M →ₗ[R] N} {ψ : N →ₗ[R] M} (h : FiniteCohomology φ ψ) :
    FiniteCohomology ψ φ := ⟨h.2, h.1⟩

theorem herbrand_symm (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) : herbrand ψ φ = - herbrand φ ψ := by
  unfold herbrand; ring

theorem length_H_le (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) :
    Module.length R (H φ ψ) ≤ Module.length R M :=
  (Module.length_le_of_surjective _ (Submodule.mkQ_surjective _)).trans
    (Module.length_le_of_injective _ (Submodule.subtype_injective _))

namespace ShortExact

variable {φ₁ : M₁ →ₗ[R] N₁} {ψ₁ : N₁ →ₗ[R] M₁} {φ₂ : M₂ →ₗ[R] N₂} {ψ₂ : N₂ →ₗ[R] M₂}
  {φ₃ : M₃ →ₗ[R] N₃} {ψ₃ : N₃ →ₗ[R] M₃}
  {i : M₁ →ₗ[R] M₂} {j : N₁ →ₗ[R] N₂} {p : M₂ →ₗ[R] M₃} {q : N₂ →ₗ[R] N₃}

theorem finite₂ (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) (h1 : FiniteCohomology φ₁ ψ₁)
    (h3 : FiniteCohomology φ₃ ψ₃) : FiniteCohomology φ₂ ψ₂ := by
  obtain ⟨a, b, c, d, a', c', e1, e2, e3, e4, e5, e6⟩ := h.exists_length_decomp
  unfold FiniteCohomology at *
  rw [e1, e4] at h1; rw [e3, e6] at h3; rw [e2, e5]
  simp only [ne_eq, ENat.add_eq_top, not_or] at *
  tauto

theorem finite₃ (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) (h1 : FiniteCohomology φ₁ ψ₁)
    (h2 : FiniteCohomology φ₂ ψ₂) : FiniteCohomology φ₃ ψ₃ := by
  obtain ⟨a, b, c, d, a', c', e1, e2, e3, e4, e5, e6⟩ := h.exists_length_decomp
  unfold FiniteCohomology at *
  rw [e1, e4] at h1; rw [e2, e5] at h2; rw [e3, e6]
  simp only [ne_eq, ENat.add_eq_top, not_or] at *
  tauto

theorem finite₁ (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) (h2 : FiniteCohomology φ₂ ψ₂)
    (h3 : FiniteCohomology φ₃ ψ₃) : FiniteCohomology φ₁ ψ₁ := by
  obtain ⟨a, b, c, d, a', c', e1, e2, e3, e4, e5, e6⟩ := h.exists_length_decomp
  unfold FiniteCohomology at *
  rw [e2, e5] at h2; rw [e3, e6] at h3; rw [e1, e4]
  simp only [ne_eq, ENat.add_eq_top, not_or] at *
  tauto

/-- Stacks 0EA7: the Herbrand quotient is additive on short exact sequences. -/
theorem herbrand_add (h : ShortExact φ₁ ψ₁ φ₂ ψ₂ φ₃ ψ₃ i j p q) (h1 : FiniteCohomology φ₁ ψ₁)
    (h3 : FiniteCohomology φ₃ ψ₃) :
    herbrand φ₂ ψ₂ = herbrand φ₁ ψ₁ + herbrand φ₃ ψ₃ := by
  obtain ⟨a, b, c, d, a', c', e1, e2, e3, e4, e5, e6⟩ := h.exists_length_decomp
  unfold FiniteCohomology at *
  unfold herbrand
  rw [e1, e4] at h1; rw [e3, e6] at h3
  rw [e1, e2, e3, e4, e5, e6]
  simp only [ne_eq, ENat.add_eq_top, not_or] at h1 h3
  obtain ⟨⟨hb, ha⟩, hd, ha'⟩ := h1
  obtain ⟨⟨hc, -⟩, hc', -⟩ := h3
  rw [ENat.toNat_add hb ha, ENat.toNat_add ha hc, ENat.toNat_add hc hd, ENat.toNat_add hd ha',
    ENat.toNat_add ha' hc', ENat.toNat_add hc' hb]
  push_cast
  ring

end ShortExact

/-- `l M = l Im ψ + l H⁰ + l Im φ`. -/
theorem length_eq_range_add_H_add_range (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) (h : φ ∘ₗ ψ = 0) :
    Module.length R M = Module.length R (LinearMap.range ψ) + Module.length R (H φ ψ) +
      Module.length R (LinearMap.range φ) := by
  have hle : LinearMap.range ψ ≤ LinearMap.ker φ := LinearMap.range_le_ker_iff.mpr h
  rw [← (Submodule.topEquiv (R := R) (M := M)).length_eq, ← relLength_bot,
    relLength_add bot_le (le_top : LinearMap.ker φ ≤ ⊤), relLength_add bot_le hle,
    relLength_bot, relLength_top, φ.quotKerEquivRange.length_eq, length_H]

/-- Stacks 0EA8 (`ℕ∞` form): `l M + l H¹ = l N + l H⁰`. -/
theorem length_add_length_H (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) (hφψ : φ ∘ₗ ψ = 0)
    (hψφ : ψ ∘ₗ φ = 0) :
    Module.length R M + Module.length R (H ψ φ) = Module.length R N + Module.length R (H φ ψ) := by
  rw [length_eq_range_add_H_add_range φ ψ hφψ, length_eq_range_add_H_add_range ψ φ hψφ]
  ac_rfl

/-- Stacks 0EA8: if `M`, `N` have finite length then `e = l M − l N`. -/
theorem herbrand_eq_of_length_ne_top (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) (hφψ : φ ∘ₗ ψ = 0)
    (hψφ : ψ ∘ₗ φ = 0) (hM : Module.length R M ≠ ⊤) (hN : Module.length R N ≠ ⊤) :
    FiniteCohomology φ ψ ∧
      herbrand φ ψ = ((Module.length R M).toNat : ℤ) - ((Module.length R N).toNat : ℤ) := by
  have h0 : Module.length R (H φ ψ) ≠ ⊤ := ne_top_of_le_ne_top hM (length_H_le φ ψ)
  have h1 : Module.length R (H ψ φ) ≠ ⊤ := ne_top_of_le_ne_top hN (length_H_le ψ φ)
  refine ⟨⟨h0, h1⟩, ?_⟩
  have e := congrArg ENat.toNat (length_add_length_H φ ψ hφψ hψφ)
  rw [ENat.toNat_add hM h1, ENat.toNat_add hN h0] at e
  unfold herbrand
  omega

/-- Stacks 0EA8: a `(2,1)`-periodic complex with `M` of finite length has `e = 0`. -/
theorem herbrand_eq_zero_of_length_ne_top (φ ψ : M →ₗ[R] M) (hφψ : φ ∘ₗ ψ = 0)
    (hψφ : ψ ∘ₗ φ = 0) (hM : Module.length R M ≠ ⊤) :
    FiniteCohomology φ ψ ∧ herbrand φ ψ = 0 := by
  obtain ⟨h, e⟩ := herbrand_eq_of_length_ne_top φ ψ hφψ hψφ hM hM
  exact ⟨h, by rw [e, sub_self]⟩

/-- Stacks formula 0EA6: `H⁰(M, 0, ψ) = Coker ψ`, `H¹(M, 0, ψ) = Ker ψ`. -/
theorem length_H_zero_left (ψ : N →ₗ[R] M) :
    Module.length R (H (0 : M →ₗ[R] N) ψ) = Module.length R (M ⧸ LinearMap.range ψ) := by
  rw [length_H, LinearMap.ker_zero, relLength_top]

theorem length_H_zero_right (ψ : N →ₗ[R] M) :
    Module.length R (H ψ (0 : M →ₗ[R] N)) = Module.length R (LinearMap.ker ψ) := by
  rw [length_H, LinearMap.range_zero, relLength_bot]

theorem herbrand_zero_left (ψ : N →ₗ[R] M) :
    herbrand (0 : M →ₗ[R] N) ψ = ((Module.length R (M ⧸ LinearMap.range ψ)).toNat : ℤ) -
      ((Module.length R (LinearMap.ker ψ)).toNat : ℤ) := by
  unfold herbrand
  rw [length_H_zero_left, length_H_zero_right]

theorem finiteCohomology_zero_left_iff (ψ : N →ₗ[R] M) :
    FiniteCohomology (0 : M →ₗ[R] N) ψ ↔
      Module.length R (M ⧸ LinearMap.range ψ) ≠ ⊤ ∧ Module.length R (LinearMap.ker ψ) ≠ ⊤ := by
  unfold FiniteCohomology
  rw [length_H_zero_left, length_H_zero_right]

/-! ## Subcomplexes and quotient complexes -/

/-- A subcomplex `(P, Q) ⊂ (M, N)` gives the short exact sequence `0 → (P,Q) → (M,N) → (M/P, N/Q) → 0`. -/
theorem ShortExact.of_submodule (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) (hφψ : φ ∘ₗ ψ = 0)
    (hψφ : ψ ∘ₗ φ = 0) (P : Submodule R M) (Q : Submodule R N)
    (hφ : P ≤ Q.comap φ) (hψ : Q ≤ P.comap ψ) :
    ShortExact (φ.restrict hφ) (ψ.restrict hψ) φ ψ (P.mapQ Q φ hφ) (Q.mapQ P ψ hψ)
      P.subtype Q.subtype P.mkQ Q.mkQ where
  i_inj := Submodule.subtype_injective _
  j_inj := Submodule.subtype_injective _
  p_surj := Submodule.mkQ_surjective _
  q_surj := Submodule.mkQ_surjective _
  exact_M := LinearMap.exact_subtype_mkQ P
  exact_N := LinearMap.exact_subtype_mkQ Q
  comm_φi := rfl
  comm_ψj := rfl
  comm_φp := rfl
  comm_ψq := rfl
  φψ := hφψ
  ψφ := hψφ

/-! ## Morphisms of complexes: kernel, image, cokernel (Stacks 0EA9) -/

section Compare

variable {M' : Type*} [AddCommGroup M'] [Module R M'] {N' : Type*} [AddCommGroup N'] [Module R N']
variable (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) (φ' : M' →ₗ[R] N') (ψ' : N' →ₗ[R] M')
variable (f : M →ₗ[R] M') (g : N →ₗ[R] N')

theorem ker_le_comap_of_comm (hφ : g ∘ₗ φ = φ' ∘ₗ f) :
    LinearMap.ker f ≤ (LinearMap.ker g).comap φ := fun x hx => by
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  have e : g (φ x) = φ' (f x) := LinearMap.congr_fun hφ x
  rw [e, LinearMap.mem_ker.mp hx, map_zero]

theorem range_le_comap_of_comm (hφ : g ∘ₗ φ = φ' ∘ₗ f) :
    LinearMap.range f ≤ (LinearMap.range g).comap φ' := by
  rintro _ ⟨x, rfl⟩
  exact ⟨φ x, LinearMap.congr_fun hφ x⟩

/-- A morphism `(f, g)` gives the short exact sequence `0 → Ker → (M, N) → Im → 0`. -/
theorem ShortExact.of_ker_range (hφψ : φ ∘ₗ ψ = 0) (hψφ : ψ ∘ₗ φ = 0)
    (hφ : g ∘ₗ φ = φ' ∘ₗ f) (hψ : f ∘ₗ ψ = ψ' ∘ₗ g) :
    ShortExact (φ.restrict (ker_le_comap_of_comm φ φ' f g hφ))
      (ψ.restrict (ker_le_comap_of_comm ψ ψ' g f hψ)) φ ψ
      (φ'.restrict (range_le_comap_of_comm φ φ' f g hφ))
      (ψ'.restrict (range_le_comap_of_comm ψ ψ' g f hψ))
      (LinearMap.ker f).subtype (LinearMap.ker g).subtype f.rangeRestrict g.rangeRestrict where
  i_inj := Submodule.subtype_injective _
  j_inj := Submodule.subtype_injective _
  p_surj := f.surjective_rangeRestrict
  q_surj := g.surjective_rangeRestrict
  exact_M := by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  exact_N := by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  comm_φi := rfl
  comm_ψj := rfl
  comm_φp := by
    ext x
    exact (LinearMap.congr_fun hφ x).symm
  comm_ψq := by
    ext x
    exact (LinearMap.congr_fun hψ x).symm
  φψ := hφψ
  ψφ := hψφ

/-- A morphism `(f, g)` of `2`-periodic complexes with `Ker f`, `Ker g`, `Coker f`, `Coker g` of finite length:
finiteness of the cohomology is equivalent on both sides, and
`e(M', N') = e(M, N) − (l Ker f − l Ker g) + (l Coker f − l Coker g)`. -/
theorem herbrand_of_map (hφψ : φ ∘ₗ ψ = 0) (hψφ : ψ ∘ₗ φ = 0) (hφψ' : φ' ∘ₗ ψ' = 0)
    (hψφ' : ψ' ∘ₗ φ' = 0) (hφ : g ∘ₗ φ = φ' ∘ₗ f) (hψ : f ∘ₗ ψ = ψ' ∘ₗ g)
    (hKf : Module.length R (LinearMap.ker f) ≠ ⊤) (hKg : Module.length R (LinearMap.ker g) ≠ ⊤)
    (hCf : Module.length R (M' ⧸ LinearMap.range f) ≠ ⊤)
    (hCg : Module.length R (N' ⧸ LinearMap.range g) ≠ ⊤) :
    (FiniteCohomology φ ψ ↔ FiniteCohomology φ' ψ') ∧
      (FiniteCohomology φ ψ → herbrand φ' ψ' = herbrand φ ψ -
        (((Module.length R (LinearMap.ker f)).toNat : ℤ) - (Module.length R (LinearMap.ker g)).toNat) +
        (((Module.length R (M' ⧸ LinearMap.range f)).toNat : ℤ) -
          (Module.length R (N' ⧸ LinearMap.range g)).toNat)) := by
  have S1 := ShortExact.of_ker_range φ ψ φ' ψ' f g hφψ hψφ hφ hψ
  have S2 := ShortExact.of_submodule φ' ψ' hφψ' hψφ' (LinearMap.range f) (LinearMap.range g)
    (range_le_comap_of_comm φ φ' f g hφ) (range_le_comap_of_comm ψ ψ' g f hψ)
  obtain ⟨hK, eK⟩ := herbrand_eq_of_length_ne_top
    (φ.restrict (ker_le_comap_of_comm φ φ' f g hφ)) (ψ.restrict (ker_le_comap_of_comm ψ ψ' g f hψ))
    (by ext x; exact LinearMap.congr_fun hφψ x) (by ext x; exact LinearMap.congr_fun hψφ x) hKf hKg
  obtain ⟨hC, eC⟩ := herbrand_eq_of_length_ne_top
    ((LinearMap.range f).mapQ (LinearMap.range g) φ' (range_le_comap_of_comm φ φ' f g hφ))
    ((LinearMap.range g).mapQ (LinearMap.range f) ψ' (range_le_comap_of_comm ψ ψ' g f hψ))
    (by
      apply Submodule.linearMap_qext
      ext x
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.zero_apply]
      have e : φ' (ψ' x) = 0 := LinearMap.congr_fun hφψ' x
      rw [e, Submodule.Quotient.mk_zero])
    (by
      apply Submodule.linearMap_qext
      ext x
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.zero_apply]
      have e : ψ' (φ' x) = 0 := LinearMap.congr_fun hψφ' x
      rw [e, Submodule.Quotient.mk_zero]) hCf hCg
  refine ⟨⟨fun h => S2.finite₂ (S1.finite₃ hK h) hC, fun h => S1.finite₂ hK (S2.finite₁ h hC)⟩,
    fun h => ?_⟩
  have hI := S1.finite₃ hK h
  have e1 := S1.herbrand_add hK hI
  have e2 := S2.herbrand_add hI hC
  rw [e2, eC, e1, eK]
  ring

/-- Stacks 0EA9: for a morphism `f` of `(2,1)`-periodic complexes with `Ker f`, `Coker f` of finite length, the
Herbrand quotients agree. -/
theorem herbrand_eq_of_map (φ ψ : M →ₗ[R] M) (φ' ψ' : M' →ₗ[R] M') (f : M →ₗ[R] M')
    (hφψ : φ ∘ₗ ψ = 0) (hψφ : ψ ∘ₗ φ = 0) (hφψ' : φ' ∘ₗ ψ' = 0)
    (hψφ' : ψ' ∘ₗ φ' = 0) (hφ : f ∘ₗ φ = φ' ∘ₗ f) (hψ : f ∘ₗ ψ = ψ' ∘ₗ f)
    (hKf : Module.length R (LinearMap.ker f) ≠ ⊤)
    (hCf : Module.length R (M' ⧸ LinearMap.range f) ≠ ⊤) :
    (FiniteCohomology φ ψ ↔ FiniteCohomology φ' ψ') ∧
      (FiniteCohomology φ ψ → herbrand φ' ψ' = herbrand φ ψ) := by
  obtain ⟨h1, h2⟩ := herbrand_of_map φ ψ φ' ψ' f f hφψ hψφ hφψ' hψφ' hφ hψ hKf hKf hCf hCf
  refine ⟨h1, fun h => ?_⟩
  rw [h2 h]; ring

end Compare

end PeriodicComplex
