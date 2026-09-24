import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.InvertibleOfLocalFreeRankOne
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible

/-! # An invertible module with a finite free resolution is free

A consequence of determinants and finite free resolutions (Stacks 0FJB/0AFX/0AFY): an invertible
`R`-module `L` admitting a finite free resolution of finite length is free (equivalently, the class
of `det L = L` in `Pic` is trivial).

References: Stacks 0AFY (`more-algebra-lemma-perfect-to-K-group`, the passage "cut the acyclic
complex into short exact sequences and split them one by one"), 0AFX (`more-algebra-lemma-det`),
0FJB (`more-algebra-lemma-det-ses`).

Instead of following Stacks literally (0FJB, multiplicativity of exterior powers on short exact
sequences → 0AFX, `det : K₀ → Pic` → 0AFY), which would require the multiplicativity of `det` for
short exact sequences of finite projective modules, the proof here takes an equivalent, shorter route:

1. `L` invertible ⇒ `L` projective (an instance of Mathlib's `Module.Invertible`);
2. going down the resolution, split each `0 → ker → C_m → im → 0` (a surjection onto a projective
   module has a right inverse), so every `im(d_{m+1})` is projective and finite;
3. by induction from the top (the `C_n` end) every `im(d_{m+1})` is **stably free**, hence so is `L`;
4. Mathlib's `Module.free_of_isStablyFree_of_invertible` (whose proof is the determinant argument of
   0FJB/0AFX: cofactor expansion of the top exterior power along the `L`-component) gives that `L` is free.

Steps 3 and 4 together are the descending induction of Stacks 0AFY plus taking determinants as in
0AFX, with the determinant half delegated to Mathlib's "finite stably free + invertible ⇒ free".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped TensorProduct

namespace Module

/-- Splitting lemma: if `p : F →ₗ[R] M` is surjective and `M` is projective, then `F ≃ₗ[R] M × ker p`.

Proof: `M` projective gives a right inverse `s : M →ₗ[R] F` (`LinearMap.exists_rightInverse_of_surjective`);
take `x ↦ (p x, x - s (p x))` (the second component lies in `ker p` since `p (s (p x)) = p x`), with
inverse `(m, k) ↦ s m + k`. -/
theorem nonempty_prodKerEquiv {R : Type u} [CommRing R] {F M : Type*} [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (p : F →ₗ[R] M) (hp : Function.Surjective p) :
    Nonempty (F ≃ₗ[R] M × (LinearMap.ker p)) := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  have hps : ∀ m, p (s m) = m := fun m => by
    simpa using DFunLike.congr_fun hs m
  have hmem : ∀ x : F, ((LinearMap.id : F →ₗ[R] F) - s ∘ₗ p) x ∈ LinearMap.ker p := by
    intro x
    simp [LinearMap.mem_ker, hps]
  refine ⟨LinearEquiv.ofLinearMap
    (LinearMap.prod p (((LinearMap.id : F →ₗ[R] F) - s ∘ₗ p).codRestrict (LinearMap.ker p) hmem))
    (LinearMap.coprod s (LinearMap.ker p).subtype) ?_ ?_⟩
  · apply LinearMap.ext
    rintro ⟨m, k, hk⟩
    have hk' : p k = 0 := hk
    apply Prod.ext
    · simp [hps, hk']
    · apply Subtype.ext
      simp [hps, hk']
  · apply LinearMap.ext
    intro x
    simp

/-- Induction step for stable freeness: if `K × K' ≅ F` with `F` finite free and `K'` finite and stably
free, then `K` is stably free.

Proof: let `P` witness the stable freeness of `K'` (`P` finite free, `K' × P` free); then
`K × (K' × P) ≅ (K × K') × P ≅ F × P` is free and `K' × P` is finite free, so `K` is stably free
(`Module.IsStablyFree.of_free_prod`). -/
theorem isStablyFree_of_prodEquiv {R : Type u} [CommRing R] {K K' F : Type*}
    [AddCommGroup K] [Module R K] [AddCommGroup K'] [Module R K']
    [AddCommGroup F] [Module R F]
    [Module.Finite R K'] [Module.IsStablyFree R K']
    [Module.Finite R F] [Module.Free R F]
    (e : (K × K') ≃ₗ[R] F) : Module.IsStablyFree R K := by
  obtain ⟨P, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R K'
  have φ : (K × (K' × P)) ≃ₗ[R] F × P :=
    (LinearEquiv.prodAssoc R K K' P).symm.trans (e.prodCongr (LinearEquiv.refl R P))
  have : Module.Free R (K × (K' × P)) := Module.Free.of_equiv φ.symm
  exact Module.IsStablyFree.of_free_prod R K (K' × P)

end Module

/-- Stacks 0AFY/0AFX applied to an invertible module: if an invertible `R`-module `L` has a finite
free resolution of finite length `0 → C_n → ⋯ → C_1 → C_0 →ε L → 0` (`C` exact in positive degrees,
`ker ε = im d₁`), then `L` is free (i.e. its class in `Pic R` is trivial).

Reference: Stacks 0AFY (cutting an acyclic finite projective complex into short exact sequences,
descending induction) and 0AFX (`det : K₀(R) → Pic(R)`). Note that `R` need **not** be local (the
result is applied to `Localization.Away f`, which is not local).

Proof sketch (matching the Lean proof step by step):

* Put `S m := im(d_{m+1} : C_{m+1} → C_m) ⊆ C_m`. From `hex` (exactness at `m+1`), `S (m+1) = ker(d_{m+1})`,
  and from `hker`, `S 0 = ker ε`. So the kernel of `C_{m+1} ↠ S m` is `S (m+1)` and the kernel of
  `C_0 ↠ L` is `S 0`.
* (Upward induction, projectivity) `L` invertible ⇒ projective, so `C_0 ≅ L × S 0`; `C_0` free ⇒
  projective ⇒ `S 0` projective; inductively `S m` projective ⇒ `C_{m+1} ≅ S m × S (m+1)` ⇒ `S (m+1)`
  projective (`nonempty_prodKerEquiv`).
* (Boundary) `C_i = 0` for `i > n`, so `S m = im(d_{m+1}) = 0` for `m ≥ n`; in particular `S n = 0` is
  free and stably free.
* (Downward induction, stable freeness) From `S m × S (m+1) ≅ C_{m+1}` finite free and `S (m+1)`
  finite stably free, `S m` is stably free (`isStablyFree_of_prodEquiv`); going down from `m = n` to
  `m = 0`, `S 0` is stably free, and from `L × S 0 ≅ C_0` so is `L`.
* (Determinant) Mathlib's `Module.free_of_isStablyFree_of_invertible`: finite stably free + invertible
  ⇒ free. Internally this is the determinant argument of 0AFX (cofactor expansion of
  `⋀^{n+1}(L × R^n)` along the `L`-component gives `R ≃ₗ L`).

Edge cases: for `R = 0` all modules vanish and the statement is trivial
(`Module.free_of_isStablyFree_of_invertible` itself splits on `subsingleton_or_nontrivial R`); for
`n = 0` the base case of the downward induction gives `S 0 = 0`, `C_0 ≅ L`, and `L` is free. -/
theorem Module.Invertible.free_of_finite_free_resolution {R : Type u} [CommRing R]
    (L : Type u) [AddCommGroup L] [Module R L] [Module.Invertible R L]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (hfree : ∀ i, Module.Free R (C.X i)) (hfin : ∀ i, Module.Finite R (C.X i))
    (hbd : ∀ i, n < i → Subsingleton (C.X i))
    (hex : ∀ i, C.ExactAt (i + 1))
    (ε : C.X 0 →ₗ[R] L) (hε : Function.Surjective ε)
    (hker : LinearMap.ker ε = LinearMap.range (C.d 1 0).hom) :
    Module.Free R L := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : (m : ℕ) → Submodule R (C.X m),
      ∀ m, S m = LinearMap.range (C.d (m + 1) m).hom := ⟨_, fun _ => rfl⟩
  -- exactness: S (m+1) = ker d_{m+1}
  have hexr : ∀ m : ℕ, LinearMap.range (C.d (m + 1 + 1) (m + 1)).hom
      = LinearMap.ker (C.d (m + 1) m).hom := fun m =>
    ((HomologicalComplex.exactAt_iff' C (m + 1 + 1) (m + 1) m (by simp) (by simp)).1
      (hex m)).moduleCat_range_eq_ker
  have hSfin : ∀ m, Module.Finite R (S m) := by
    intro m
    rw [hSdef]
    have := hfin (m + 1)
    infer_instance
  -- the short exact sequence 0 → S (m+1) → C_{m+1} → S m → 0 splits when S m is projective
  have hsplit : ∀ m : ℕ, Module.Projective R (S m) →
      Nonempty ((C.X (m + 1)) ≃ₗ[R] (S m) × (S (m + 1))) := by
    intro m hproj
    have hmem : ∀ x : C.X (m + 1), (C.d (m + 1) m).hom x ∈ S m := by
      intro x; rw [hSdef]; exact ⟨x, rfl⟩
    have hqsurj : Function.Surjective
        (((C.d (m + 1) m).hom).codRestrict (S m) hmem) := by
      rintro ⟨y, hy⟩
      rw [hSdef] at hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩
    have hqker : LinearMap.ker (((C.d (m + 1) m).hom).codRestrict (S m) hmem) = S (m + 1) := by
      rw [LinearMap.ker_codRestrict, hSdef (m + 1), hexr m]
    obtain ⟨e⟩ := Module.nonempty_prodKerEquiv _ hqsurj
    exact ⟨e.trans ((LinearEquiv.refl R _).prodCongr (LinearEquiv.ofEq _ _ hqker))⟩
  have hsplit0 : Nonempty ((C.X 0) ≃ₗ[R] L × (S 0)) := by
    obtain ⟨e⟩ := Module.nonempty_prodKerEquiv ε hε
    refine ⟨e.trans ((LinearEquiv.refl R L).prodCongr (LinearEquiv.ofEq _ _ ?_))⟩
    rw [hSdef]; exact hker
  -- upward induction: every S m is projective
  have hproj : ∀ m, Module.Projective R (S m) := by
    intro m
    induction m with
    | zero =>
      obtain ⟨e⟩ := hsplit0
      have := hfree 0
      have : Module.Projective R (L × (S 0)) := Module.Projective.of_equiv' e
      exact Module.Projective.of_split (LinearMap.inr R L (S 0))
        (LinearMap.snd R L (S 0)) (by ext x; simp)
    | succ m ih =>
      obtain ⟨e⟩ := hsplit m ih
      have := hfree (m + 1)
      have : Module.Projective R ((S m) × (S (m + 1))) := Module.Projective.of_equiv' e
      exact Module.Projective.of_split (LinearMap.inr R (S m) (S (m + 1)))
        (LinearMap.snd R (S m) (S (m + 1))) (by ext x; simp)
  -- downward induction: every S m is stably free (descending from m = n)
  have hsf : ∀ k m : ℕ, m + k = n → Module.IsStablyFree R (S m) := by
    intro k
    induction k with
    | zero =>
      intro m hm
      have hsub : Subsingleton (S m) := by
        rw [hSdef]
        have := hbd (m + 1) (by omega)
        constructor
        rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
        exact Subtype.ext (by rw [Subsingleton.elim x y])
      infer_instance
    | succ k ih =>
      intro m hm
      have h1 : Module.IsStablyFree R (S (m + 1)) := ih (m + 1) (by omega)
      have h2 := hSfin (m + 1)
      have h3 := hfree (m + 1)
      have h4 := hfin (m + 1)
      obtain ⟨e⟩ := hsplit m (hproj m)
      exact Module.isStablyFree_of_prodEquiv e.symm
  have h0 : Module.IsStablyFree R (S 0) := hsf n 0 (by omega)
  have h1 := hSfin 0
  have h2 := hfree 0
  have h3 := hfin 0
  obtain ⟨e⟩ := hsplit0
  have : Module.IsStablyFree R L := Module.isStablyFree_of_prodEquiv e.symm
  exact Module.free_of_isStablyFree_of_invertible R L

end
