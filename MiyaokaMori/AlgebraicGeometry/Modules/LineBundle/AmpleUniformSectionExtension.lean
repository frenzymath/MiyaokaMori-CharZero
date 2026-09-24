import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowIsoSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01pw

/-! # Uniform extension of finitely many local functions to global sections

**Finitely many local functions, multiplied by a common high power of the covering sections, extend to
global sections of one tensor power** (the finite, uniform version of Stacks 01PW(2)).

Statement: `X` quasi-compact quasi-separated, `L` a line bundle, `n > 0`, a finite family
`s_i ∈ Γ(X, L^{⊗n})` (`i : ι`), each `i` carrying finitely many local functions `t_{i,a} ∈ Γ(X_{s_i}, O_X)`.
Then there are `n' > 0`, `S_i ∈ Γ(X, L^{⊗n'})`, `T_{i,a} ∈ Γ(X, L^{⊗n'})` with `X_{S_i} = X_{s_i}` and
`T_{i,a}|_{X_{s_i}} = t_{i,a} · S_i|_{X_{s_i}}`.

References: the second paragraph of the proof of Stacks 01VU ("by Properties, Lemma 01PW we may write
`s_i^{e} f_{ij}` as the restriction of a global section of `L^{⊗ne}`"); Stacks 01PW(2)
(`Scheme.Modules.exists_tensorPow_section_restrict_eq`).

Proof (keeping the rearrangement isomorphisms to a minimum):
1. Write `L' := L^{⊗n}` (a line bundle). For each `(i, a)`, apply 01PW(2) to the line bundle `L'`, the
   section `s_i`, the quasi-coherent sheaf `F := L'` (line bundles are locally free, hence quasi-coherent)
   and `t_{i,a} • s_i|_{X_{s_i}} ∈ Γ(X_{s_i}, L')`: this gives `e` and `σ ∈ Γ(X, L' ⊗ L'^{⊗e})` with
   `σ|_{X_{s_i}} = (t • s_i|) ⊗ s_i^{⊗e}| = t • (s_i ⊗ s_i^{⊗e})|` (`moduleTensorSection_smul_left`,
   `moduleTensorSection_restrict`).
2. The braiding isomorphism `tensorBraidIso : L' ⊗ L'^{⊗e} ≅ L'^{⊗e} ⊗ L' = L'^{⊗(e+1)}` (on pure tensors
   `a ⊗ b ↦ b ⊗ a`) sends `σ` to `τ₀ ∈ Γ(X, L'^{⊗(e+1)})` with `τ₀|_{X_{s_i}} = t • s_i^{⊗(e+1)}|`
   (isomorphisms commute with restriction and are `Γ(X_{s_i}, O)`-linear).
3. For any `N ≥ e + 1`, write `N = (e+1) + k` and `τ := τ₀ ⊗ s_i ⊗ ⋯ ⊗ s_i` (`k` times, `extendPowSection`,
   the same right-recursion as `tensorPowSection`); by induction `τ|_{X_{s_i}} = t • s_i^{⊗N}|`
   (`exists_tensorPow_section_extension_of_le`).
4. Uniformization: `E := 1 + Σ_{i,a} e_{i,a}` (`E = 1` when `ι` is empty), `n' := n · E > 0`; for each `(i,a)`
   take `N := E` to get `T'_{i,a} ∈ Γ(X, L'^{⊗E})` with `T'|_{X_{s_i}} = t • s_i^{⊗E}|`. Let
   `θ := tensorPowMulIso L n E : L'^{⊗E} ≅ L^{⊗n'}`, `S_i := θ(s_i^{⊗E})`, `T_{i,a} := θ(T'_{i,a})`; `θ`
   commutes with restriction and is linear, so `T_{i,a}|_{X_{s_i}} = t • S_i|_{X_{s_i}}`.
5. `X_{S_i} = X_{s_i^{⊗E}}` (`nonvanishingLocus_iso`) `= X_{s_i}` (`E ≥ 1`, `nonvanishingLocus_tensorPowSection`).

Edge cases: `ι` empty: `E = 1`, `n' = n`, the families `S_i`/`T` are empty and the conclusion is vacuous.
`m i = 0`: the family `T i` is empty. `X` empty: all section rings are trivial. The requirement `n' > 0`
guarantees the `∃ n, 0 < n` of the main theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Morphisms of modules commute with restriction (elementwise form): `φ(x|_{W'}) = (φ x)|_{W'}`. -/
theorem hom_app_res' {M N : X.Modules} (φ : M ⟶ N) {W' W : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.res h x) = N.res h (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- Scalar multiplication of a pure tensor section in the first factor: `(a • s) ⊗ t = a • (s ⊗ t)`. -/
theorem moduleTensorSection_smul_left' {M N : X.Modules} {U : X.Opens} (a : Γ(X, U))
    (s : Γ(M, U)) (t : Γ(N, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection (a • s) t = a • AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t := by
  have h := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul a (1 : Γ(X, U)) s t
  rwa [one_smul, mul_one] at h

/-- Multiply `τ ∈ Γ(X, L^{⊗e})` by `k` further copies of `s`: `extendPowSection s τ k ∈ Γ(X, L^{⊗(e+k)})`
(the same right-recursion as `tensorPowSection`). -/
def extendPowSection {L : X.Modules} (s : Γ(L, ⊤)) {e : ℕ}
    (τ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤)) :
    (k : ℕ) → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (e + k), ⊤)
  | 0 => τ
  | k + 1 => AlgebraicGeometry.Scheme.Modules.moduleTensorSection (extendPowSection s τ k) s

/-- If `τ|_U = t • s^{⊗e}|_U`, then `(τ ⊗ s^{⊗k})|_U = t • s^{⊗(e+k)}|_U` (induction on `k`). -/
theorem res_extendPowSection {L : X.Modules} (s : Γ(L, ⊤)) {U : X.Opens} (t : Γ(X, U)) {e : ℕ}
    (τ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤))
    (hτ : (AlgebraicGeometry.Scheme.Modules.tensorPow L e).res (le_top : U ≤ ⊤) τ =
      t • (AlgebraicGeometry.Scheme.Modules.tensorPow L e).res (le_top : U ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e)) :
    ∀ k : ℕ,
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (e + k)).res (le_top : U ≤ ⊤)
          (extendPowSection s τ k) =
        t • (AlgebraicGeometry.Scheme.Modules.tensorPow L (e + k)).res (le_top : U ≤ ⊤)
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (e + k))
  | 0 => hτ
  | k + 1 => by
    have ih := res_extendPowSection s t τ hτ k
    -- `res (x ⊗ s) = res x ⊗ res s` (twice), then the induction hypothesis and scalar multiplication
    have h1 := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (M := AlgebraicGeometry.Scheme.Modules.tensorPow L (e + k))
      (N := L) (homOfLE (le_top : U ≤ ⊤)) (extendPowSection s τ k) s
    have h2 := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (M := AlgebraicGeometry.Scheme.Modules.tensorPow L (e + k))
      (N := L) (homOfLE (le_top : U ≤ ⊤)) (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (e + k)) s
    refine h1.trans ?_
    refine Eq.trans ?_ (congrArg (fun y => t • y) h2.symm)
    refine (congrArg (fun y => AlgebraicGeometry.Scheme.Modules.moduleTensorSection y (L.res (le_top : U ≤ ⊤) s)) ih).trans ?_
    exact moduleTensorSection_smul_left' t _ _

/-- **Extension of a single local function (01PW(2) plus the braiding isomorphism)**: `X` quasi-compact
quasi-separated, `L` a line bundle, `s ∈ Γ(X, L)`, `t ∈ Γ(X_s, O_X)`. Then there is `e` such that for every
`N ≥ e` there is `τ ∈ Γ(X, L^{⊗N})` with `τ|_{X_s} = t • s^{⊗N}|_{X_s}`. -/
theorem exists_tensorPow_section_extension_of_le [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) (t : Γ(X, L.nonvanishingLocus s)) :
    ∃ e : ℕ, ∀ N : ℕ, e ≤ N →
      ∃ τ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L N, ⊤),
        (AlgebraicGeometry.Scheme.Modules.tensorPow L N).res (le_top : L.nonvanishingLocus s ≤ ⊤) τ =
          t • (AlgebraicGeometry.Scheme.Modules.tensorPow L N).res (le_top : L.nonvanishingLocus s ≤ ⊤)
            (AlgebraicGeometry.Scheme.Modules.tensorPowSection s N) := by
  have : L.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree L
  obtain ⟨e, σ, hσ⟩ := AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_restrict_eq L s L
    (t • L.res (le_top : L.nonvanishingLocus s ≤ ⊤) s)
  refine ⟨e + 1, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  -- Step 2: the braiding isomorphism sends `σ ∈ Γ(L ⊗ L^{⊗e})` to `τ₀ ∈ Γ(L^{⊗e} ⊗ L) = Γ(L^{⊗(e+1)})`
  let θ := AlgebraicGeometry.Scheme.Modules.tensorBraidIso L (AlgebraicGeometry.Scheme.Modules.tensorPow L e)
  let τ₀ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (e + 1), ⊤) := θ.hom.app ⊤ σ
  have hτ₀ : (AlgebraicGeometry.Scheme.Modules.tensorPow L (e + 1)).res
        (le_top : L.nonvanishingLocus s ≤ ⊤) τ₀ =
      t • (AlgebraicGeometry.Scheme.Modules.tensorPow L (e + 1)).res (le_top : L.nonvanishingLocus s ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (e + 1)) := by
    -- `res τ₀ = θ (res σ)`
    have h1 : (AlgebraicGeometry.Scheme.Modules.tensorPow L (e + 1)).res
        (le_top : L.nonvanishingLocus s ≤ ⊤) τ₀ =
        θ.hom.app (L.nonvanishingLocus s)
          ((AlgebraicGeometry.Scheme.Modules.tensor L (AlgebraicGeometry.Scheme.Modules.tensorPow L e)).res
            (le_top : L.nonvanishingLocus s ≤ ⊤) σ) :=
      (hom_app_res' θ.hom (le_top : L.nonvanishingLocus s ≤ ⊤) σ).symm
    -- `res σ = t • (s ⊗ s^{⊗e})|`
    have h2 : (AlgebraicGeometry.Scheme.Modules.tensor L (AlgebraicGeometry.Scheme.Modules.tensorPow L e)).res
        (le_top : L.nonvanishingLocus s ≤ ⊤) σ =
        t • AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res (le_top : L.nonvanishingLocus s ≤ ⊤) s)
          ((AlgebraicGeometry.Scheme.Modules.tensorPow L e).res (le_top : L.nonvanishingLocus s ≤ ⊤)
            (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e)) := by
      refine hσ.trans ?_
      exact moduleTensorSection_smul_left' t _ _
    -- linearity, the formula for the braiding on pure tensors, `s^{⊗(e+1)}| = s^{⊗e}| ⊗ s|`
    have h3 := Hom.app_smul θ.hom t (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res (le_top : L.nonvanishingLocus s ≤ ⊤) s)
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L e).res (le_top : L.nonvanishingLocus s ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e)))
    have h4 := AlgebraicGeometry.Scheme.Modules.tensorBraidIso_hom_app_moduleTensorSection L
      (AlgebraicGeometry.Scheme.Modules.tensorPow L e) (L.nonvanishingLocus s)
      (L.res (le_top : L.nonvanishingLocus s ≤ ⊤) s)
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L e).res (le_top : L.nonvanishingLocus s ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e))
    have h5 := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (M := AlgebraicGeometry.Scheme.Modules.tensorPow L e) (N := L)
      (homOfLE (le_top : L.nonvanishingLocus s ≤ ⊤)) (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e) s
    refine h1.trans ?_
    refine (congrArg (θ.hom.app (L.nonvanishingLocus s)) h2).trans ?_
    refine h3.trans ?_
    refine (congrArg (fun y => t • y) h4).trans ?_
    exact congrArg (fun y => t • y) h5.symm
  exact ⟨extendPowSection s τ₀ k, res_extendPowSection s t τ₀ hτ₀ k⟩

end AlgebraicGeometry.Scheme.Modules

/-- **Uniform extension**: finitely many local functions `t_{i,a} ∈ Γ(X_{s_i}, O)`, multiplied by a common
power of the covering sections, extend to global sections `T_{i,a}` of `Γ(X, L^{⊗n'})`, where `S_i` is a
power of `s_i` (`X_{S_i} = X_{s_i}`) and `T_{i,a}|_{X_{s_i}} = t_{i,a} • S_i|_{X_{s_i}}` (the finite uniform
version of Stacks 01PW(2)). -/
theorem AlgebraicGeometry.Scheme.Modules.exists_uniform_tensorPow_extension
    {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsLineBundle] {ι : Type u} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (s : ι → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)) (m : ι → ℕ)
    (t : (i : ι) → Fin (m i) →
      Γ(X, (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i))) :
    ∃ (n' : ℕ) (_ : 0 < n') (S : ι → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n', ⊤))
      (T : (i : ι) → Fin (m i) → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n', ⊤)),
      (∀ i, (AlgebraicGeometry.Scheme.Modules.tensorPow L n').nonvanishingLocus (S i) =
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i)) ∧
      ∀ i a, (AlgebraicGeometry.Scheme.Modules.tensorPow L n').res
          (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i) ≤ ⊤)
          (T i a) =
        t i a • (AlgebraicGeometry.Scheme.Modules.tensorPow L n').res
          (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i) ≤ ⊤)
          (S i) := by
  classical
  -- Steps 1–3: choose `e i a` for each `(i, a)`
  choose e he using fun i a =>
    AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_extension_of_le
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (s i) (t i a)
  -- Step 4: the uniform exponent `E`
  let E : ℕ := 1 + ∑ i, ∑ a, e i a
  have hE : 0 < E := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 _)
  have hle : ∀ i a, e i a ≤ E := fun i a => by
    have h1 : e i a ≤ ∑ a, e i a :=
      Finset.single_le_sum (f := fun a => e i a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    have h2 : ∑ a, e i a ≤ ∑ i, ∑ a, e i a :=
      Finset.single_le_sum (f := fun i => ∑ a, e i a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact (h1.trans h2).trans (Nat.le_add_left _ 1)
  choose T' hT' using fun i a => he i a E (hle i a)
  let θ := AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L n E
  refine ⟨n * E, Nat.mul_pos hn hE,
    fun i => θ.hom.app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection (s i) E),
    fun i a => θ.hom.app ⊤ (T' i a), fun i => ?_, fun i a => ?_⟩
  · -- Step 5
    rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso θ
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection (s i) E)]
    exact AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (s i) hE
  · -- Step 4: `θ` commutes with restriction and is `Γ(X_{s_i}, O)`-linear
    have r1 := AlgebraicGeometry.Scheme.Modules.hom_app_res' θ.hom
      (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i) ≤ ⊤) (T' i a)
    have r2 := AlgebraicGeometry.Scheme.Modules.hom_app_res' θ.hom
      (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i) ≤ ⊤)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection (s i) E)
    have r3 := Hom.app_smul θ.hom (t i a)
      ((AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L n) E).res
        (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i) ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection (s i) E))
    refine r1.symm.trans ?_
    refine (congrArg (θ.hom.app _) (hT' i a)).trans ?_
    refine r3.trans ?_
    exact congrArg (fun y => t i a • y) r2

end
