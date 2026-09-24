import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesQuasicoherentClosure
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeBiproduct
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.Stacks08aa

/-! # Euler characteristic of a finite direct sum of copies

`χ(X, M^{⊕ n}) = n · χ(X, M)` for a coherent `M` on a proper `k`-scheme: the `n`-fold direct sum is an
iterated split extension, and `χ` is additive on short exact sequences (Stacks 08AA). Used in Stacks 0AYT
(`χ(G^{⊕ n}) = n χ(G)`).

Coherence of `M^{⊕ n}`: quasi-coherence of finite biproducts (`isQuasicoherent_biproduct_of_fintype`)
and finite type of finite biproducts (`isFiniteType_biproduct`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `M^{⊕ n}` is coherent when `M` is (quasi-coherence: `isQuasicoherent_biproduct_of_fintype`;
finite type: `isFiniteType_biproduct`). -/
theorem isCoherent_pow (M : X.Modules) [hM : M.IsCoherent] (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pow M n).IsCoherent :=
  ⟨isQuasicoherent_biproduct_of_fintype (fun _ : Fin n => M) (fun _ => hM.quasicoherent),
    isFiniteType_biproduct (fun _ : Fin n => M) (fun _ => hM.finiteType)⟩

/-- `M^{⊕ 0}` (the empty biproduct) is a zero object. -/
theorem isZero_pow_zero (M : X.Modules) : IsZero (AlgebraicGeometry.Scheme.Modules.pow M 0) := by
  refine ⟨fun Y => ⟨⟨⟨0⟩, fun a => ?_⟩⟩, fun Y => ⟨⟨⟨0⟩, fun a => ?_⟩⟩⟩
  · exact biproduct.hom_ext' (f := fun _ : Fin 0 => M) a 0 (fun j => j.elim0)
  · exact biproduct.hom_ext (f := fun _ : Fin 0 => M) a 0 (fun j => j.elim0)

/-- The short complex `M → M^{⊕ (n+1)} → M^{⊕ n}` (inclusion of the last summand, projection onto the
first `n` summands). -/
def powSuccShortComplex (M : X.Modules) (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (biproduct.ι (fun _ : Fin (n + 1) => M) (Fin.last n))
    (biproduct.lift (fun j : Fin n => biproduct.π (fun _ : Fin (n + 1) => M) j.castSucc)) (by
      apply biproduct.hom_ext
      intro j
      simp only [Category.assoc, biproduct.lift_π, zero_comp]
      exact biproduct.ι_π_ne (fun _ : Fin (n + 1) => M) (Fin.ne_of_gt (Fin.castSucc_lt_last j)))

/-- `powSuccShortComplex` is split (retraction: projection onto the last summand; section: inclusion
of the first `n` summands). -/
def powSuccSplitting (M : X.Modules) (n : ℕ) : (powSuccShortComplex M n).Splitting where
  r := biproduct.π (fun _ : Fin (n + 1) => M) (Fin.last n)
  s := biproduct.desc (fun j : Fin n => biproduct.ι (fun _ : Fin (n + 1) => M) j.castSucc)
  f_r := by simp [powSuccShortComplex]
  s_g := by
    show biproduct.desc (fun j : Fin n => biproduct.ι (fun _ : Fin (n + 1) => M) j.castSucc) ≫
        biproduct.lift (fun j : Fin n => biproduct.π (fun _ : Fin (n + 1) => M) j.castSucc) = 𝟙 _
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.id_comp]
    by_cases h : j = k
    · subst h
      simp
    · rw [biproduct.ι_π_ne _ (fun h' => h (Fin.castSucc_inj.mp h')), biproduct.ι_π_ne _ h]
  id := by
    show biproduct.π (fun _ : Fin (n + 1) => M) (Fin.last n) ≫
          biproduct.ι (fun _ : Fin (n + 1) => M) (Fin.last n) +
        biproduct.lift (fun j : Fin n => biproduct.π (fun _ : Fin (n + 1) => M) j.castSucc) ≫
          biproduct.desc (fun j : Fin n => biproduct.ι (fun _ : Fin (n + 1) => M) j.castSucc) = 𝟙 _
    have h := biproduct.total (f := fun _ : Fin (n + 1) => M)
    rw [Fin.sum_univ_castSucc] at h
    rw [biproduct.lift_desc]
    exact (add_comm _ _).trans h

/-- `powSuccShortComplex` is short exact. -/
theorem powSuccShortComplex_shortExact (M : X.Modules) (n : ℕ) :
    (powSuccShortComplex M n).ShortExact :=
  (powSuccSplitting M n).shortExact

end AlgebraicGeometry.Scheme.Modules

/-- **`χ(M^{⊕ n}) = n · χ(M)`** for `X` proper over `k` and `M` coherent. Induction on `n` with the split
short exact sequences `0 → M → M^{⊕(n+1)} → M^{⊕ n} → 0` and Stacks 08AA
(`sheafEulerCharacteristic_additive`); the base case uses `0 → M → M → M^{⊕ 0} → 0` (`M^{⊕ 0}` is a zero
object) to get `χ(M^{⊕ 0}) = 0`. All three terms are coherent (`isCoherent_pow`). -/
theorem AlgebraicGeometry.sheafEulerCharacteristic_pow {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (M : X.Modules) [M.IsCoherent] (n : ℕ) :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (AlgebraicGeometry.Scheme.Modules.pow M n) =
      n * AlgebraicGeometry.sheafEulerCharacteristic (k := k) X M := by
  induction n with
  | zero =>
    let S : ShortComplex X.Modules :=
      ShortComplex.mk (𝟙 M) (0 : M ⟶ AlgebraicGeometry.Scheme.Modules.pow M 0) (by simp)
    have hS : S.ShortExact :=
      (ShortComplex.Splitting.ofIsIsoOfIsZero (S := S) inferInstance
        (AlgebraicGeometry.Scheme.Modules.isZero_pow_zero M)).shortExact
    have h1 : S.X₁.IsCoherent := ‹M.IsCoherent›
    have h2 : S.X₂.IsCoherent := ‹M.IsCoherent›
    have h3 : S.X₃.IsCoherent := AlgebraicGeometry.Scheme.Modules.isCoherent_pow M 0
    have h := AlgebraicGeometry.sheafEulerCharacteristic_additive X hX S hS
    change AlgebraicGeometry.sheafEulerCharacteristic (k := k) X M =
      AlgebraicGeometry.sheafEulerCharacteristic (k := k) X M +
        AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.Scheme.Modules.pow M 0) at h
    push_cast
    linarith
  | succ n ih =>
    have h1 : (AlgebraicGeometry.Scheme.Modules.powSuccShortComplex M n).X₁.IsCoherent :=
      ‹M.IsCoherent›
    have h2 : (AlgebraicGeometry.Scheme.Modules.powSuccShortComplex M n).X₂.IsCoherent :=
      AlgebraicGeometry.Scheme.Modules.isCoherent_pow M (n + 1)
    have h3 : (AlgebraicGeometry.Scheme.Modules.powSuccShortComplex M n).X₃.IsCoherent :=
      AlgebraicGeometry.Scheme.Modules.isCoherent_pow M n
    have h := AlgebraicGeometry.sheafEulerCharacteristic_additive X hX _
      (AlgebraicGeometry.Scheme.Modules.powSuccShortComplex_shortExact M n)
    change AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
        (AlgebraicGeometry.Scheme.Modules.pow M (n + 1)) =
      AlgebraicGeometry.sheafEulerCharacteristic (k := k) X M +
        AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.Scheme.Modules.pow M n) at h
    rw [h, ih]
    push_cast
    ring

end
