import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle

/-! # Transition matrices of a trivialization cocycle form a matrix cocycle

The transition matrices of a trivialization cocycle satisfy the matrix cocycle condition: if `V` has
frames `e_α` on `U_α` with `e_{α'} = e_α · g_{αα'}` on overlaps, then `det g_{αα'}` is invertible and
`g_{αα'} g_{α'α''} = g_{αα''}` on triple intersections.

References: the transition matrices (2.7) in §2 of the paper; the standard
correspondence between locally free sheaves and cocycles (Hartshorne II Ex. 5.18, Stacks 01AJ).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace IsTrivializationCocycle

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Restricting a section twice equals restricting once along the composite inclusion (`Opens` is
thin; `Functor.map_comp`). -/
private lemma res_res_mod (V : X.Modules) {T W U : X.Opens} (h₁ : T ≤ W) (h₂ : W ≤ U)
    (s : Γ(V, U)) :
    V.presheaf.map (homOfLE h₁).op (V.presheaf.map (homOfLE h₂).op s) =
      V.presheaf.map (homOfLE (h₁.trans h₂)).op s := by
  change (V.presheaf.map (homOfLE h₂).op ≫ V.presheaf.map (homOfLE h₁).op) s = _
  rw [← V.presheaf.map_comp]
  rfl

/-- The transition relation `e_{α',j} = Σ_i (g_{αα'})_{ij} e_{α,i}` restricted to any
`T ≤ U_α ⊓ U_α'` (restriction is semilinear: `Scheme.Modules.map_smul`). -/
private lemma transition_res {ι : Type u} {r : ℕ} {V : X.Modules} {U : ι → X.Opens}
    {g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α')} {e : ∀ α, Fin r → Γ(V, U α)}
    (he : ∀ α α' (j : Fin r),
      V.presheaf.map (homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')).op (e α' j) =
        ∑ i, g α α' i j • V.presheaf.map (homOfLE (inf_le_left : U α ⊓ U α' ≤ U α)).op (e α i))
    (α α' : ι) {T : X.Opens} (hT : T ≤ U α ⊓ U α') (j : Fin r) :
    V.presheaf.map (homOfLE (hT.trans inf_le_right)).op (e α' j) =
      ∑ i, X.presheaf.map (homOfLE hT).op (g α α' i j) •
        V.presheaf.map (homOfLE (hT.trans inf_le_left)).op (e α i) := by
  have this := congrArg (V.presheaf.map (homOfLE hT).op) (he α α' j)
  rw [res_res_mod, map_sum] at this
  simp only [AlgebraicGeometry.Scheme.Modules.map_smul, res_res_mod] at this
  exact this

/-- On any open `T` contained in the three overlaps, `g_{αα'} g_{α'α''} = g_{αα''}` (coefficients
restricted to `T`): substitute two transition relations, compare with the third, and use the linear
independence of `e_α|_T` to equate coefficients. -/
private lemma mul_eq_res {ι : Type u} {r : ℕ} {V : X.Modules} {U : ι → X.Opens}
    {g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α')} {e : ∀ α, Fin r → Γ(V, U α)}
    (hfr : ∀ α, AlgebraicGeometry.Scheme.Modules.IsFrameOn V (U α) (e α))
    (he : ∀ α α' (j : Fin r),
      V.presheaf.map (homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')).op (e α' j) =
        ∑ i, g α α' i j • V.presheaf.map (homOfLE (inf_le_left : U α ⊓ U α' ≤ U α)).op (e α i))
    (α α' α'' : ι) {T : X.Opens} (h₁ : T ≤ U α ⊓ U α') (h₂ : T ≤ U α' ⊓ U α'')
    (h₃ : T ≤ U α ⊓ U α'') :
    (g α α').map (X.presheaf.map (homOfLE h₁).op).hom *
        (g α' α'').map (X.presheaf.map (homOfLE h₂).op).hom =
      (g α α'').map (X.presheaf.map (homOfLE h₃).op).hom := by
  ext i j
  have hli := (hfr α T (h₁.trans inf_le_left)).1
  have E1 := transition_res he α' α'' h₂ j
  have E3 := transition_res he α α'' h₃ j
  have key : ∑ i, X.presheaf.map (homOfLE h₃).op (g α α'' i j) •
        V.presheaf.map (homOfLE (h₁.trans inf_le_left)).op (e α i) =
      ∑ i, (∑ l, X.presheaf.map (homOfLE h₁).op (g α α' i l) *
          X.presheaf.map (homOfLE h₂).op (g α' α'' l j)) •
        V.presheaf.map (homOfLE (h₁.trans inf_le_left)).op (e α i) := by
    rw [← E3, E1]
    simp_rw [transition_res he α α' h₁, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hc := (Fintype.linearIndependent_iffₛ.mp hli) _ _ key i
  simp only [Matrix.mul_apply, Matrix.map_apply]
  exact hc.symm

/-- `g_{αα}` restricted to any `T ≤ U_α ⊓ U_α` is the identity matrix: compare
`e_{α,j} = Σ_i (g_{αα})_{ij} e_{α,i}` with `e_{α,j} = Σ_i δ_{ij} e_{α,i}`. -/
private lemma self_eq_one {ι : Type u} {r : ℕ} {V : X.Modules} {U : ι → X.Opens}
    {g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α')} {e : ∀ α, Fin r → Γ(V, U α)}
    (hfr : ∀ α, AlgebraicGeometry.Scheme.Modules.IsFrameOn V (U α) (e α))
    (he : ∀ α α' (j : Fin r),
      V.presheaf.map (homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')).op (e α' j) =
        ∑ i, g α α' i j • V.presheaf.map (homOfLE (inf_le_left : U α ⊓ U α' ≤ U α)).op (e α i))
    (α : ι) {T : X.Opens} (hT : T ≤ U α ⊓ U α) :
    (g α α).map (X.presheaf.map (homOfLE hT).op).hom = 1 := by
  ext i j
  have hli := (hfr α T (hT.trans inf_le_left)).1
  have E := transition_res he α α hT j
  have key : ∑ i, X.presheaf.map (homOfLE hT).op (g α α i j) •
        V.presheaf.map (homOfLE (hT.trans inf_le_left)).op (e α i) =
      ∑ i, (1 : Matrix (Fin r) (Fin r) Γ(X, T)) i j •
        V.presheaf.map (homOfLE (hT.trans inf_le_left)).op (e α i) := by
    rw [← E]
    simp [Matrix.one_apply, ite_smul]
  have hc := (Fintype.linearIndependent_iffₛ.mp hli) _ _ key i
  simpa only [Matrix.map_apply] using hc

end IsTrivializationCocycle

/-- The transition matrices of a trivialization cocycle (`IsTrivializationCocycle V U g`: `V` has a
frame `e_α` on every `U_α`, and `e_{α',j} = Σ_i (g_{αα'})_{ij} e_{α,i}` on overlaps) form a matrix
cocycle (`IsMatrixCocycle U g`).

Reference: Hartshorne II Ex. 5.18(a) (locally free sheaves ↔ 1-cocycles of transition matrices).

Proof sketch. Write `W = U_α ⊓ U_α'`, `T = U_α ⊓ U_α' ⊓ U_α''`; all sections are restricted to the
open in question; restriction is `Γ(X, ·)`-semilinear (`Scheme.Modules.map_smul`) and composites of
restrictions are restrictions along the composite inclusion (`Functor.map_comp`; `Opens` is thin).

(1) Cocycle condition. On `T`: restrict the `α'α''` transition relation,
  `e_{α'',j} = Σ_l (g_{α'α''})_{lj} e_{α',l}`, substitute the restricted `αα'` relation
  `e_{α',l} = Σ_i (g_{αα'})_{il} e_{α,i}`, and get
  `e_{α'',j} = Σ_i (g_{αα'} g_{α'α''})_{ij} e_{α,i}` (`Finset.smul_sum`, `Finset.sum_comm`, `smul_smul`,
  `Matrix.mul_apply`). The restricted `αα''` relation gives `e_{α'',j} = Σ_i (g_{αα''})_{ij} e_{α,i}`.
  By `IsFrameOn V (U α) (e α)` with `W' = T ≤ U_α`, the restricted `e_{α,i}` are linearly independent
  over `Γ(X, T)`, so the coefficients agree (`Fintype.linearIndependent_iffₛ`). In Lean this is the
  general lemma `mul_eq_res` for any `T` inside the three overlaps; the second clause of
  `IsMatrixCocycle` is the case `T = U_α ⊓ U_α' ⊓ U_α''`.

(2) Invertibility of the determinant. On `W`: `mul_eq_res` for `(α, α', α)` and `T = W` gives
  `g_{αα'} · g_{α'α}|_W = g_{αα}|_W`; `g_{αα}` restricted to any `T ≤ U_α ⊓ U_α` is the identity
  (`self_eq_one`), and restriction along `le_refl` is the identity (`homOfLE_refl`, `Functor.map_id`),
  so `g_{αα'} g_{α'α}|_W = 1`; `Matrix.det_mul` gives `det g_{αα'} · det (g_{α'α}|_W) = 1`, i.e.
  `IsUnit (g α α').det` (`IsUnit.of_mul_eq_one`). -/
theorem IsTrivializationCocycle.isMatrixCocycle {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} {r : ℕ}
    {V : X.Modules} {U : ι → X.Opens} {g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α')}
    (h : IsTrivializationCocycle V U g) : IsMatrixCocycle U g := by
  obtain ⟨e, hfr, he⟩ := h
  refine ⟨fun α α' => ?_, fun α α' α'' => IsTrivializationCocycle.mul_eq_res hfr he α α' α'' _ _ _⟩
  have h1 := IsTrivializationCocycle.mul_eq_res hfr he α α' α (le_refl (U α ⊓ U α'))
    (le_inf inf_le_right inf_le_left) (le_inf inf_le_left inf_le_left)
  rw [IsTrivializationCocycle.self_eq_one hfr he α] at h1
  have hid : (g α α').map (X.presheaf.map (homOfLE (le_refl (U α ⊓ U α'))).op).hom = g α α' := by
    ext i j
    simp [Matrix.map_apply]
  rw [hid] at h1
  have hdet := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  exact IsUnit.of_mul_eq_one _ hdet

end
