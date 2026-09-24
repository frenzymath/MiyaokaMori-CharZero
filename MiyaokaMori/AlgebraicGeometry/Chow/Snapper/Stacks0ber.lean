import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Cohomology.SnapperPolynomial
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bem
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bep

/-! # Additivity of the Snapper intersection number

Stacks 0BER: the intersection number `(L_1⋯L_d·X)` defined through `χ` is additive in each `L_i`:
if `L_i ≅ L_i' ⊗ L_i''` then the intersection number is the sum of the two.

Source: Stacks 0BER; Lazarsfeld, Positivity in Algebraic Geometry I, §1.1.C, footnote 7; used in the
proof that the Snapper intersection number equals the Chow one.

## Route

`snapperIntersection X hX hd L` is *defined* (Stacks0bep) as the d-fold mixed difference at the origin
`∑_{S ⊆ Fin d} (-1)^{d-|S|} χ(X, ⨂_{j∈S} L_j)`. Write `L₁ := update L i L'`, `L₂ := update L i L''`.

1. **One application of Stacks 0BEM** (`exists_snapper_mvPolynomial`) to the coherent sheaf `O_X` and the
   `d+1` line bundles `Fin.cons L'' L₁ : Fin (d+1) → X.Modules` gives a polynomial `P ∈ ℚ[x_0,…,x_d]` of total
   degree `≤ d` with `χ(X, L''^{m} ⊗ ⨂_j L₁_j^{n_j}) = P(m, n)` for all `(m, n) ∈ ℤ × ℤ^d`
   (`hchain`: the `foldl` over `finRange (d+1)` splits off its first factor by `List.finRange_succ`).
2. **Algebra** (`mixedDifference_cons_eq_zero`): for any `P` of total degree `≤ d` in `d+1` variables,
   `∑_{S ⊆ Fin d} (-1)^{d-|S|} (P(1, 1_S) − P(0, 1_S)) = 0`. Indeed, expanding `P` into monomials `x^u` and using
   `∑_S (-1)^{d-|S|} ∏_j 1_S(j)^{u_j} = ∏_j (1 − 0^{u_j})` (`Finset.prod_add`), the coefficient of `x^u` in the sum is
   `∏_{j<d+1} (1 − 0^{u_j})`, which vanishes because `∑_j u_j ≤ d < d+1` forces some `u_j = 0`.
3. **Geometry** (isomorphisms of tensor chains, `chain_cons_insert` / `chain_congr_start` / `chain_congr_fun`,
   built from the symmetric monoidal structure on `X.Modules` via `tensorIsoTensorObj`; the associator and the
   two congruence isomorphisms are reused from `Stacks0892_TensorPowIsos`):
   for `i ∈ S`: `O ⊗ L''^1 ⊗ ⨂_{j∈S} L₁_j ≅ ⨂_{j∈S} L_j` (uses `e : L_i ≅ L' ⊗ L''`);
   for `i ∉ S`: `O ⊗ L''^1 ⊗ ⨂_{j∈S} L₁_j ≅ ⨂_{j∈S∪{i}} L₂_j`, and `⨂_{j∈S} L_j = ⨂_{j∈S} L₁_j = ⨂_{j∈S} L₂_j`
   (the `i`-th factor is `L^0 = O_X` for every `L`, definitionally); `O ⊗ L''^0 ⊗ M ≅ M`.
   `χ` is invariant under isomorphism (`sheafEulerCharacteristic_eq_of_iso`, valid without any finiteness).
4. Split every sum over `Finset (Fin d)` as `∑_{S ⊆ univ \ {i}} (f S + f (insert i S))` (`Finset.sum_powerset_insert`);
   with `(-1)^{d-|S|} = -(-1)^{d-|S ∪ {i}|}`, step 2 becomes termwise exactly
   `(L) = (L₁) + (L₂)`, i.e. the statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Commutativity of `Modules.tensor` up to isomorphism (the braiding of `X.Modules`). -/
noncomputable def tensorCommIso (A B : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor A B ≅ AlgebraicGeometry.Scheme.Modules.tensor B A :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B ≪≫
    CategoryTheory.BraidedCategory.braiding (C := X.Modules) A B ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B A).symm

/-- `(G ⊗ M) ⊗ B ≅ (G ⊗ B) ⊗ M`. -/
noncomputable def tensorSwapIso (G M B : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensor G M) B ≅
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensor G B) M :=
  tensorAssocIso G M B ≪≫ tensorCongrRightIso G (tensorCommIso M B) ≪≫ (tensorAssocIso G B M).symm

/-- Changing the starting object of a tensor chain by an isomorphism. -/
theorem chain_congr_start {d : ℕ} (f : Fin d → X.Modules) (l : List (Fin d)) :
    ∀ {G G' : X.Modules}, (G ≅ G') →
      Nonempty (l.foldl (fun (G : X.Modules) (j : Fin d) => AlgebraicGeometry.Scheme.Modules.tensor G (f j)) G ≅
        l.foldl (fun (G : X.Modules) (j : Fin d) => AlgebraicGeometry.Scheme.Modules.tensor G (f j)) G') := by
  induction l with
  | nil => intro G G' e; exact ⟨e⟩
  | cons j l ih =>
    intro G G' e
    simp only [List.foldl_cons]
    exact ih (tensorCongrLeftIso e (f j))

/-- Two tensor chains with the same factors along the list are equal. -/
theorem chain_congr_fun {d : ℕ} (f g : Fin d → X.Modules) (l : List (Fin d)) (h : ∀ j ∈ l, f j = g j)
    (G : X.Modules) :
    l.foldl (fun (G : X.Modules) (j : Fin d) => AlgebraicGeometry.Scheme.Modules.tensor G (f j)) G =
      l.foldl (fun (G : X.Modules) (j : Fin d) => AlgebraicGeometry.Scheme.Modules.tensor G (g j)) G := by
  induction l generalizing G with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [h j (List.mem_cons_self ..)]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

/-- Absorbing an extra factor `M` (placed at the start of the chain) into the `i`-th factor:
if `f = g` away from `i` and `M ⊗ f i ≅ g i`, then `(G ⊗ M) ⊗ ⨂_{j∈l} f j ≅ G ⊗ ⨂_{j∈l} g j`
for any list `l` without repetitions containing `i`. -/
theorem chain_cons_insert {d : ℕ} (i : Fin d) (f g : Fin d → X.Modules) (M : X.Modules)
    (e : AlgebraicGeometry.Scheme.Modules.tensor M (f i) ≅ g i) (l : List (Fin d)) :
    l.Nodup → i ∈ l → (∀ j ∈ l, j ≠ i → f j = g j) → ∀ G : X.Modules,
      Nonempty (l.foldl (fun (G : X.Modules) (j : Fin d) => AlgebraicGeometry.Scheme.Modules.tensor G (f j))
          (AlgebraicGeometry.Scheme.Modules.tensor G M) ≅
        l.foldl (fun (G : X.Modules) (j : Fin d) => AlgebraicGeometry.Scheme.Modules.tensor G (g j)) G) := by
  induction l with
  | nil => intro _ hi; exact absurd hi (by simp)
  | cons j l ih =>
    intro hnd hi hfg G
    obtain ⟨hjl, hl⟩ := List.nodup_cons.mp hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hil
    · -- the head is `i`: reassociate, use `e`, and `i` does not occur in the tail
      have hfg' : ∀ j ∈ l, f j = g j := fun j hj =>
        hfg j (List.mem_cons_of_mem _ hj) (fun h => hjl (h ▸ hj))
      rw [chain_congr_fun f g l hfg']
      exact chain_congr_start g l (tensorAssocIso G M (f i) ≪≫ tensorCongrRightIso G e)
    · -- the head is some `j ≠ i`: swap `M` past `f j = g j` and use the induction hypothesis
      have hji : j ≠ i := fun h => hjl (h ▸ hil)
      obtain ⟨e₀⟩ := chain_congr_start f l (tensorSwapIso G M (f j))
      obtain ⟨e₁⟩ := ih hl hil (fun j hj hne => hfg j (List.mem_cons_of_mem _ hj) hne)
        (AlgebraicGeometry.Scheme.Modules.tensor G (f j))
      rw [← hfg j (List.mem_cons_self ..) hji]
      exact ⟨e₀ ≪≫ e₁⟩

end AlgebraicGeometry.Scheme.Modules

section MixedDifference

/-- `∏_i (1_{i∈t})^{u i} = ∏_{i ∉ t} 0^{u i}` (with `0^0 = 1`). -/
private theorem prod_indicator_pow {d : ℕ} (u : Fin d → ℕ) (t : Finset (Fin d)) :
    (∏ i : Fin d, (if i ∈ t then (1 : ℚ) else 0) ^ u i)
      = ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i := by
  rw [← Finset.prod_sdiff (Finset.subset_univ t)]
  have h1 : (∏ i ∈ t, (if i ∈ t then (1 : ℚ) else 0) ^ u i) = 1 :=
    Finset.prod_eq_one fun i hi => by rw [if_pos hi, one_pow]
  have h2 : (∏ i ∈ Finset.univ \ t, (if i ∈ t then (1 : ℚ) else 0) ^ u i)
      = ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i :=
    Finset.prod_congr rfl fun i hi => by rw [if_neg (Finset.mem_sdiff.mp hi).2]
  rw [h1, h2, mul_one]

/-- The mixed difference of a monomial:
`∑_{S ⊆ Fin d} (-1)^{d-|S|} ∏_i (1_{i∈S})^{u i} = ∏_i (1 - 0^{u i})` (`Finset.prod_add` with
`f i = 1`, `g i = -0^{u i}`). Same proof as in `Stacks0bepLemmas`, for a function `u`. -/
private theorem alternating_sum_indicator_prod {d : ℕ} (u : Fin d → ℕ) :
    (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        ∏ i : Fin d, (if i ∈ S then (1 : ℚ) else 0) ^ u i)
      = ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) := by
  have key := Finset.prod_add (fun _ : Fin d => (1 : ℚ)) (fun i => -((0 : ℚ) ^ u i)) Finset.univ
  rw [Finset.powerset_univ] at key
  have hl : (∏ i : Fin d, ((1 : ℚ) + -((0 : ℚ) ^ u i))) = ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) :=
    Finset.prod_congr rfl fun i _ => by ring
  have hr : ∀ t : Finset (Fin d),
      ((∏ _i ∈ t, (1 : ℚ)) * ∏ i ∈ Finset.univ \ t, -((0 : ℚ) ^ u i))
        = (-1 : ℚ) ^ (d - t.card) * ∏ i : Fin d, (if i ∈ t then (1 : ℚ) else 0) ^ u i := by
    intro t
    have hsplit : (∏ i ∈ Finset.univ \ t, -((0 : ℚ) ^ u i))
        = (∏ _i ∈ Finset.univ \ t, (-1 : ℚ)) * ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [Finset.prod_const_one, one_mul, prod_indicator_pow, hsplit, Finset.prod_const,
      Finset.card_univ_sdiff, Fintype.card_fin]
  rw [← hl, key]
  exact Finset.sum_congr rfl fun t _ => (hr t).symm

/-- **Algebraic core of Stacks 0BER.** If `P ∈ ℚ[x_0, …, x_d]` has total degree `≤ d`, then the
`(d+1)`-fold mixed difference at the origin vanishes; written with the first variable separated:
`∑_{S ⊆ Fin d} (-1)^{d-|S|} (P(1, 1_S) − P(0, 1_S)) = 0`.
Proof: expand `P` into monomials; by `alternating_sum_indicator_prod` the coefficient of `x^u` is
`(1 − 0^{u 0}) ∏_{j<d} (1 − 0^{u (j+1)}) = ∏_{j<d+1} (1 − 0^{u j})`, and `∑_j u_j ≤ d < d + 1` forces some
`u_j = 0`, so every such product is `0`. -/
theorem MvPolynomial.mixedDifference_cons_eq_zero {d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℚ)
    (hP : P.totalDegree ≤ d) :
    (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
      (MvPolynomial.eval (fun j => ((Fin.cons (α := fun _ => ℤ) (1 : ℤ)
            (fun j => if j ∈ S then (1 : ℤ) else 0) j : ℤ) : ℚ)) P
        - MvPolynomial.eval (fun j => ((Fin.cons (α := fun _ => ℤ) (0 : ℤ)
            (fun j => if j ∈ S then (1 : ℤ) else 0) j : ℤ) : ℚ)) P)) = 0 := by
  have hev : ∀ (b : ℤ) (S : Finset (Fin d)),
      MvPolynomial.eval (fun j => ((Fin.cons (α := fun _ => ℤ) b
            (fun j => if j ∈ S then (1 : ℤ) else 0) j : ℤ) : ℚ)) P
        = ∑ u ∈ P.support, P.coeff u *
            ((b : ℚ) ^ u 0 * ∏ j : Fin d, (if j ∈ S then (1 : ℚ) else 0) ^ u j.succ) := by
    intro b S
    rw [MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_ite, Int.cast_one, Int.cast_zero]
  have hterm : ∀ S : Finset (Fin d),
      (-1 : ℚ) ^ (d - S.card) *
        (MvPolynomial.eval (fun j => ((Fin.cons (α := fun _ => ℤ) (1 : ℤ)
              (fun j => if j ∈ S then (1 : ℤ) else 0) j : ℤ) : ℚ)) P
          - MvPolynomial.eval (fun j => ((Fin.cons (α := fun _ => ℤ) (0 : ℤ)
              (fun j => if j ∈ S then (1 : ℤ) else 0) j : ℤ) : ℚ)) P)
        = ∑ u ∈ P.support, P.coeff u * (1 - (0 : ℚ) ^ u 0) *
            ((-1 : ℚ) ^ (d - S.card) * ∏ j : Fin d, (if j ∈ S then (1 : ℚ) else 0) ^ u j.succ) := by
    intro S
    rw [hev, hev, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Int.cast_one, Int.cast_zero, one_pow]
    ring
  rw [Finset.sum_congr rfl (fun S _ => hterm S), Finset.sum_comm]
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [← Finset.mul_sum]
  rw [alternating_sum_indicator_prod (fun j : Fin d => u j.succ)]
  have hprod : (1 - (0 : ℚ) ^ u 0) * ∏ j : Fin d, (1 - (0 : ℚ) ^ u j.succ)
      = ∏ j : Fin (d + 1), (1 - (0 : ℚ) ^ u j) :=
    (Fin.prod_univ_succ (fun j : Fin (d + 1) => 1 - (0 : ℚ) ^ u j)).symm
  rw [mul_assoc, hprod]
  obtain ⟨j, hj⟩ : ∃ j, u j = 0 := by
    by_contra hcon
    have h : ∀ j, u j ≠ 0 := fun j hj => hcon ⟨j, hj⟩
    have hsupp : u.support = Finset.univ := by
      ext j
      simp [Finsupp.mem_support_iff, h j]
    have hsum : ∑ j : Fin (d + 1), u j ≤ d := by
      simpa [Finsupp.sum, hsupp] using le_trans (MvPolynomial.le_totalDegree hu) hP
    have hge : ∑ _j : Fin (d + 1), (1 : ℕ) ≤ ∑ j : Fin (d + 1), u j :=
      Finset.sum_le_sum fun j _ => Nat.one_le_iff_ne_zero.mpr (h j)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hge
    omega
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, pow_zero, sub_self]), mul_zero]

end MixedDifference

/-- The tensor chain `G ⊗ F_0^{n_0} ⊗ ⋯ ⊗ F_{d-1}^{n_{d-1}}`, spelled exactly as in
`exists_snapper_mvPolynomial` (Stacks 0BEM) and `snapperIntersection` (Stacks 0BEP). -/
noncomputable def AlgebraicGeometry.snapperChain {X : AlgebraicGeometry.Scheme.{u}} {d : ℕ}
    (F : Fin d → X.Modules) (n : Fin d → ℤ) (G : X.Modules) : X.Modules :=
  (List.finRange d).foldl
    (fun (G : X.Modules) (j : Fin d) => G.tensor (F j ^ n j)) G

local notation "𝒪[" X "]" =>
  (SheafOfModules.unit (AlgebraicGeometry.Scheme.ringCatSheaf X) : AlgebraicGeometry.Scheme.Modules X)

/-- **Stacks 0BER**: the intersection number `(L_1 ⋯ L_d · X)` is additive in each factor:
if `L_i ≅ L' ⊗ L''`, then `(L_1⋯L_i⋯L_d · X) = (L_1⋯L'⋯L_d · X) + (L_1⋯L''⋯L_d · X)`.
Route: see the module docstring (one application of Stacks 0BEM to the `d+1` line bundles
`L'', L_1, …, L', …, L_d`, then the vanishing of the `(d+1)`-fold mixed difference of a polynomial of total
degree `≤ d`). -/
theorem AlgebraicGeometry.snapperIntersection_tensor {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) {d : ℕ} (hd : X.dimension = d) (L : Fin d → X.Modules)
    [∀ i, (L i).IsLineBundle] (i : Fin d) (L' L'' : X.Modules) [L'.IsLineBundle] [L''.IsLineBundle]
    [∀ j, (Function.update L i L' j).IsLineBundle] [∀ j, (Function.update L i L'' j).IsLineBundle]
    (e : L i ≅ AlgebraicGeometry.Scheme.Modules.tensor L' L'') :
    AlgebraicGeometry.snapperIntersection X hX hd L
      = AlgebraicGeometry.snapperIntersection X hX hd (Function.update L i L')
        + AlgebraicGeometry.snapperIntersection X hX hd (Function.update L i L'') := by
  set L₁ := Function.update L i L' with hL₁
  set L₂ := Function.update L i L'' with hL₂
  -- unfold the definition of the intersection number
  have hsn : ∀ (F : Fin d → X.Modules) [∀ j, (F j).IsLineBundle],
      AlgebraicGeometry.snapperIntersection X hX hd F
        = ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
            ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
              (AlgebraicGeometry.snapperChain F (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ) :=
    fun F _ => rfl
  -- Step 1: Stacks 0BEM for `O_X` and the `d+1` line bundles `L'', L₁_0, …, L₁_{d-1}`
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hO : AlgebraicGeometry.Scheme.Modules.IsCoherent 𝒪[X] := AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree _
  have hsupp : topologicalKrullDim (AlgebraicGeometry.Scheme.Modules.support 𝒪[X]) ≤ ((d : ℕ) : WithBot ℕ∞) := by
    have h1 := AlgebraicGeometry.topologicalKrullDim_le_dimension_of_isProperOver X hX
    rw [hd] at h1
    exact (topologicalKrullDim_subspace_le X _).trans h1
  have hLt : ∀ j : Fin (d + 1), (Fin.cons (α := fun _ => X.Modules) L'' L₁ j).IsLineBundle := fun j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Fin.cons_zero]; infer_instance
    · rw [Fin.cons_succ]; infer_instance
  obtain ⟨P, hPdeg, hPχ⟩ := AlgebraicGeometry.exists_snapper_mvPolynomial (k := k) X hX 𝒪[X]
    (Fin.cons (α := fun _ => X.Modules) L'' L₁) d hsupp
  -- the `(d+1)`-chain splits off its first factor
  have hchain : ∀ (m : ℤ) (n : Fin d → ℤ),
      (List.finRange (d + 1)).foldl
          (fun (G : X.Modules) (j : Fin (d + 1)) =>
            G.tensor (Fin.cons (α := fun _ => X.Modules) L'' L₁ j ^ Fin.cons (α := fun _ => ℤ) m n j)) 𝒪[X]
        = AlgebraicGeometry.snapperChain L₁ n (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ m)) := by
    intro m n
    rw [List.finRange_succ]
    change (List.map Fin.succ (List.finRange d)).foldl _ _ = _
    rw [List.foldl_map]
    rfl
  have hval : ∀ (S : Finset (Fin d)) (m : ℤ),
      MvPolynomial.eval (fun j => ((Fin.cons (α := fun _ => ℤ) m
          (fun j => if j ∈ S then (1 : ℤ) else 0) j : ℤ) : ℚ)) P
        = ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ m))) : ℤ) : ℚ) := by
    intro S m
    rw [← hPχ (Fin.cons (α := fun _ => ℤ) m (fun j => if j ∈ S then (1 : ℤ) else 0)), hchain]
  -- Step 2: the algebraic vanishing
  have halg := MvPolynomial.mixedDifference_cons_eq_zero P hPdeg
  -- Step 3: identifications of the chains
  have G1 : ∀ S : Finset (Fin d), i ∈ S →
      ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0)
            (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (1 : ℤ)))) : ℤ) : ℚ)
        = ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.snapperChain L (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ) := by
    intro S hi
    have e₀ : Nonempty (AlgebraicGeometry.Scheme.Modules.tensor (L'' ^ (1 : ℤ))
        (L₁ i ^ (if i ∈ S then (1 : ℤ) else 0)) ≅ L i ^ (if i ∈ S then (1 : ℤ) else 0)) := by
      rw [if_pos hi, hL₁, Function.update_self]
      exact ⟨AlgebraicGeometry.Scheme.Modules.tensorCongrLeftIso
          (AlgebraicGeometry.Scheme.Modules.tensorUnitIso L'') _ ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso _
          (AlgebraicGeometry.Scheme.Modules.tensorUnitIso L') ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorCommIso L'' L' ≪≫ e.symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.tensorUnitIso (L i)).symm⟩
    obtain ⟨e₀⟩ := e₀
    obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.chain_cons_insert i
      (fun j => L₁ j ^ (if j ∈ S then (1 : ℤ) else 0)) (fun j => L j ^ (if j ∈ S then (1 : ℤ) else 0))
      (L'' ^ (1 : ℤ)) e₀ (List.finRange d) (List.nodup_finRange d) (List.mem_finRange i)
      (fun j _ hj => by simp only [hL₁, Function.update_of_ne hj]) 𝒪[X]
    exact congrArg _ (AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso (k := k) e₁)
  have G2 : ∀ S : Finset (Fin d), i ∉ S →
      ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0)
            (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (1 : ℤ)))) : ℤ) : ℚ)
        = ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.snapperChain L₂ (fun j => if j ∈ insert i S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ) := by
    intro S hi
    have e₀ : Nonempty (AlgebraicGeometry.Scheme.Modules.tensor (L'' ^ (1 : ℤ))
        (L₁ i ^ (if i ∈ S then (1 : ℤ) else 0)) ≅ L₂ i ^ (if i ∈ insert i S then (1 : ℤ) else 0)) := by
      rw [if_neg hi, if_pos (Finset.mem_insert_self i S), hL₁, hL₂, Function.update_self,
        Function.update_self]
      exact ⟨AlgebraicGeometry.Scheme.Modules.tensorUnitIso (L'' ^ (1 : ℤ))⟩
    obtain ⟨e₀⟩ := e₀
    obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.chain_cons_insert i
      (fun j => L₁ j ^ (if j ∈ S then (1 : ℤ) else 0))
      (fun j => L₂ j ^ (if j ∈ insert i S then (1 : ℤ) else 0))
      (L'' ^ (1 : ℤ)) e₀ (List.finRange d) (List.nodup_finRange d) (List.mem_finRange i)
      (fun j _ hj => by simp only [hL₁, hL₂, Function.update_of_ne hj, Finset.mem_insert, hj, false_or]) 𝒪[X]
    exact congrArg _ (AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso (k := k) e₁)
  have G3 : ∀ S : Finset (Fin d),
      ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0)
            (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (0 : ℤ)))) : ℤ) : ℚ)
        = ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ) := by
    intro S
    obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.chain_congr_start
      (fun j => L₁ j ^ (if j ∈ S then (1 : ℤ) else 0)) (List.finRange d)
      (G := AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (0 : ℤ))) (G' := 𝒪[X])
      (AlgebraicGeometry.Scheme.Modules.tensorUnitIso 𝒪[X])
    exact congrArg _ (AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso (k := k) e₁)
  have G4 : ∀ S : Finset (Fin d), i ∉ S →
      AlgebraicGeometry.snapperChain L (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X]
          = AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X] ∧
        AlgebraicGeometry.snapperChain L₂ (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X]
          = AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X] := by
    intro S hi
    constructor
    · refine AlgebraicGeometry.Scheme.Modules.chain_congr_fun _ _ (List.finRange d) (fun j _ => ?_) _
      by_cases hj : j = i
      · subst hj
        show L j ^ (if j ∈ S then (1 : ℤ) else 0) = L₁ j ^ (if j ∈ S then (1 : ℤ) else 0)
        rw [if_neg hi]
        rfl
      · show L j ^ (if j ∈ S then (1 : ℤ) else 0) = L₁ j ^ (if j ∈ S then (1 : ℤ) else 0)
        rw [hL₁, Function.update_of_ne hj]
    · refine AlgebraicGeometry.Scheme.Modules.chain_congr_fun _ _ (List.finRange d) (fun j _ => ?_) _
      by_cases hj : j = i
      · subst hj
        show L₂ j ^ (if j ∈ S then (1 : ℤ) else 0) = L₁ j ^ (if j ∈ S then (1 : ℤ) else 0)
        rw [if_neg hi]
        rfl
      · show L₂ j ^ (if j ∈ S then (1 : ℤ) else 0) = L₁ j ^ (if j ∈ S then (1 : ℤ) else 0)
        rw [hL₁, hL₂, Function.update_of_ne hj, Function.update_of_ne hj]
  -- Step 4: split every sum over `Finset (Fin d)` according to whether `i` is in the set
  have hi' : i ∉ Finset.univ.erase i := fun h => (Finset.mem_erase.mp h).1 rfl
  have hsplit : ∀ f : Finset (Fin d) → ℚ,
      ∑ S : Finset (Fin d), f S = ∑ S ∈ (Finset.univ.erase i).powerset, (f S + f (insert i S)) := by
    intro f
    have h := Finset.sum_powerset_insert hi' f
    rw [Finset.insert_erase (Finset.mem_univ i), Finset.powerset_univ, ← Finset.sum_add_distrib] at h
    exact h
  have hmem : ∀ S ∈ (Finset.univ.erase i).powerset, i ∉ S := fun S hS h =>
    (Finset.mem_erase.mp (Finset.mem_powerset.mp hS h)).1 rfl
  have hsign : ∀ S ∈ (Finset.univ.erase i).powerset,
      (-1 : ℚ) ^ (d - S.card) = -((-1 : ℚ) ^ (d - (insert i S).card)) := by
    intro S hS
    have hle : S.card + 1 ≤ d := by
      have h := Finset.card_le_card (Finset.mem_powerset.mp hS)
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at h
      have hd0 : 0 < d := Fin.pos i
      omega
    rw [Finset.card_insert_of_notMem (hmem S hS)]
    have h2 : d - S.card = (d - (S.card + 1)) + 1 := by omega
    rw [h2, pow_succ]
    ring
  -- the vanishing, in terms of Euler characteristics and split
  have halg' : ∑ S ∈ (Finset.univ.erase i).powerset,
      ((-1 : ℚ) ^ (d - S.card) *
        (((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (1 : ℤ)))) : ℤ) : ℚ)
          - ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (0 : ℤ)))) : ℤ) : ℚ))
        + (-1 : ℚ) ^ (d - (insert i S).card) *
        (((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ insert i S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (1 : ℤ)))) : ℤ) : ℚ)
          - ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ insert i S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (0 : ℤ)))) : ℤ) : ℚ))) = 0 := by
    refine Eq.trans ?_ halg
    rw [hsplit]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hval, hval, hval, hval]
  -- termwise identity
  have key : ∀ S ∈ (Finset.univ.erase i).powerset,
      ((-1 : ℚ) ^ (d - S.card) *
          ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ)
        + (-1 : ℚ) ^ (d - (insert i S).card) *
          ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L (fun j => if j ∈ insert i S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ))
        = ((-1 : ℚ) ^ (d - S.card) *
          ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ)
        + (-1 : ℚ) ^ (d - (insert i S).card) *
          ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ insert i S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ))
        + ((-1 : ℚ) ^ (d - S.card) *
          ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₂ (fun j => if j ∈ S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ)
        + (-1 : ℚ) ^ (d - (insert i S).card) *
          ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₂ (fun j => if j ∈ insert i S then (1 : ℤ) else 0) 𝒪[X]) : ℤ) : ℚ))
        + ((-1 : ℚ) ^ (d - S.card) *
        (((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (1 : ℤ)))) : ℤ) : ℚ)
          - ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (0 : ℤ)))) : ℤ) : ℚ))
        + (-1 : ℚ) ^ (d - (insert i S).card) *
        (((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ insert i S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (1 : ℤ)))) : ℤ) : ℚ)
          - ((AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (AlgebraicGeometry.snapperChain L₁ (fun j => if j ∈ insert i S then (1 : ℤ) else 0)
              (AlgebraicGeometry.Scheme.Modules.tensor 𝒪[X] (L'' ^ (0 : ℤ)))) : ℤ) : ℚ))) := by
    intro S hS
    have hiS := hmem S hS
    rw [G1 (insert i S) (Finset.mem_insert_self i S), G2 S hiS, G3 S, G3 (insert i S),
      (G4 S hiS).1, (G4 S hiS).2, hsign S hS]
    ring
  rw [hsn L, hsn L₁, hsn L₂, hsplit, hsplit, hsplit, Finset.sum_congr rfl key,
    Finset.sum_add_distrib, Finset.sum_add_distrib, halg', add_zero]

end
