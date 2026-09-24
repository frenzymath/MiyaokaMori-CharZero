import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.Stacks0a38GradedPieceRestrict

/-! # The opens `V`, `W` and the generators of degree `k+1`

Bookkeeping for paragraph 3 of the proof of Stacks 0A38. Given the gcd-closed list `(V_i, n_i, ψ_i)` of
constant positive generators of `K ⊆ ℤ_X` and `k : ℕ`:
* `gradedOpen V n k = V := ⋃_{n_i = k+1} V_i`, `gradedOpenLow V n k := ⋃_{n_i ≤ k} V_i` and
  `gradedOpenInter V n k = W := V ∩ ⋃_{n_i ≤ k} V_i`, with their compactness (finite unions of quasi-compact
  opens; `W` by quasi-separatedness);
* `genSubIn ψ n k i hi : j_!ℤ_{V_i} ⟶ K_k` — the generator `ψ_i` (`n_i ≤ k`) as a map into `K_k = genSub ψ n k`
  (`genSubIn_comp_genSubι : genSubIn ≫ genSubι = ψ_i`);
* `exists_gradedSection`: the constant section `k+1` of `ℤ_X` over `V` lies in `K_{k+1}`: there is
  `q : j_!ℤ_V ⟶ K_{k+1}` with `q ≫ ι_{k+1} ≫ m = (k+1) • c_V` (locally on `V_i`, `n_i = k+1`, it is `ψ_i`;
  glue with `exists_comp_eq_of_cover`);
* `exists_gcd_index`: for `x ∈ W` the gcd-closure provides a generator `(V_l, n_l)` with `x ∈ V_l`, `n_l ∣ k+1`
  and `n_l ≤ k` (`hgcd` applied to `{i, j}` with `x ∈ V_i`, `n_i = k+1`, `x ∈ V_j`, `n_j ≤ k`);
* `exists_gradedSectionLow`: the constant section `k+1` over `W` lies in `K_k`: there is
  `r : j_!ℤ_W ⟶ K_k` with `r ≫ ι_k ≫ m = (k+1) • c_W` (locally on `V_i ∩ V_j ∩ V_l` it is `((k+1)/n_l) • ψ_l`).

Source: Stacks 0A38 (cohomology-lemma-subsheaf-of-constant-sheaf), proof, paragraph 3. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

section Opens

variable {t : ℕ} (V : Fin t → Opens X) (n : Fin t → ℕ) (k : ℕ)

/-- `V := ⋃_{n_i = k+1} V_i` -/
def gradedOpen : Opens X := ⨆ i : {i : Fin t // n i = k + 1}, V i.1

/-- `⋃_{n_i ≤ k} V_i` -/
def gradedOpenLow : Opens X := ⨆ i : {i : Fin t // n i ≤ k}, V i.1

/-- `W := V ∩ ⋃_{n_i ≤ k} V_i` -/
def gradedOpenInter : Opens X := gradedOpen V n k ⊓ gradedOpenLow V n k

theorem le_gradedOpen {i : Fin t} (hi : n i = k + 1) : V i ≤ gradedOpen V n k :=
  le_iSup (fun i : {i : Fin t // n i = k + 1} => V i.1) ⟨i, hi⟩

theorem le_gradedOpenLow {i : Fin t} (hi : n i ≤ k) : V i ≤ gradedOpenLow V n k :=
  le_iSup (fun i : {i : Fin t // n i ≤ k} => V i.1) ⟨i, hi⟩

theorem mem_gradedOpen {x : X} : x ∈ gradedOpen V n k ↔ ∃ i, n i = k + 1 ∧ x ∈ V i := by
  unfold gradedOpen
  rw [Opens.mem_iSup]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.1, i.2, hi⟩, fun ⟨i, hi, hx⟩ => ⟨⟨i, hi⟩, hx⟩⟩

theorem mem_gradedOpenLow {x : X} : x ∈ gradedOpenLow V n k ↔ ∃ i, n i ≤ k ∧ x ∈ V i := by
  unfold gradedOpenLow
  rw [Opens.mem_iSup]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.1, i.2, hi⟩, fun ⟨i, hi, hx⟩ => ⟨⟨i, hi⟩, hx⟩⟩

theorem gradedOpenInter_le : gradedOpenInter V n k ≤ gradedOpen V n k := inf_le_left

theorem isCompact_gradedOpen (hV : ∀ i, IsCompact ((V i : Opens X) : Set X)) :
    IsCompact ((gradedOpen V n k : Opens X) : Set X) := by
  unfold gradedOpen
  rw [Opens.coe_iSup]
  exact isCompact_iUnion fun i => hV i.1

theorem isCompact_gradedOpenLow (hV : ∀ i, IsCompact ((V i : Opens X) : Set X)) :
    IsCompact ((gradedOpenLow V n k : Opens X) : Set X) := by
  unfold gradedOpenLow
  rw [Opens.coe_iSup]
  exact isCompact_iUnion fun i => hV i.1

theorem isCompact_gradedOpenInter [QuasiSeparatedSpace X] (hV : ∀ i, IsCompact ((V i : Opens X) : Set X)) :
    IsCompact ((gradedOpenInter V n k : Opens X) : Set X) := by
  unfold gradedOpenInter
  rw [Opens.coe_inf]
  exact QuasiSeparatedSpace.inter_isCompact _ _ (gradedOpen V n k).isOpen (isCompact_gradedOpen V n k hV)
    (gradedOpenLow V n k).isOpen (isCompact_gradedOpenLow V n k hV)

/-- For `x ∈ W` there are `i, j, l` with `n_i = k+1`, `x ∈ V_i`, `n_j ≤ k`, `x ∈ V_j`, `x ∈ V_l`, `n_l ∣ k+1`
and `n_l ≤ k` (gcd-closure applied to `{i, j}`: `n_l = gcd(n_i, n_j)` divides `n_i = k+1` and `n_j ≤ k`). -/
theorem exists_gcd_index (hn : ∀ i, 0 < n i)
    (hgcd : ∀ (x : X) (J : Finset (Fin t)), J.Nonempty → (∀ j ∈ J, x ∈ V j) → ∃ i, x ∈ V i ∧ n i = J.gcd n)
    {x : X} (hx : x ∈ gradedOpenInter V n k) :
    ∃ i j l : Fin t, n i = k + 1 ∧ x ∈ V i ∧ n j ≤ k ∧ x ∈ V j ∧ x ∈ V l ∧ n l ∣ k + 1 ∧ n l ≤ k := by
  obtain ⟨i, hi, hxi⟩ := (mem_gradedOpen V n k).mp hx.1
  obtain ⟨j, hj, hxj⟩ := (mem_gradedOpenLow V n k).mp hx.2
  classical
  obtain ⟨l, hxl, hl⟩ := hgcd x {i, j} ⟨i, Finset.mem_insert_self i {j}⟩ (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hxi
    · rw [Finset.mem_singleton] at ha
      subst ha
      exact hxj)
  have hli : n l ∣ n i := hl ▸ Finset.gcd_dvd (Finset.mem_insert_self i {j})
  have hlj : n l ∣ n j := hl ▸ Finset.gcd_dvd (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  exact ⟨i, j, l, hi, hxi, hj, hxj, hxl, hi ▸ hli, le_trans (Nat.le_of_dvd (hn j) hlj) hj⟩

end Opens

section Generators

variable {K : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {t : ℕ} {V : Fin t → Opens X} (ψ : ∀ i, extendByZeroConstant (V i) ⟶ K) (n : Fin t → ℕ) (k : ℕ)

section Biproduct

-- Mathlib states `Abelian.hasFiniteBiproducts` as a theorem, not an instance; we use it section-locally
-- (no global instance is registered), exactly as in `Stacks0a38GenSub.lean`.
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- the generator `ψ_i` (`n_i ≤ k`) as a morphism into `K_k = genSub ψ n k` -/
def genSubIn (i : Fin t) (hi : n i ≤ k) : extendByZeroConstant (V i) ⟶ genSub ψ n k :=
  biproduct.ι (fun i : {i : Fin t // n i ≤ k} => extendByZeroConstant (V i.1)) ⟨i, hi⟩ ≫
    factorThruImage (genSubDesc ψ n k)

theorem genSubIn_comp_genSubι (i : Fin t) (hi : n i ≤ k) : genSubIn ψ n k i hi ≫ genSubι ψ n k = ψ i := by
  unfold genSubIn genSubι
  rw [Category.assoc, image.fac]
  exact ι_genSubDesc ψ n k ⟨i, hi⟩

end Biproduct

/-- `genSubIn_comp_genSubι` composed further with `m`, in the form used below -/
theorem genSubIn_comp_genSubι_comp (i : Fin t) (hi : n i ≤ k)
    {Z : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (m : K ⟶ Z) :
    genSubIn ψ n k i hi ≫ genSubι ψ n k ≫ m = ψ i ≫ m := by
  rw [← Category.assoc, genSubIn_comp_genSubι]

variable (m : K ⟶ (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
  (AddCommGrpCat.of (ULift ℤ)))

/-- `ι_k ≫ m : K_k ⟶ ℤ_X` is a monomorphism -/
theorem mono_genSubι_comp [Mono m] : Mono (genSubι ψ n k ≫ m) := by
  have := genSubι_mono ψ n k
  exact mono_comp _ _

/-- **The constant section `k+1` over `V` lies in `K_{k+1}`**: there is `q : j_!ℤ_V ⟶ K_{k+1}` with
`q ≫ ι_{k+1} ≫ m = (k+1) • c_V`. Locally on `V_i` (`n_i = k+1`) the section `k+1` is `ψ_i`
(`hψ : ψ_i ≫ m = n_i • c_{V_i}`), and `V = ⋃_{n_i = k+1} V_i`; glue with `exists_comp_eq_of_cover`. -/
theorem exists_gradedSection [Mono m]
    (hψ : ∀ i, ψ i ≫ m = ((n i : ℤ) • constantInclusion (V i))) :
    ∃ q : extendByZeroConstant (gradedOpen V n k) ⟶ genSub ψ n (k + 1),
      q ≫ genSubι ψ n (k + 1) ≫ m = (((k + 1 : ℕ) : ℤ) • constantInclusion (gradedOpen V n k)) := by
  have := mono_genSubι_comp ψ n (k + 1) m
  refine exists_comp_eq_of_cover (fun i : {i : Fin t // n i = k + 1} => V i.1) (fun i => le_gradedOpen V n k i.2)
    (fun x hx => ?_) (genSubι ψ n (k + 1) ≫ m) _
    (fun i => genSubIn ψ n (k + 1) i.1 (le_of_eq i.2)) (fun i => ?_)
  · obtain ⟨i, hi, hxi⟩ := (mem_gradedOpen V n k).mp hx
    exact ⟨⟨i, hi⟩, hxi⟩
  · rw [genSubIn_comp_genSubι_comp, hψ, Preadditive.comp_zsmul,
      extendByZeroConstantRestrict_comp_constantInclusion, i.2]

/-- **The constant section `k+1` over `W` lies in `K_k`**: there is `r : j_!ℤ_W ⟶ K_k` with
`r ≫ ι_k ≫ m = (k+1) • c_W`. For `x ∈ W` pick `i, j, l` as in `exists_gcd_index`; on
`V_i ∩ V_j ∩ V_l ⊆ V_l` the section `k+1 = ((k+1)/n_l) · n_l` is `((k+1)/n_l) • ψ_l` with `n_l ≤ k`, so it lies
in `K_k`; these opens cover `W`; glue with `exists_comp_eq_of_cover`. -/
theorem exists_gradedSectionLow [Mono m] (hn : ∀ i, 0 < n i)
    (hψ : ∀ i, ψ i ≫ m = ((n i : ℤ) • constantInclusion (V i)))
    (hgcd : ∀ (x : X) (J : Finset (Fin t)), J.Nonempty → (∀ j ∈ J, x ∈ V j) → ∃ i, x ∈ V i ∧ n i = J.gcd n) :
    ∃ r : extendByZeroConstant (gradedOpenInter V n k) ⟶ genSub ψ n k,
      r ≫ genSubι ψ n k ≫ m = (((k + 1 : ℕ) : ℤ) • constantInclusion (gradedOpenInter V n k)) := by
  have := mono_genSubι_comp ψ n k m
  choose i j l hi hxi hj hxj hxl hdvd hlk using fun x : {x : X // x ∈ gradedOpenInter V n k} =>
    exists_gcd_index V n k hn hgcd x.2
  choose d hd using hdvd
  let Wc : {x : X // x ∈ gradedOpenInter V n k} → Opens X := fun x => V (i x) ⊓ V (j x) ⊓ V (l x)
  have hle : ∀ x, Wc x ≤ gradedOpenInter V n k := fun x =>
    le_inf (le_trans inf_le_left (le_trans inf_le_left (le_gradedOpen V n k (hi x))))
      (le_trans inf_le_left (le_trans inf_le_right (le_gradedOpenLow V n k (hj x))))
  have hleL : ∀ x, Wc x ≤ V (l x) := fun x => inf_le_right
  refine exists_comp_eq_of_cover Wc hle (fun x hx => ⟨⟨x, hx⟩, ⟨⟨hxi ⟨x, hx⟩, hxj ⟨x, hx⟩⟩, hxl ⟨x, hx⟩⟩⟩)
    (genSubι ψ n k ≫ m) _
    (fun x => extendByZeroConstantRestrict (hleL x) ≫ ((d x : ℤ) • genSubIn ψ n k (l x) (hlk x))) (fun x => ?_)
  rw [Category.assoc, Preadditive.zsmul_comp, genSubIn_comp_genSubι_comp, hψ, Preadditive.comp_zsmul,
    Preadditive.comp_zsmul, extendByZeroConstantRestrict_comp_constantInclusion, Preadditive.comp_zsmul,
    extendByZeroConstantRestrict_comp_constantInclusion, smul_smul, hd x, Nat.cast_mul, mul_comm]

end Generators

end TopCat.Sheaf

end
