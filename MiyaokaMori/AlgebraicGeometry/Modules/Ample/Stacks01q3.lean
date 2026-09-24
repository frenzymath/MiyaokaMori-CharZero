import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowMapIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleFiniteAffineCover
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ProjectivizationChartLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892_ExtendLocalSection
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1

/-! # High tensor powers of an ample line bundle are globally generated (Stacks 01Q3)

One of the equivalent characterizations of Stacks 01Q3: if `L` is ample on a quasi-compact scheme,
then for `n ≫ 0` the sheaf `L^{⊗n}` has at every point a global section not vanishing there.

References: Stacks 01Q3 (`properties-proposition-characterize-ample`); Lazarsfeld, *Positivity I*,
proof of Thm 1.2.23 ("`O_D(mL)` is globally generated").

Route (Stacks 01Q3 (1)⇒(5) specialised to `F = L^{⊗j}`, with the local step done
via the "`X_s` form a basis" trick instead of "quasi-coherent sheaves on affines are globally generated"):
1. `X` is quasi-separated (`IsAmple.quasiSeparatedSpace`, Stacks 01PY) and `IsAmple` contains `CompactSpace X`.
   `IsAmple.exists_finite_affine_cover` (Stacks 01VU, first step) gives one degree `n > 0` and finitely
   many `s_i ∈ Γ(X, L^{⊗n})` with `X_{s_i}` affine covering `X`; in particular `L^{⊗n}` has, at every point,
   a global section not vanishing there.
2. `exists_mem_nonvanishingLocus_tensorPow_add`: nonvanishing sections of `L^{⊗a}` and `L^{⊗b}` at `y`
   multiply (`sectionTensor`, then `tensorIsoTensorObj ≪≫ (tensorPowAddIso L a b).symm`) to one of
   `L^{⊗(a+b)}` (`mem_nonvanishingLocus_sectionTensor`, `mem_nonvanishingLocus_iso`); iterated with `L^{⊗n}`
   this gives `L^{⊗(a + n m)}` for all `m` (`exists_mem_nonvanishingLocus_tensorPow_add_mul`).
3. `exists_section_tensor_tensorPow_mem_nonvanishingLocus_of_isAffineOpen` (the core): for a line bundle
   `F`, `τ ∈ Γ(X, N)` with `X_τ` affine and `x ∈ X_τ`: take a frame `(W, e)` of `F` at `x`; `X_τ` affine
   gives `g ∈ Γ(X_τ, O)` with `x ∈ D(g) ⊆ W` (Mathlib `IsAffineOpen.exists_basicOpen_le`); Stacks 01PW(2)
   (`exists_section_nonvanishingLocus_inf_eq`, `Stacks0892_ExtendLocalSection`)
   applied to the section `g` of `O_X` over `X_τ` yields `σ₁ ∈ Γ(X, O_X ⊗ N^{⊗e₁})` with `X_{σ₁} ⊓ X_τ = D(g)`;
   `σ₂ := σ₁ ⊗ τ` has `X_{σ₂} = D(g) ⊆ W`; 01PW(2) again, applied to the frame `e|_{X_{σ₂}}` of `F` over
   `X_{σ₂}`, yields `σ ∈ Γ(X, F ⊗ N₂^{⊗e₂})` not vanishing at `x`.
4. `exists_tensorPow_section_mem_nonvanishingLocus_of_isAffineOpen`: with `N = L^{⊗n}`, `F = L^{⊗j}` the
   sheaf in step 3 is rearranged to `L^{⊗(j + n k)}`, `k = (e₁+1) e₂` (`unitTensorLeftIso`, `tensorPowMapIso`,
   `tensorPowMulIso`, `tensorPowAddIso`).
5. Main theorem: for each residue `j` and each `x`, step 4 (with `τ = s_i`, `x ∈ X_{s_i}`) gives `k_x` and a
   section of `L^{⊗(j + n k_x)}` not vanishing at `x`; by compactness finitely many of these nonvanishing loci
   cover `X`; with `K_j := max k_x` step 2 gives nonvanishing sections of `L^{⊗(j + n K_j)}` everywhere.
   Put `n₀ := n · max_{j<n} K_j`; for `m ≥ n₀` write `m = (m % n) + n (m / n)` with `m / n ≥ K_{m % n}` and use
   step 2 once more. `¬ IsZeroAt s x` is by definition `x ∈ X_s`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Sections of `L^{⊗a}` and `L^{⊗b}` not vanishing at `y` multiply to a section of `L^{⊗(a+b)}` not
vanishing at `y`. -/
theorem exists_mem_nonvanishingLocus_tensorPow_add (L : X.Modules) [L.IsLineBundle] {a b : ℕ} (y : X)
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L a, ⊤))
    (hs : y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L a).nonvanishingLocus s)
    (t : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L b, ⊤))
    (ht : y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L b).nonvanishingLocus t) :
    ∃ r : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (a + b), ⊤),
      y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L (a + b)).nonvanishingLocus r := by
  let θ : AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L a)
      (AlgebraicGeometry.Scheme.Modules.tensorPow L b) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow L (a + b) :=
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L a b).symm
  refine ⟨θ.hom.app ⊤ (sectionTensor s t), ?_⟩
  refine (mem_nonvanishingLocus_iso θ (sectionTensor s t) y).mpr ?_
  exact (mem_nonvanishingLocus_sectionTensor _ _ s t y).mpr ⟨hs, ht⟩

/-- Iterating the previous lemma: nonvanishing sections of `L^{⊗a}` and `L^{⊗n}` at `y` give one of
`L^{⊗(a + n m)}` for every `m`. -/
theorem exists_mem_nonvanishingLocus_tensorPow_add_mul (L : X.Modules) [L.IsLineBundle] {a n : ℕ} (y : X)
    (ha : ∃ r : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L a, ⊤),
      y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L a).nonvanishingLocus r)
    (hn : ∃ t : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤),
      y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus t) (m : ℕ) :
    ∃ r : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (a + n * m), ⊤),
      y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L (a + n * m)).nonvanishingLocus r := by
  induction m with
  | zero =>
    rw [Nat.mul_zero, Nat.add_zero]
    exact ha
  | succ m ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨t, ht⟩ := hn
    have h := exists_mem_nonvanishingLocus_tensorPow_add L y r hr t ht
    rw [show a + n * m + n = a + n * (m + 1) by ring] at h
    exact h

set_option backward.isDefEq.respectTransparency false in
/-- **Core step of Stacks 01Q3 (1)⇒(5) for line bundles, at one point.** `X` quasi-compact and
quasi-separated, `N`, `F` line bundles, `τ ∈ Γ(X, N)` with `X_τ` affine, `x ∈ X_τ`. Then for some
`e₁, e₂` there is a global section `σ` of `F ⊗ ((O_X ⊗ N^{⊗e₁}) ⊗ N)^{⊗e₂}` not vanishing at `x`.

Proof. Take a frame `(W, e)` of `F` at `x` (`exists_frame`); since `X_τ` is affine, there is
`g ∈ Γ(X_τ, O)` with `x ∈ D(g) ⊆ W` (Mathlib `IsAffineOpen.exists_basicOpen_le`). Stacks 01PW(2)
(`exists_section_nonvanishingLocus_inf_eq`) applied to the section `g` of
`O_X` over `X_τ` gives `σ₁ ∈ Γ(X, O_X ⊗ N^{⊗e₁})` with `X_{σ₁} ⊓ X_τ = D(g)`; then
`σ₂ := σ₁ ⊗ τ` has `X_{σ₂} = D(g)` (`nonvanishingLocus_sectionTensor`). Apply 01PW(2) again to the
frame `e|_{X_{σ₂}}` of `F` over `X_{σ₂}`: `σ ∈ Γ(X, F ⊗ N₂^{⊗e₂})` with `X_σ ⊓ X_{σ₂} = X_{σ₂} ∋ x`. -/
theorem exists_section_tensor_tensorPow_mem_nonvanishingLocus_of_isAffineOpen
    [CompactSpace X] [QuasiSeparatedSpace X]
    (N F : X.Modules) [N.IsLineBundle] [F.IsLineBundle] (τ : Γ(N, ⊤))
    (hτ : AlgebraicGeometry.IsAffineOpen (N.nonvanishingLocus τ)) {x : X}
    (hx : x ∈ N.nonvanishingLocus τ) :
    ∃ (e₁ e₂ : ℕ) (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensor F
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.tensor (SheafOfModules.unit X.ringCatSheaf)
            (AlgebraicGeometry.Scheme.Modules.tensorPow N e₁)) N) e₂), ⊤)),
      x ∈ (AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          (AlgebraicGeometry.Scheme.Modules.tensor
            (AlgebraicGeometry.Scheme.Modules.tensor (SheafOfModules.unit X.ringCatSheaf)
              (AlgebraicGeometry.Scheme.Modules.tensorPow N e₁)) N) e₂)).nonvanishingLocus σ := by
  obtain ⟨W, hxW, e, hf⟩ := exists_frame F x
  obtain ⟨g, hgW, hxg⟩ := hτ.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hx
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  -- Step 1: a global section σ₁ of `O_X ⊗ N^{⊗e₁}` with `X_{σ₁} ⊓ X_τ = D(g)` (Stacks 01PW(2)).
  have hW₁ : ∀ (y : X) (hy : y ∈ N.nonvanishingLocus τ), y ∈ X.basicOpen g ↔
      O.presheaf.germ (N.nonvanishingLocus τ) y hy g ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (O.stalk y)) := by
    intro y hy
    have hfr := ProjectivizationChartLocalFormula.isFrame_unit_one (X := X) (N.nonvanishingLocus τ)
    have hc : hfr.coord le_rfl (O.res le_rfl g) = g := by
      refine hfr.coord_unique le_rfl _ _ ?_
      rw [res_self, res_self]
      change g * (1 : Γ(X, N.nonvanishingLocus τ)) = g
      exact mul_one g
    have h1 := hfr.germ_mem_maximalIdeal_smul_iff_coord_res le_rfl hy g
    rw [hc] at h1
    refine Iff.trans (X.mem_basicOpen g y hy) ?_
    refine Iff.trans ?_ (not_congr h1).symm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  obtain ⟨e₁, σ₁, hσ₁⟩ := exists_section_nonvanishingLocus_inf_eq N τ O g (X.basicOpen g)
    (X.basicOpen_le g) hW₁
  -- Step 2: σ₂ := σ₁ ⊗ τ has nonvanishing locus exactly `D(g) ⊆ W`.
  let N₂ : X.Modules := AlgebraicGeometry.Scheme.Modules.tensor
    (AlgebraicGeometry.Scheme.Modules.tensor O (AlgebraicGeometry.Scheme.Modules.tensorPow N e₁)) N
  let σ₂ : Γ(N₂, ⊤) := sectionTensor σ₁ τ
  have hσ₂ : N₂.nonvanishingLocus σ₂ = X.basicOpen g := by
    rw [← hσ₁]
    exact nonvanishingLocus_sectionTensor _ N σ₁ τ
  have hle : N₂.nonvanishingLocus σ₂ ≤ W := by rw [hσ₂]; exact hgW
  have hxσ₂ : x ∈ N₂.nonvanishingLocus σ₂ := by rw [hσ₂]; exact hxg
  -- Step 3: extend the frame `e|_{X_{σ₂}}` of `F` to a global section of `F ⊗ N₂^{⊗e₂}` (01PW(2)).
  have hW₂ : ∀ (y : X) (hy : y ∈ N₂.nonvanishingLocus σ₂), y ∈ N₂.nonvanishingLocus σ₂ ↔
      F.presheaf.germ (N₂.nonvanishingLocus σ₂) y hy (F.res hle e) ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (F.stalk y)) :=
    fun y hy => iff_of_true hy ((hf.restrict hle).germ_notMem_maximalIdeal_smul hy)
  obtain ⟨e₂, σ₃, hσ₃⟩ := exists_section_nonvanishingLocus_inf_eq N₂ σ₂ F (F.res hle e)
    (N₂.nonvanishingLocus σ₂) le_rfl hW₂
  refine ⟨e₁, e₂, σ₃, ?_⟩
  have h : x ∈ (AlgebraicGeometry.Scheme.Modules.tensor F
      (AlgebraicGeometry.Scheme.Modules.tensorPow N₂ e₂)).nonvanishingLocus σ₃ ⊓
      N₂.nonvanishingLocus σ₂ := by
    rw [hσ₃]; exact hxσ₂
  exact h.1

set_option backward.isDefEq.respectTransparency false in
/-- Degree bookkeeping for the previous lemma with `N = L^{⊗n}`, `F = L^{⊗j}`: a global section of
`L^{⊗(j + n k)}` (some `k`) not vanishing at `x ∈ X_τ`, `X_τ` affine, `τ ∈ Γ(X, L^{⊗n})`.
The rearrangement `L^{⊗j} ⊗ ((O_X ⊗ (L^{⊗n})^{⊗e₁}) ⊗ L^{⊗n})^{⊗e₂} ≅ L^{⊗(j + n(e₁+1)e₂)}` is built from
`unitTensorLeftIso`, `tensorPowMapIso`, `tensorPowMulIso`, `tensorPowAddIso`; nonvanishing loci are
invariant under isomorphisms (`mem_nonvanishingLocus_iso`). -/
theorem exists_tensorPow_section_mem_nonvanishingLocus_of_isAffineOpen
    [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsLineBundle] (n : ℕ) (τ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤))
    (hτ : AlgebraicGeometry.IsAffineOpen
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus τ)) (j : ℕ) {x : X}
    (hx : x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus τ) :
    ∃ (k : ℕ) (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * k), ⊤)),
      x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * k)).nonvanishingLocus σ := by
  obtain ⟨e₁, e₂, σ₃, hxσ₃⟩ := exists_section_tensor_tensorPow_mem_nonvanishingLocus_of_isAffineOpen
    (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (AlgebraicGeometry.Scheme.Modules.tensorPow L j)
    τ hτ hx
  let θ₁ : AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensor (SheafOfModules.unit X.ringCatSheaf)
        (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L n) e₁))
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (e₁ + 1) :=
    tensorCongrLeftIso (unitTensorLeftIso _) _
  let θ : AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L j)
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.tensor (SheafOfModules.unit X.ringCatSheaf)
            (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L n) e₁))
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n)) e₂) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * ((e₁ + 1) * e₂)) :=
    tensorCongrRightIso _ (AlgebraicGeometry.Scheme.Modules.tensorPowMapIso θ₁ e₂ ≪≫
        tensorPowMulIso (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (e₁ + 1) e₂ ≪≫
        tensorPowMulIso L n ((e₁ + 1) * e₂)) ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L j (n * ((e₁ + 1) * e₂))).symm
  exact ⟨(e₁ + 1) * e₂, θ.hom.app ⊤ σ₃, (mem_nonvanishingLocus_iso θ σ₃ x).mpr hxσ₃⟩

end AlgebraicGeometry.Scheme.Modules

/-- **Stacks 01Q3 (1)⇒(5) for the powers of `L`.** If `L` is ample then there is `n₀` such that for
every `m ≥ n₀` and every point `x` some global section of `L^{⊗m}` does not vanish at `x`. -/
theorem AlgebraicGeometry.IsAmple.eventually_globallyGenerated {X : AlgebraicGeometry.Scheme.{u}}
    [CompactSpace X] (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x : X, ∃ s : ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).val.obj (Opposite.op ⊤) : Type u), ¬ IsZeroAt s x := by
  classical
  have hqs : QuasiSeparatedSpace X := hL.quasiSeparatedSpace L
  obtain ⟨n, hn, ι, hι, s, hcov, haff⟩ := hL.exists_finite_affine_cover
  -- `L^{⊗n}` has a nonvanishing global section at every point.
  have hQn : ∀ y : X, ∃ t : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤),
      y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus t := fun y =>
    let ⟨i, hi⟩ := hcov y; ⟨s i, hi⟩
  -- For each residue `j` there is `K j` with `L^{⊗(j + n K j)}` globally generated.
  have hres : ∀ j : ℕ, ∃ K : ℕ, ∀ y : X,
      ∃ r : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * K), ⊤),
        y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * K)).nonvanishingLocus r := by
    intro j
    have hpt : ∀ x : X, ∃ (k : ℕ) (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * k), ⊤)),
        x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * k)).nonvanishingLocus σ := by
      intro x
      obtain ⟨i, hi⟩ := hcov x
      exact AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_mem_nonvanishingLocus_of_isAffineOpen
        L n (s i) (haff i) j hi
    choose k σ hσ using hpt
    obtain ⟨T, hT⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
      (fun x : X => (((AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * k x)).nonvanishingLocus (σ x) :
        X.Opens) : Set X))
      (fun x => ((AlgebraicGeometry.Scheme.Modules.tensorPow L (j + n * k x)).nonvanishingLocus (σ x)).isOpen)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, hσ x⟩)
    refine ⟨T.sup k, fun y => ?_⟩
    have hy := hT (Set.mem_univ y)
    rw [Set.mem_iUnion₂] at hy
    obtain ⟨x, hxT, hyx⟩ := hy
    have hk : k x ≤ T.sup k := Finset.le_sup hxT
    have key : ∀ b : ℕ, b = j + n * k x + n * (T.sup k - k x) →
        ∃ r : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L b, ⊤),
          y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L b).nonvanishingLocus r := by
      rintro _ rfl
      exact AlgebraicGeometry.Scheme.Modules.exists_mem_nonvanishingLocus_tensorPow_add_mul L y
        ⟨σ x, hyx⟩ (hQn y) _
    exact key _ (by rw [add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hk])
  choose K hK using hres
  refine ⟨n * (Finset.range n).sup K, fun m hm y => ?_⟩
  have hjn : m % n < n := Nat.mod_lt m hn
  have hKle : K (m % n) ≤ (Finset.range n).sup K := Finset.le_sup (Finset.mem_range.mpr hjn)
  have hq : (Finset.range n).sup K ≤ m / n := by
    rw [Nat.le_div_iff_mul_le hn, Nat.mul_comm]
    exact hm
  have hKq : K (m % n) ≤ m / n := hKle.trans hq
  have key : ∀ b : ℕ, b = m % n + n * K (m % n) + n * (m / n - K (m % n)) →
      ∃ r : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L b, ⊤),
        y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L b).nonvanishingLocus r := by
    rintro _ rfl
    exact AlgebraicGeometry.Scheme.Modules.exists_mem_nonvanishingLocus_tensorPow_add_mul L y
      (hK (m % n) y) (hQn y) _
  obtain ⟨r, hr⟩ := key m (by rw [add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hKq, Nat.mod_add_div])
  exact ⟨r, hr⟩

end
