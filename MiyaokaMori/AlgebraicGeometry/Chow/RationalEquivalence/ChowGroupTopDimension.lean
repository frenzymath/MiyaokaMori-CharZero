import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassRat

/-! # The top-dimensional Chow group is spanned by the fundamental class

For an integral scheme `X` with `dim X = n`, the top-dimensional Chow group `CH_n(X)_ℚ` is spanned by
the fundamental class: every class is `r·[X]` (e.g. `CH_1(C)_ℚ = ℚ·[C]` on a curve `C`, so the
pushforward `π_*(H^{s_k−1} ∩ [Y^sp])` in the proof of Proposition 2.4 of the paper is a
multiple of `[C]`).

## Proof

1. `height_genericPoint_eq`: for `X` integral of finite dimension, `height η = dim X`
   (`Order.height_top_eq_krullDim` + `irreducibleSetEquivPoints` + `Scheme.dimension_spec`).
2. `eq_genericPoint_of_height`: `η` is the only point of dimension `n` (`x ≤ η` for all `x`; height is
   strictly monotone at finite heights).
3. `cycle_eq_smul_single`: `Z_n(X) = ℤ·[X]`; an `n`-cycle `c` equals `c(η)·single η 1`, compared pointwise.
4. Surjectivity of the quotient map + `TensorProduct.induction_on`; the `dite` condition of
   `fundamentalClassRat` holds by step 1, so the positive branch is taken.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- An integral scheme is nonempty, so the Krull dimension of its underlying space is not `⊥`. -/
theorem ChowGroupTopDimension.topologicalKrullDim_ne_bot {X : Scheme.{u}} [IsIntegral X] :
    topologicalKrullDim X ≠ ⊥ := by
  unfold topologicalKrullDim
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  exact Order.krullDim_ne_bot_iff.mpr inferInstance

/-- The height of the generic point of an integral scheme is its dimension (when finite). -/
theorem ChowGroupTopDimension.height_genericPoint_eq {X : Scheme.{u}} [IsIntegral X]
    (hX : topologicalKrullDim X ≠ ⊤) :
    Order.height (genericPoint X) = (X.dimension : ℕ∞) := by
  have hk : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints X _ _ _ : TopologicalSpace.IrreducibleCloseds X ≃o X)).symm
  have h1 : ((Order.height (⊤ : X) : ℕ∞) : WithBot ℕ∞) = Order.krullDim X :=
    Order.height_top_eq_krullDim
  rw [hk, X.dimension_spec ChowGroupTopDimension.topologicalKrullDim_ne_bot hX] at h1
  exact WithBot.coe_injective h1

/-- The generic point is the only point of height `height η` (finite): `x ≤ η` (`η` specializes to every
point), and if `x ≠ η` then `x < η`, contradicting the strict monotonicity of the height. -/
theorem ChowGroupTopDimension.eq_genericPoint_of_height {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
    (hη : Order.height (genericPoint X) = (n : ℕ∞)) {x : X} (hx : Order.height x = (n : ℕ∞)) :
    x = genericPoint X := by
  by_contra hne
  have hle : x ≤ genericPoint X := Scheme.le_iff_specializes.mpr (genericPoint_specializes x)
  have hlt : x < genericPoint X := lt_of_le_not_ge hle fun h =>
    hne ((Scheme.le_iff_specializes.mp h).antisymm (Scheme.le_iff_specializes.mp hle)).eq
  have h := Order.height_strictMono hlt (by rw [hx]; exact WithTop.coe_lt_top _)
  rw [hx, hη] at h
  exact lt_irrefl _ h

open Classical in
/-- The single-point cycle with coefficient `1` at a point of height `n` lies in `Z_n(X)`. -/
theorem ChowGroupTopDimension.single_mem_cycleSubgroup {X : Scheme.{u}} {n : ℕ} {η : X}
    (hη : Order.height η = (n : ℕ∞)) :
    Function.locallyFinsuppWithin.single η (1 : ℤ) ∈ cycleSubgroup X n := by
  intro x hx
  rw [Function.locallyFinsuppWithin.single_apply] at hx
  by_cases hxe : x = η
  · subst hxe; exact hη
  · simp [hxe] at hx

open Classical in
/-- `Z_n(X) = ℤ·[X]`: on an integral scheme with `height η = n`, an `n`-cycle equals `c(η)` times the
single-point cycle at `η`. -/
theorem ChowGroupTopDimension.cycle_eq_smul_single {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
    (hη : Order.height (genericPoint X) = (n : ℕ∞)) (c : ↥(cycleSubgroup X n)) :
    c = (c.1 (genericPoint X)) •
      (⟨Function.locallyFinsuppWithin.single (genericPoint X) (1 : ℤ),
        ChowGroupTopDimension.single_mem_cycleSubgroup hη⟩ : ↥(cycleSubgroup X n)) := by
  apply Subtype.ext
  rw [AddSubgroup.coe_zsmul]
  refine Function.locallyFinsuppWithin.ext fun x => ?_
  rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.single_apply]
  by_cases hx : x = genericPoint X
  · subst hx; simp
  · rw [if_neg hx, smul_zero]
    by_contra hne
    exact hx (ChowGroupTopDimension.eq_genericPoint_of_height hη (c.2 x hne))

open Classical in
/-- Every class in `CH_n(X)_ℚ` of an integral scheme of dimension `n` is a rational multiple of the
fundamental class. -/
theorem ChowGroupRat.exists_eq_smul_fundamentalClassRat
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (n : ℕ)
    (hn : X.dimension = n) (hfin : topologicalKrullDim X ≠ ⊤)
    (α : AlgebraicGeometry.ChowGroupRat X n) :
    ∃ r : ℚ, α = r • AlgebraicGeometry.fundamentalClassRat X n hn := by
  have hη : Order.height (genericPoint X) = (n : ℕ∞) := by
    rw [ChowGroupTopDimension.height_genericPoint_eq hfin, hn]
  set e : ↥(cycleSubgroup X n) :=
    ⟨Function.locallyFinsuppWithin.single (genericPoint X) (1 : ℤ),
      ChowGroupTopDimension.single_mem_cycleSubgroup hη⟩ with he
  have hfund : fundamentalClassRat X n hn = ChowGroupRat.of (ChowGroup.mk e) := by
    unfold fundamentalClassRat
    rw [dif_pos hη]
  rw [hfund]
  induction α using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [zero_smul]; rfl⟩
  | tmul q m =>
    obtain ⟨c, rfl⟩ : ∃ c, ChowGroup.mk c = m := QuotientAddGroup.mk'_surjective _ m
    refine ⟨q * (c.1 (genericPoint X) : ℚ), ?_⟩
    show q ⊗ₜ[ℤ] (ChowGroup.mk c) = (q * (c.1 (genericPoint X) : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] ChowGroup.mk e)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    conv_lhs => rw [ChowGroupTopDimension.cycle_eq_smul_single hη c]
    rw [map_zsmul, ← TensorProduct.smul_tmul, zsmul_eq_mul, mul_comm]
  | add x y hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨s, hs⟩ := hy
    exact ⟨r + s, by rw [hr, hs, add_smul]; rfl⟩

end AlgebraicGeometry

end
