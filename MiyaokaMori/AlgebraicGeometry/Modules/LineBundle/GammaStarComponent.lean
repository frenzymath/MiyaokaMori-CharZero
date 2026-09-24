import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionRing
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus

/-! # Homogeneous components of the section ring of a line bundle

Homogeneous elements of the section ring `Γ_*(X, L) = ⊕_n Γ(X, L^{⊗n})` (`gammaStar L`) and their sections.

For `x ∈ Γ_*(X, L)_m` the `m`-th component `gammaStarComponent L x m ∈ Γ(X, L^{⊗m})` is the
section it represents. This file records the bridge between the ring structure of `Γ_*(X, L)`
(multiplication `sectionsGMul` = tensor of sections followed by `tensorPowAddIso⁻¹`) and the
line-bundle geometry of the components:

* `gammaStarComponent_mul`: the `(m+n)`-component of `x * y` is `sectionsGMul x_m y_n`;
* `nonvanishingLocus_sectionsGMul`: `X_{a·b} = X_a ⊓ X_b` (Stacks 01CY for a product, via
  `nonvanishingLocus_sectionTensor`);
* `nonvanishingLocus_gammaStarComponent_congr`: the nonvanishing locus of a homogeneous element
  does not depend on the degree witness (either `x = 0` and both loci are `⊥`, or the degrees
  agree by `DirectSum.degree_eq_of_mem_mem`);
* `nonvanishingLocus_pow_gammaStarOf`: `X_{s^n} = X_s` for `n > 0`;
* `coord_sectionsGMul`: in frames `x|_U`, `y|_U`, `(x·y)|_U` the coordinates are multiplicative:
  `coord_{xy}(a·b) = coord_x(a) · coord_y(b)`.

These are exactly the facts needed to build the ring map `Γ_*(X, L)_{(s)} → Γ(X_s, O_X)`,
`a/s^n ↦ a · s^{-n}` of Stacks 01PZ (`GammaStarAwayRingHom`).

Reference: Stacks 01PZ (`properties-lemma-map-into-proj`), the sentence "the ring map
`S_{(s)} → Γ(X_s, O_X)`, `a/s^n ↦ a ⊗ s^{-n}`"; Stacks 01CY (`X_s` and frames).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `X_0 = ⊥`: the germ of `0` lies in `𝔪_x • M_x`. -/
theorem nonvanishingLocus_zero (M : X.Modules) [M.IsLineBundle] :
    M.nonvanishingLocus (0 : Γ(M, ⊤)) = ⊥ := by
  apply le_bot_iff.mp
  intro y hy
  refine (hy : _ ∉ _) ?_
  rw [map_zero]
  exact Submodule.zero_mem _

/-- The restriction of a global section to any open contained in its nonvanishing locus is a
frame. -/
theorem isFrame_res_of_le_nonvanishingLocus (M : X.Modules) [M.IsLineBundle] (s : Γ(M, ⊤))
    {U : X.Opens} (hU : U ≤ M.nonvanishingLocus s) : IsFrame M U (M.res le_top s) := by
  have h := (isFrame_res_nonvanishingLocus M s).restrict hU
  rwa [res_res] at h

variable (L : X.Modules) [L.IsLineBundle]

/-! ## Components of homogeneous elements -/

theorem gammaStarComponent_gammaStarOf (n : ℕ) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf L n s) n = s := by
  show (DirectSum.of ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsPiece ⊤) n s) n = s
  exact DirectSum.of_eq_same (β := (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsPiece ⊤) n s

theorem gammaStarOf_gammaStarComponent {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {n : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L n) :
    AlgebraicGeometry.Scheme.Modules.gammaStarOf L n
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x n) = x := by
  obtain ⟨s, rfl⟩ := hx
  show DirectSum.of _ n ((DirectSum.of _ n s) n) = DirectSum.of _ n s
  rw [DirectSum.of_eq_same]

theorem gammaStarComponent_zero (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.gammaStarComponent L 0 n = 0 := rfl

theorem gammaStarComponent_add (x y : AlgebraicGeometry.Scheme.Modules.gammaStar L) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x + y) n =
      AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x n +
        AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y n := rfl

theorem gammaStarComponent_neg (x : AlgebraicGeometry.Scheme.Modules.gammaStar L) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (-x) n =
      -AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x n := rfl

/-- The `(m + n)`-component of a product of homogeneous elements is the graded product of the
components (`DirectSum.of_mul_of`). -/
theorem gammaStarComponent_mul {x y : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m n : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m)
    (hy : y ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L n) :
    AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x * y) (m + n) =
      (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y n) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  show (DirectSum.of _ m a * DirectSum.of _ n b) (m + n) = _
  rw [DirectSum.of_mul_of, DirectSum.of_eq_same]
  show GradedMonoid.GMul.mul a b =
    (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤
      ((DirectSum.of ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsPiece ⊤) m a) m)
      ((DirectSum.of ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsPiece ⊤) n b) n)
  rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
  rfl

/-- The `0`-component of `1` is `1 ∈ Γ(X, O_X)`. -/
theorem gammaStarComponent_one :
    AlgebraicGeometry.Scheme.Modules.gammaStarComponent L 1 0 = (1 : Γ(X, ⊤)) := by
  show (DirectSum.of ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsPiece ⊤) 0
    GradedMonoid.GOne.one) 0 = (1 : Γ(X, ⊤))
  rw [DirectSum.of_eq_same]
  rfl

/-! ## Nonvanishing loci -/

/-- `X_{a·b} = X_a ⊓ X_b` for the graded product of sections of `L^{⊗m}` and `L^{⊗n}`. -/
theorem nonvanishingLocus_sectionsGMul {m n : ℕ}
    (a : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤))
    (b : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n)).nonvanishingLocus
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤ a b) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus a ⊓
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus b := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤ a b =
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n) ≪≫
        (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m n).symm).hom.app ⊤
        (sectionTensor a b) := rfl
  have h2 := AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m n).symm) (sectionTensor a b)
  rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_sectionTensor] at h2
  rw [h1]
  exact h2

/-- The nonvanishing locus of a homogeneous element does not depend on the degree witness. -/
theorem nonvanishingLocus_gammaStarComponent_congr
    {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m m' : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m)
    (hx' : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m') :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m').nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m') := by
  by_cases h0 : x = 0
  · subst h0
    rw [gammaStarComponent_zero, gammaStarComponent_zero, nonvanishingLocus_zero,
      nonvanishingLocus_zero]
  · obtain rfl := DirectSum.degree_eq_of_mem_mem (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      hx hx' h0
    rfl

/-- The `0`-component of `1` is nowhere vanishing. -/
theorem nonvanishingLocus_gammaStarComponent_one :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L 0).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L 1 0) = ⊤ := by
  rw [gammaStarComponent_one]
  exact nonvanishingLocus_tensorPowSection_zero L (0 : Γ(L, ⊤))

/-- `X_{s^{n+1}} = X_s`, where `s^{n+1}` is read in its natural degree `(n+1) • d`. -/
theorem nonvanishingLocus_pow_succ_gammaStarOf (d : ℕ)
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L ((n + 1) • d)).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s ^ (n + 1)) ((n + 1) • d)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s := by
  induction n with
  | zero =>
    have h1 : AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s ^ (0 + 1) ∈
        AlgebraicGeometry.Scheme.Modules.gammaStarGrading L d := by
      rw [zero_add, pow_one]; exact AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s
    rw [nonvanishingLocus_gammaStarComponent_congr L
      (SetLike.pow_mem_graded (0 + 1) (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s)) h1,
      zero_add, pow_one, gammaStarComponent_gammaStarOf]
  | succ k ih =>
    have hk := SetLike.pow_mem_graded (k + 1) (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s)
    have h1 : AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s ^ (k + 1 + 1) ∈
        AlgebraicGeometry.Scheme.Modules.gammaStarGrading L ((k + 1) • d + d) := by
      rw [pow_succ]
      exact SetLike.mul_mem_graded hk (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s)
    rw [nonvanishingLocus_gammaStarComponent_congr L
      (SetLike.pow_mem_graded (k + 1 + 1) (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s)) h1,
      pow_succ, gammaStarComponent_mul L hk (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s),
      nonvanishingLocus_sectionsGMul, ih, gammaStarComponent_gammaStarOf, inf_idem]

/-- **`X_{s^n} = X_s` for `n > 0`** (Stacks 01PT, in the section ring). -/
theorem nonvanishingLocus_pow_gammaStarOf (d : ℕ)
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)) {n : ℕ} (hn : 0 < n) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d)).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s ^ n) (n • d)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact nonvanishingLocus_pow_succ_gammaStarOf L d s k

/-- `X_s ≤ X_{s^n}` for every `n` (for `n = 0` the right side is `⊤`). -/
theorem nonvanishingLocus_le_nonvanishingLocus_pow_gammaStarOf (d : ℕ)
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s ≤
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d)).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s ^ n) (n • d)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s ^ 0 ∈
        AlgebraicGeometry.Scheme.Modules.gammaStarGrading L 0 := by
      rw [pow_zero]; exact SetLike.one_mem_graded _
    rw [nonvanishingLocus_gammaStarComponent_congr L
      (SetLike.pow_mem_graded 0 (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s)) h1,
      pow_zero, nonvanishingLocus_gammaStarComponent_one]
    exact le_top
  · rw [nonvanishingLocus_pow_gammaStarOf L d s hn]

/-! ## Frames and coordinates -/

/-- Scalars pull out of the graded product of sections (bilinearity of `tensorSections` and
`O_X`-linearity of the multiplication map). -/
theorem sectionsGMul_smul_smul (U : X.Opens) {m n : ℕ} (α β : Γ(X, U))
    (x : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, U))
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul U (α • x) (β • y) =
      @HSMul.hSMul Γ(X, U) Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n), U)
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n), U) _ (α * β)
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul U x y) := by
  show ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).mul m n).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n) U (α • x) (β • y)) =
    @HSMul.hSMul Γ(X, U) Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n), U)
      Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n), U) _ (α * β)
      (((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).mul m n).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n) U x y))
  rw [AlgebraicGeometry.Scheme.Modules.tensorSections_smul_left _ _ U α x (β • y) _ rfl,
    AlgebraicGeometry.Scheme.Modules.tensorSections_smul_right _ _ U β x y _ rfl]
  refine (AlgebraicGeometry.Scheme.Modules.Hom.app_smul _ α _).trans ?_
  refine (congrArg (fun w => α • w) (AlgebraicGeometry.Scheme.Modules.Hom.app_smul _ β _)).trans ?_
  exact smul_smul α β _

/-- The graded product commutes with restriction (`res` form of `sectionsGMul_restrict`). -/
theorem res_sectionsGMul {U : X.Opens} {m n : ℕ}
    (x : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤))
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n)).res le_top
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤ x y) =
      (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul U
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).res le_top x)
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).res le_top y) :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul_restrict (le_top : U ≤ ⊤) x y

/-- If `x|_U` and `y|_U` are frames then `(x·y)|_U` is a frame. -/
theorem isFrame_res_sectionsGMul {U : X.Opens} {m n : ℕ}
    {x : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤)}
    {y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)}
    (hx : IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L m) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).res le_top x))
    (hy : IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L n) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).res le_top y)) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n)) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n)).res le_top
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤ x y)) := by
  apply isFrame_res_of_le_nonvanishingLocus
  rw [nonvanishingLocus_sectionsGMul]
  exact le_inf hx.le_nonvanishingLocus hy.le_nonvanishingLocus

/-- **Coordinates are multiplicative**: `coord_{x·y}(a·b) = coord_x(a) · coord_y(b)`. -/
theorem coord_sectionsGMul {U : X.Opens} {m n : ℕ}
    {x : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤)}
    {y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)}
    (hx : IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L m) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).res le_top x))
    (hy : IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L n) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).res le_top y))
    (hxy : IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n)) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n)).res le_top
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤ x y)))
    (a : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤))
    (b : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)) :
    hxy.coord le_rfl ((AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n)).res le_top
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤ a b)) =
      hx.coord le_rfl ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).res le_top a) *
        hy.coord le_rfl ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).res le_top b) := by
  apply hxy.coord_unique
  rw [res_self]
  have ha := hx.coord_smul_frame le_rfl ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).res le_top a)
  have hb := hy.coord_smul_frame le_rfl ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).res le_top b)
  rw [res_self] at ha hb
  rw [res_sectionsGMul L a, res_sectionsGMul L x, ← sectionsGMul_smul_smul, ha, hb]

end AlgebraicGeometry.Scheme.Modules

end
