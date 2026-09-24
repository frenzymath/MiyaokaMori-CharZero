import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The nonvanishing locus of a tensor power of a section

The nonvanishing locus of the tensor power `s^{⊗b} ∈ Γ(L^{⊗b})` (`tensorPowSection`) of a global
section of a line bundle: for `b ≥ 1`, `X_{s^{⊗b}} = X_s` (the `X_{σ^n} = X_σ` in the proof of
Stacks 01PT); for `b = 0`, `s^{⊗0} = 1 ∈ Γ(O_X)` and the nonvanishing locus is `⊤`.

References: the proof of Stacks 01PT (`properties-lemma-ample-power`); Stacks 01CY.

Proof:
* `1 ∈ Γ(O_X, ⊤)` is a frame of the structure sheaf (`r ↦ r • 1 = r` is bijective), and frames are
  nowhere zero (`IsFrame.le_nonvanishingLocus`), so `X_1 = ⊤`.
* `tensorPowSection s (b+1) = sectionTensor (tensorPowSection s b) s`, and `X_{σ ⊗ τ} = X_σ ⊓ X_τ`
  (`nonvanishingLocus_sectionTensor`) with the induction hypothesis give
  `X_{s^{⊗(b+1)}} = X_{s^{⊗b}} ⊓ X_s = X_s`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `1` is a frame of `L^{⊗0} = O_X` on every open: `r ↦ r • 1 = r`. -/
theorem isFrame_tensorPow_zero_one (L : X.Modules) (W : X.Opens) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L 0) W (1 : Γ(X, W)) := by
  intro W' h
  have h1 : (AlgebraicGeometry.Scheme.Modules.tensorPow L 0).res h (1 : Γ(X, W)) =
      (1 : Γ(X, W')) := by
    change (X.presheaf.map (homOfLE h).op).hom (1 : Γ(X, W)) = 1
    exact map_one _
  rw [h1]
  refine ⟨fun a b hab => ?_, fun b => ⟨b, ?_⟩⟩
  · have hab' : a * (1 : Γ(X, W')) = b * (1 : Γ(X, W')) := hab
    rwa [mul_one, mul_one] at hab'
  · exact @mul_one Γ(X, W') _ b

/-- `X_{s^{⊗0}} = ⊤` (`s^{⊗0} = 1 ∈ Γ(O_X)`, and `1` is a frame, which is nowhere zero). -/
theorem nonvanishingLocus_tensorPowSection_zero (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L 0).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s 0) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  exact IsFrame.germ_notMem_maximalIdeal_smul (isFrame_tensorPow_zero_one L ⊤) (y := x) trivial

/-- `X_{s^{⊗(b+1)}} = X_s`. -/
theorem nonvanishingLocus_tensorPowSection_succ (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) (b : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (b + 1)).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (b + 1)) = L.nonvanishingLocus s := by
  induction b with
  | zero =>
    have h := nonvanishingLocus_sectionTensor (AlgebraicGeometry.Scheme.Modules.tensorPow L 0) L
      ((AlgebraicGeometry.Scheme.Modules.tensorPowSection (s : (L.val.obj (Opposite.op ⊤) : Type u)) 0 :
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L 0, ⊤))) s
    rw [nonvanishingLocus_tensorPowSection_zero, top_inf_eq] at h
    exact h
  | succ b ih =>
    have h := nonvanishingLocus_sectionTensor (AlgebraicGeometry.Scheme.Modules.tensorPow L (b + 1)) L
      ((AlgebraicGeometry.Scheme.Modules.tensorPowSection (s : (L.val.obj (Opposite.op ⊤) : Type u)) (b + 1) :
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (b + 1), ⊤))) s
    rw [ih, inf_idem] at h
    exact h

/-- **The nonvanishing locus of a positive tensor power of a section is unchanged**: for `0 < b`,
`X_{s^{⊗b}} = X_s` (proof of Stacks 01PT). -/
theorem nonvanishingLocus_tensorPowSection (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) {b : ℕ}
    (hb : 0 < b) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L b).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s b) = L.nonvanishingLocus s := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hb
  rw [Nat.zero_add]
  exact nonvanishingLocus_tensorPowSection_succ L s c

end AlgebraicGeometry.Scheme.Modules

end
