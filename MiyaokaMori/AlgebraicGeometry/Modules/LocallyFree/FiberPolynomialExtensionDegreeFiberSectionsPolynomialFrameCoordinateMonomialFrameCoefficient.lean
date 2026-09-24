import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheafOld

/-! # The tensor product of two frames is a frame

Used for the monomial frames `ξ^q` on the fibres of the total space of a line bundle (module
`…FrameCoordinateMonomialFrame`).

* `IsFrame.moduleTensorSection`: if `a` is a frame of `A` on `W` and `b` a frame of `B` on `W`, then the pure
  tensor `a ⊗ b` (`AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b`) is a frame of `A ⊗ B` (`AlgebraicGeometry.Scheme.Modules.moduleTensor A B =
  Modules.tensor A B`) on `W`. Proof (Stacks 01CR/01CY pattern, as in `isFrame_res_nonvanishingLocus`): the
  question is local (`IsFrame.of_iSup`). Near `x ∈ W` take a frame `g` of the line bundle `A ⊗ B` (it is a line
  bundle: `SheafOfModules.IsLineBundle.tensor`) and write `a ⊗ b = f • g` with `f := coord_g(a ⊗ b)`. The germ
  of `a ⊗ b` at `x` generates the stalk `(A ⊗ B)_x ≅ O_x` (the stalk isomorphism of two frames,
  `IsFrame.tensorStalkEquivOfFrames_germ_frame`), so the germ of `f` is a unit, i.e. `x ∈ X_f`
  (`Scheme.mem_basicOpen`); on `X_f` the function `f` is a unit (`RingedSpace.isUnit_res_basicOpen`), so `a ⊗ b`
  is a frame there (`IsFrame.of_isUnit_coord`).
* `IsFrame.moduleTensorPowerSection`: `a^{⊗q}` (`AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection a q`) is a frame of
  `A^{⊗q}` (`AlgebraicGeometry.Scheme.Modules.moduleTensorPower A q`); `q = 0`: `1` is a frame of `O_X`; induction with the previous
  lemma (`SheafOfModules.IsLineBundle.moduleTensorPower`).
* `IsFrame.coefficientLineModule`: for frames `η` of `M` and `t` of `L^∨` on `W`, `η ⊗ t^{⊗q}` is a frame of the
  coefficient line bundle `M ⊗ (L^∨)^{⊗q}` (`AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **The tensor product of two frames is a frame**: `a ⊗ b` is a frame of `A ⊗ B` on `W`. -/
theorem IsFrame.moduleTensorSection {A B : X.Modules} [A.IsLineBundle] [B.IsLineBundle] {W : X.Opens}
    {a : Γ(A, W)} {b : Γ(B, W)} (ha : IsFrame A W a) (hb : IsFrame B W b) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.tensor A B) W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) := by
  let T : X.Modules := AlgebraicGeometry.Scheme.Modules.tensor A B
  have hT : T.IsLineBundle := SheafOfModules.IsLineBundle.tensor A B
  let s : Γ(T, W) := AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b
  have key : ∀ x : X, x ∈ W → ∃ V : X.Opens, ∃ hVW : V ≤ W, x ∈ V ∧ IsFrame T V (T.res hVW s) := by
    intro x hx
    obtain ⟨W₁, hxW₁, e, hf⟩ := exists_frame T x
    have h₂W : W ⊓ W₁ ≤ W := inf_le_left
    have h₂₁ : W ⊓ W₁ ≤ W₁ := inf_le_right
    have hx₂ : x ∈ W ⊓ W₁ := ⟨hx, hxW₁⟩
    have hf₂ : IsFrame T (W ⊓ W₁) (T.res h₂₁ e) := hf.restrict h₂₁
    let f : Γ(X, W ⊓ W₁) := hf₂.coord le_rfl (T.res h₂W s)
    -- `s|_{W₂} = f • e|_{W₂}`
    have hse : T.res h₂W s = f • T.res h₂₁ e := by
      have := hf₂.coord_smul_frame le_rfl (T.res h₂W s)
      rw [res_self] at this
      exact this.symm
    -- `s|_{W₂}` is the tensor of the restricted frames
    have hs₂ : T.res h₂W s = AlgebraicGeometry.Scheme.Modules.moduleTensorSection (A.res h₂W a) (B.res h₂W b) :=
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (homOfLE h₂W) a b
    -- the germ of `f` at `x` is a unit
    have hunit : IsUnit (X.presheaf.germ (W ⊓ W₁) x hx₂ f) := by
      have hΘ := (ha.restrict h₂W).tensorStalkEquivOfFrames_germ_frame (hb.restrict h₂W) hx₂
      have h1 : T.presheaf.germ (W ⊓ W₁) x hx₂
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (A.res h₂W a) (B.res h₂W b)) =
          X.presheaf.germ (W ⊓ W₁) x hx₂ f • T.presheaf.germ (W ⊓ W₁) x hx₂ (T.res h₂₁ e) := by
        rw [← hs₂, hse]
        exact germ_smul' T hx₂ f (T.res h₂₁ e)
      rw [h1, LinearEquiv.map_smul, smul_eq_mul] at hΘ
      exact IsUnit.of_mul_eq_one _ hΘ
    have hmem : x ∈ X.basicOpen f := (X.mem_basicOpen f x hx₂).mpr hunit
    have hle : X.basicOpen f ≤ W ⊓ W₁ := X.basicOpen_le f
    refine ⟨X.basicOpen f, hle.trans h₂W, hmem, ?_⟩
    have hcoord : IsFrame.coord (hf₂.restrict hle) le_rfl (T.res (hle.trans h₂W) s) =
        X.presheaf.map (homOfLE hle).op f := by
      refine IsFrame.coord_unique (hf₂.restrict hle) le_rfl _ _ ?_
      have h1 := congrArg (T.res hle) (hf₂.coord_smul_frame le_rfl (T.res h₂W s))
      have h2 : T.res hle (f • T.res le_rfl (T.res h₂₁ e)) =
          X.presheaf.map (homOfLE hle).op f • T.res le_rfl (T.res hle (T.res h₂₁ e)) := by
        rw [T.res_smul, T.res_self, T.res_self]
      have h3 : T.res hle (T.res h₂W s) = T.res (hle.trans h₂W) s := T.res_res hle h₂W s
      exact h2.symm.trans (h1.trans h3)
    have hu : IsUnit (IsFrame.coord (hf₂.restrict hle) le_rfl (T.res (hle.trans h₂W) s)) := by
      rw [hcoord]
      exact X.toRingedSpace.isUnit_res_basicOpen f
    exact IsFrame.of_isUnit_coord (hf₂.restrict hle) hu
  choose! V hVW hxV hfV using key
  refine IsFrame.of_iSup (ι := (W : Set X)) (fun p => V p.1) (fun p => hVW p.1 p.2) ?_ ?_
  · intro p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hxV p hp⟩
  · intro p
    exact hfV p.1 p.2

/-- `1 ∈ Γ(O_X, W)` is a frame of `O_X = A^{⊗0}` on `W`. -/
theorem isFrame_moduleTensorPower_zero_one (A : X.Modules) (W : X.Opens) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.moduleTensorPower A 0) W (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection (U := W) (M := A) 0 0) := by
  intro W' h
  change Function.Bijective (fun r : Γ(X, W') => r • (AlgebraicGeometry.Scheme.Modules.moduleTensorPower A 0).res h (1 : Γ(X, W)))
  have h1 : (AlgebraicGeometry.Scheme.Modules.moduleTensorPower A 0).res h (1 : Γ(X, W)) = (1 : Γ(X, W')) := by
    change (X.presheaf.map (homOfLE h).op).hom (1 : Γ(X, W)) = 1
    exact map_one _
  rw [h1]
  refine ⟨fun a b hab => ?_, fun b => ⟨b, ?_⟩⟩
  · have hab' : a * (1 : Γ(X, W')) = b * (1 : Γ(X, W')) := hab
    rwa [mul_one, mul_one] at hab'
  · exact @mul_one Γ(X, W') _ b

/-- **The tensor power of a frame is a frame**: `a^{⊗q}` is a frame of `A^{⊗q}` on `W`. -/
theorem IsFrame.moduleTensorPowerSection {A : X.Modules} [A.IsLineBundle] {W : X.Opens} {a : Γ(A, W)}
    (ha : IsFrame A W a) (q : ℕ) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.moduleTensorPower A q) W (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection a q) := by
  induction q with
  | zero => exact isFrame_moduleTensorPower_zero_one A W
  | succ q ih => exact IsFrame.moduleTensorSection ha ih

/-- **A frame of the coefficient line bundle**: for frames `η` of `M` and `t` of `L^∨` on `W`, `η ⊗ t^{⊗q}` is a
frame of `M ⊗ (L^∨)^{⊗q} = AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q`. -/
theorem IsFrame.coefficientLineModule {M L : X.Modules} [M.IsLineBundle] [L.IsLineBundle] {W : X.Opens}
    {η : Γ(M, W)} {t : Γ(AlgebraicGeometry.Scheme.Modules.moduleSheafDual L, W)} (hη : IsFrame M W η)
    (ht : IsFrame (AlgebraicGeometry.Scheme.Modules.moduleSheafDual L) W t) (q : ℕ) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q) W
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection η (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q)) :=
  haveI : (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L q).IsLineBundle :=
    SheafOfModules.IsLineBundle.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.moduleSheafDual L) q
  IsFrame.moduleTensorSection hη (ht.moduleTensorPowerSection q)

end AlgebraicGeometry.Scheme.Modules

end
