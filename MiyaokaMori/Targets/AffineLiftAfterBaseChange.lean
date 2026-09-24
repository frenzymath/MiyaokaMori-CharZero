import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCore

/-! # An affine lift after finite base change

**Lemma 3.1** of the paper.** Let `Γ`, `τ₀ : C̃₀ → Y_k^GG` and `ρ₀` be supplied by
Lemma 2.5. There is a finite surjective morphism `ρ₁ : C̃ → C̃₀` from a smooth
connected projective curve; set `ρ = ρ₀ ∘ ρ₁`, `τ = τ₀ ∘ ρ₁`. Then there are an ordinary line bundle
`L` on `C̃` and a morphism over `C`

  `ȷ : C̃_(k)(L) → 𝒵^×`

restricting to `s ∘ ρ` on the zero section, whose positive-order coefficient tuple is nowhere zero and
whose weighted projectivization is `τ`.

This file is the target-level restatement; the theorem is `weighted_rescaling`
(`Paper/S3PositiveLine/Rescaling/PositiveLineCore.lean`), whose docstring carries the proof sketch
(weighted-projective point of `τ₀` at the generic point, `q`-th roots after a finite extension taken
simultaneously for the finitely many charts, normalization `ρ₁`, the parameter line `L = O(Σ w_y [y])`
from the weighted orders, normalized coefficients regular with a unit at every point, gluing of the
local based jets, agreement of the projectivization with `τ` generically and hence everywhere by
separatedness). Dictionary: `ν₀` is the paper's `τ₀` (the statement takes any `k`-morphism
`ν₀ : C̃₀ → Y_k^GG` with `ν₀ ≫ π_k` finite, surjective and generic point to generic point — the three
properties the proof uses; Lemma `negative_horizontal` supplies `ν₀ = ν ≫ Γ.ι`); `η` is `ρ₁`;
`J : BasedJet f ρ L κ` is `ȷ` (a morphism over `C` restricting to `s ∘ ρ` on the zero section:
`BasedJet.over`, `BasedJet.restrict`); `NormalizedTupleNowhereZero J` is "its positive-order
coefficient tuple is nowhere zero"; `J.projectivize hnz = η ≫ ν₀` is "its weighted projectivization
is `τ`".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **An affine lift after finite base change** (Lemma 3.1 of the paper). For `ν₀ : C̃₀ → Y_κ^GG` over `k` with
`ν₀ ≫ π_κ` finite, surjective and generic point to generic point, there are a finite cover `ρ : C̃ → C` factoring as
`ρ = η ≫ ν₀ ≫ π_κ` (`η` finite, generic point to generic point), a line bundle `L` on `C̃` and a based jet
`J : C̃_(κ)(L) → 𝒵` over `ρ` with nowhere-zero normalized coefficient tuple whose weighted projectivization is `η ≫ ν₀`. -/
theorem affine_lift_after_base_change {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (hκ : 1 ≤ κ)
    {Ct₀ : SmoothProjectiveCurve k} (ν₀ : Ct₀.toScheme ⟶ YGG f κ)
    [ν₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsFinite (ν₀ ≫ YGG.proj f κ)]
    (hsurj : Function.Surjective (ν₀ ≫ YGG.proj f κ).base)
    (hgen : (ν₀ ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme) :
    ∃ (ρ : FiniteCover k C) (η : ρ.source.toScheme ⟶ Ct₀.toScheme)
      (_ : AlgebraicGeometry.IsFinite η)
      (_ : η.base (genericPoint ρ.source.toScheme) = genericPoint Ct₀.toScheme)
      (_ : ρ.hom = η ≫ ν₀ ≫ YGG.proj f κ)
      (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
      (hnz : NormalizedTupleNowhereZero J),
      J.projectivize hnz = η ≫ ν₀ :=
  weighted_rescaling f κ hκ ν₀ hsurj hgen

end
