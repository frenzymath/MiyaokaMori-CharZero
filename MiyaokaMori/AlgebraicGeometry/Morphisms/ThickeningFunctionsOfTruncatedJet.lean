import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetThickeningSectionsCoeff

/-! # Functions on the thickening `T ×_k D_κ` from truncated polynomials over a field

A helper for the local independence of jets (Lemma 3.1 of the paper).

For a `k`-scheme `T` and a ring map `ε : K → Γ(T, ⊤)`, the composite
`K[t]/(t^{κ+1}) → Γ(T, ⊤)[t]/(t^{κ+1}) → Γ(T ×_k D_κ, pr⁻¹⊤)` (`GlobalTruncatedParameterAPI.map ε`,
`jetThickening.sectionsHom`) has `t^n`-coefficient `ε (coeff n z)` (`coeff_evalToThickening`) and is injective
when `ε` is (`evalToThickening_injective`; `TruncatedJetRing.ext_coeff`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace jetThickening

variable (k : Type u) [Field k] (κ : ℕ) (T : AlgebraicGeometry.Scheme.{u})
  [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (K : Type u) [CommRing K] (ε : K →+* Γ(T, ⊤))

/-- `K[t]/(t^{κ+1}) → Γ(T ×_k D_κ, pr⁻¹⊤)`: coefficients through `ε`, `t ↦` the parameter. -/
def evalToThickening :
    MiyaokaMori.Jet.TruncatedJetRing K κ →+* Γ(jetThickening (k := k) κ T, jetThickeningProj (k := k) κ T ⁻¹ᵁ ⊤) :=
  (jetThickening.sectionsHom (k := k) κ T ⊤).comp (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map κ ε)

theorem coeff_evalToThickening (z : MiyaokaMori.Jet.TruncatedJetRing K κ) (n : ℕ) (hn : n ≤ κ) :
    jetThickening.coeff (k := k) κ T ⊤ n hn (evalToThickening k κ T K ε z) =
      ε (MiyaokaMori.Jet.TruncatedJetRing.coeff κ n hn z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  show jetThickening.coeff (k := k) κ T ⊤ n hn (jetThickening.sectionsHom (k := k) κ T ⊤
    (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map κ ε (MiyaokaMori.Jet.jetProjection K κ p))) =
    ε (MiyaokaMori.Jet.TruncatedJetRing.coeff κ n hn (MiyaokaMori.Jet.jetProjection K κ p))
  rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection, jetThickening.coeff_sectionsHom,
    MiyaokaMori.Jet.TruncatedJetRing.coeff_jetProjection, MiyaokaMori.Jet.TruncatedJetRing.coeff_jetProjection,
    Polynomial.coeff_map]

theorem evalToThickening_injective (hε : Function.Injective ε) :
    Function.Injective (evalToThickening k κ T K ε) := by
  intro z₁ z₂ h
  apply MiyaokaMori.Jet.TruncatedJetRing.ext_coeff κ
  intro n hn
  apply hε
  rw [← coeff_evalToThickening k κ T K ε z₁ n hn, ← coeff_evalToThickening k κ T K ε z₂ n hn, h]

end jetThickening

end
