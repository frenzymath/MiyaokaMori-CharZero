import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.Paper.S4Completion.GeneralFiberDegree

/-! # The embedding degree bound

`deg(Φ^*O_X(1)|_F) ≤ r₀ < 2(n+1)ka/(d h_k)` (equation (4.5), Corollary 4.3
of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

def EmbeddingDegreeBound {k : Type u} [Field k] [IsAlgClosed k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} {X : SmoothProjectiveVariety k}
    (Φ : S.toScheme ⟶ X.toScheme) (π : S.toScheme ⟶ C.toScheme)
    (hπ : AlgebraicGeometry.Surjective π) (r₀ : ℕ) : Prop :=
  ∃ V : Set C.toScheme, IsOpen V ∧ V.Nonempty ∧
    ∀ y ∈ V, IsClosed ({y} : Set C.toScheme) →
      fiberDegree π hπ (LineBundle.pullback Φ (X.OX 1)) y ≤ (r₀ : ℤ)

theorem r0_lt_embedding_bound {a e dL d : ℤ} {n κ r₀ : ℕ}
    (hdL : 0 < dL) (he : 0 < e) (hκ : 1 ≤ κ) (hd : 0 < d) (ha : 0 < a)
    (hr₀ : (r₀ : ℤ) = a * e / dL)
    (hslope : (dL : ℚ) / (e : ℚ) > ((d : ℚ) * harmonic κ) / (2 * (n + 1) * (κ : ℚ))) :
    (r₀ : ℚ) < 2 * ((n : ℚ) + 1) * (κ : ℚ) * (a : ℚ) / ((d : ℚ) * harmonic κ) := by
  have hκ0 : 0 < κ := by omega
  have hharm : (0 : ℚ) < harmonic κ := harmonic_pos hκ0.ne'
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have heQ : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he
  have hdLQ : (0 : ℚ) < (dL : ℚ) := by exact_mod_cast hdL
  have haQ : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hDQ : (0 : ℚ) < (d : ℚ) * harmonic κ := mul_pos hdQ hharm
  have hBQ : (0 : ℚ) < 2 * ((n : ℚ) + 1) * (κ : ℚ) := by positivity
  have hslope' : ((d : ℚ) * harmonic κ) /
      (2 * ((n : ℚ) + 1) * (κ : ℚ)) < (dL : ℚ) / (e : ℚ) := hslope
  have hcross : ((d : ℚ) * harmonic κ) * (e : ℚ) <
      (dL : ℚ) * (2 * ((n : ℚ) + 1) * (κ : ℚ)) := by
    exact (div_lt_div_iff₀ hBQ heQ).mp hslope'
  have hEoverL : (e : ℚ) / (dL : ℚ) <
      (2 * ((n : ℚ) + 1) * (κ : ℚ)) / ((d : ℚ) * harmonic κ) := by
    apply (div_lt_div_iff₀ hdLQ hDQ).2
    nlinarith [hcross]
  have hAquot : ((a : ℚ) * (e : ℚ)) / (dL : ℚ) <
      (2 * ((n : ℚ) + 1) * (κ : ℚ) * (a : ℚ)) /
        ((d : ℚ) * harmonic κ) := by
    have hmul := mul_lt_mul_of_pos_left hEoverL haQ
    simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hfloor_int : (a * e / dL : ℤ) * dL ≤ a * e :=
    Int.ediv_mul_le _ (ne_of_gt hdL)
  have hfloorQ : ((a * e / dL : ℤ) : ℚ) ≤
      ((a : ℚ) * (e : ℚ)) / (dL : ℚ) := by
    apply (le_div_iff₀ hdLQ).2
    exact_mod_cast hfloor_int
  have hr₀Q : (r₀ : ℚ) = ((a * e / dL : ℤ) : ℚ) := by
    exact_mod_cast hr₀
  rw [hr₀Q]
  exact hfloorQ.trans_lt hAquot

end
