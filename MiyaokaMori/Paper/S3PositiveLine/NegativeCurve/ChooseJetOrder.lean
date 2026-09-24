import MiyaokaMori.Paper.S3PositiveLine.Realization.RealizationOrderChoice

/-! # Choosing the jet order

Choice of the jet order `k`: for every rational `c` and every `d > 0` there is `κ ≥ 1` with `c < d·h_κ` (with
`c = 2(n+1)δa` this is equation (4.2) of Theorem 4.2 of the paper; the choice is also
used in Lemma 5.1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

noncomputable section

theorem choose_jet_order (c d : ℚ) (hd : 0 < d) :
    ∃ κ : ℕ, 1 ≤ κ ∧ c < d * harmonic κ := by
  obtain ⟨κ, hκ, hineq⟩ :=
    MiyaokaMori.Jet.exists_realization_order d (c / 2) 0 1 0 hd
  refine ⟨κ, ?_, ?_⟩
  · simpa using hκ
  · convert hineq using 1 <;> norm_num <;> ring

end
