import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlas

/-! # Reindexing a weighted polynomial atlas

Transport of a weighted polynomial atlas along an equivalence of variable index sets: if
`e : σ ≃ τ` and `w' ∘ e = w`, then `WeightedPolynomialAtlas S w → WeightedPolynomialAtlas S w'`
(`WeightedPolynomialAtlas.reindex`). The supporting lemma
`MvPolynomial.IsWeightedHomogeneous.rename_of` says that renaming variables along an injection
preserves weighted homogeneity when the weights correspond via `w' ∘ e = w`.

The same family of jet coordinates of weight `q + 1` is indexed differently in different places
(`Fin r × ι` versus `ULift (Fin (n+1) × Fin r)` with weight `iq.down.2 + 1`); the two spellings
differ only by an index equivalence, which this file transports.
-/

set_option autoImplicit false
universe u
open CategoryTheory Opposite
noncomputable section

/-- Renaming variables along an injection preserves weighted homogeneity, provided the weights
correspond (`w' (e i) = w i`). -/
theorem MvPolynomial.IsWeightedHomogeneous.rename_of {σ τ R : Type*} [CommSemiring R]
    {w : σ → ℕ} {w' : τ → ℕ} {e : σ → τ} (he : Function.Injective e)
    (hw : ∀ i, w' (e i) = w i) {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsWeightedHomogeneous w n) :
    (MvPolynomial.rename e p).IsWeightedHomogeneous w' n := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  | add p q _ _ ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d a hd =>
    rw [MvPolynomial.rename_monomial]
    refine MvPolynomial.isWeightedHomogeneous_monomial _ _ _ ?_
    rw [← hd, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index_inj he]
    exact Finsupp.sum_congr fun i _ => by rw [hw]

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} {S : X.GradedAffineAlgebra} {σ τ : Type u} {w : σ → ℕ} {w' : τ → ℕ}

/-- Transport of an atlas along an equivalence of index sets with compatible weights. -/
def WeightedPolynomialAtlas.reindex (e : σ ≃ τ) (hw : ∀ i, w' (e i) = w i)
    (𝒜 : S.WeightedPolynomialAtlas w) : S.WeightedPolynomialAtlas w' where
  I := 𝒜.I
  chart := 𝒜.chart
  covers := 𝒜.covers
  equiv i := (𝒜.equiv i).trans (MvPolynomial.renameEquiv _ e).toRingEquiv
  equiv_grading i m a := by
    have hw' : ∀ j, w (e.symm j) = w' j := fun j => by
      rw [← hw (e.symm j), e.apply_symm_apply]
    show _ ↔ (MvPolynomial.rename e (𝒜.equiv i a)).IsWeightedHomogeneous w' m
    rw [𝒜.equiv_grading i m a]
    refine ⟨fun h => h.rename_of e.injective hw, fun h => ?_⟩
    have h2 := h.rename_of e.symm.injective hw'
    rwa [MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id] at h2
  equiv_unit i r := by
    show MvPolynomial.rename e (𝒜.equiv i _) = MvPolynomial.C r
    rw [𝒜.equiv_unit i r, MvPolynomial.rename_C]

end AlgebraicGeometry.Scheme.GradedAffineAlgebra
end
