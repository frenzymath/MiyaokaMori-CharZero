import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.TruncatedJetRingRescale
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickeningSections

/-! # The `t`-coefficients of functions on a jet thickening

The `t`-coefficients of functions on the thickening `W ×_k D_r`. The map
`sectionsHom : Γ(W,V)[t]/(t^{r+1}) → Γ(W ×_k D_r, pr⁻¹V)` is a bijection (`JetThickeningSections`); its inverse
followed by "take the `n`-th coefficient" is `jetThickening.coeff r W V n : Γ(W ×_k D_r, pr⁻¹V) → Γ(W, V)` (`n ≤ r`).
Then: (a) `coeff n (sectionsHom p)` is the `n`-th coefficient of `p`; (b) a truncated polynomial is determined by
its coefficients of orders `0..r`, so `x = y` when all coefficients agree (`ext_coeff`); (c) `coeff` is additive;
(d) `coeff` is natural with respect to restriction: for `V' ≤ V`, `coeff n (x|_{pr⁻¹V'}) = (coeff n x)|_{V'}`;
(e) `coeff n (pr^♯(a)·t^m) = a` if `n = m` and `0` otherwise.
This is the computational handle on `relativeJetScheme.ofBasedJetSections` (coefficients taken through
`RingEquiv.ofBijective … |>.symm`).

Proof:
1. (a): in the definition of `coeff`, `(RingEquiv.ofBijective _ h).symm (sectionsHom p) = p` (`RingEquiv.symm_apply_apply`).
2. (b): lift the elements of the `TruncatedJetRing` to polynomials `p`, `q`; equal coefficients for all `n ≤ r` give
   `X^{r+1} ∣ p - q` (`Polynomial.X_pow_dvd_iff`), hence equality in the quotient; transport to sections by the
   bijectivity of `sectionsHom`.
3. (c): the inverse of a `RingEquiv` is additive, `Polynomial.coeff_add`.
4. (d): first `sectionsHom` is natural with respect to restriction (`sectionsHom_restrict`): both sides are ring
   homomorphisms out of the quotient ring `R[t]/(t^{r+1})`; on `C a` they agree by naturality of
   `(jetThickeningProj).app` (`Scheme.Hom.naturality`), on `t` both are the restriction of the parameter `t`
   (functoriality of `presheaf.map`); `Ideal.Quotient.ringHom_ext` + `Polynomial.ringHom_ext`. Then apply (a) to
   `x = sectionsHom p`.
5. (e): `pr^♯(a)·t^m = sectionsHom(jetProjection (monomial m a))` (value of `eval₂` on a monomial), then (a) and
   `Polynomial.coeff_monomial`.
Source: §2 of the paper (the graded coordinate algebra of jets).
-/

-- `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with `jetProjection_surjective` (so that
-- `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and `Ideal.Quotient.lift_mk` is rewritten with
-- `erw` (it matches only up to unfolding `AdjoinRoot`).

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

-- `MiyaokaMori.Jet.TruncatedJetRing.ext_coeff` and `MiyaokaMori.Jet.TruncatedJetRing.coeff_jetProjection` live upstream
-- (`TruncatedJet`, next to `coeff`) and are imported here.

variable {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
  [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- The `n`-th `t`-coefficient of a function on the thickening (the inverse of `sectionsHom` followed by taking the
coefficient). -/
def jetThickening.coeff (V : W.Opens) (n : ℕ) (hn : n ≤ r)
    (x : Γ(jetThickening (k := k) r W, jetThickeningProj (k := k) r W ⁻¹ᵁ V)) : Γ(W, V) :=
  MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn
    ((RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W V)).symm x)

theorem jetThickening.coeff_sectionsHom (V : W.Opens) (n : ℕ) (hn : n ≤ r)
    (p : MiyaokaMori.Jet.TruncatedJetRing Γ(W, V) r) :
    jetThickening.coeff (k := k) r W V n hn (jetThickening.sectionsHom (k := k) r W V p) =
      MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn p := by
  unfold jetThickening.coeff
  exact congrArg _ ((RingEquiv.ofBijective _
    (jetThickening.sectionsHom_bijective (k := k) r W V)).symm_apply_apply p)

theorem jetThickening.ext_coeff (V : W.Opens)
    (x y : Γ(jetThickening (k := k) r W, jetThickeningProj (k := k) r W ⁻¹ᵁ V))
    (h : ∀ (n : ℕ) (hn : n ≤ r), jetThickening.coeff (k := k) r W V n hn x =
      jetThickening.coeff (k := k) r W V n hn y) : x = y := by
  have := MiyaokaMori.Jet.TruncatedJetRing.ext_coeff r h
  exact (RingEquiv.ofBijective _
    (jetThickening.sectionsHom_bijective (k := k) r W V)).symm.injective this

theorem jetThickening.coeff_add (V : W.Opens) (n : ℕ) (hn : n ≤ r)
    (x y : Γ(jetThickening (k := k) r W, jetThickeningProj (k := k) r W ⁻¹ᵁ V)) :
    jetThickening.coeff (k := k) r W V n hn (x + y) =
      jetThickening.coeff (k := k) r W V n hn x + jetThickening.coeff (k := k) r W V n hn y := by
  obtain ⟨p, rfl⟩ := (jetThickening.sectionsHom_bijective (k := k) r W V).2 x
  obtain ⟨q, rfl⟩ := (jetThickening.sectionsHom_bijective (k := k) r W V).2 y
  rw [← map_add, jetThickening.coeff_sectionsHom, jetThickening.coeff_sectionsHom,
    jetThickening.coeff_sectionsHom]
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  obtain ⟨q, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ q
  exact Polynomial.coeff_add p q n

/-- `sectionsHom` is natural with respect to restriction. -/
theorem jetThickening.sectionsHom_restrict {V V' : W.Opens} (h : V' ≤ V)
    (p : MiyaokaMori.Jet.TruncatedJetRing Γ(W, V) r) :
    jetThickening.sectionsHom (k := k) r W V'
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (W.presheaf.map (homOfLE h).op).hom p) =
      ((jetThickening (k := k) r W).presheaf.map
        (homOfLE (show jetThickeningProj (k := k) r W ⁻¹ᵁ V' ≤ jetThickeningProj (k := k) r W ⁻¹ᵁ V from
          fun _ hx => h hx)).op).hom (jetThickening.sectionsHom (k := k) r W V p) := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection]
  unfold jetThickening.sectionsHom
  rw [MiyaokaMori.Jet.lift_jetProjection, MiyaokaMori.Jet.lift_jetProjection]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
  rw [Polynomial.hom_eval₂]
  congr 1
  · ext a
    have := (jetThickeningProj (k := k) r W).naturality (homOfLE h).op
    exact congrArg (fun φ => φ.hom a) this
  · rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl

theorem jetThickening.coeff_restrict {V V' : W.Opens} (h : V' ≤ V) (n : ℕ) (hn : n ≤ r)
    (x : Γ(jetThickening (k := k) r W, jetThickeningProj (k := k) r W ⁻¹ᵁ V)) :
    jetThickening.coeff (k := k) r W V' n hn
        (((jetThickening (k := k) r W).presheaf.map
          (homOfLE (show jetThickeningProj (k := k) r W ⁻¹ᵁ V' ≤ jetThickeningProj (k := k) r W ⁻¹ᵁ V from
            fun _ hx => h hx)).op).hom x) =
      (W.presheaf.map (homOfLE h).op).hom (jetThickening.coeff (k := k) r W V n hn x) := by
  obtain ⟨p, rfl⟩ := (jetThickening.sectionsHom_bijective (k := k) r W V).2 x
  rw [← jetThickening.sectionsHom_restrict, jetThickening.coeff_sectionsHom,
    jetThickening.coeff_sectionsHom]
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  exact Polynomial.coeff_map _ n

/-- The coefficients of the monomial `pr^♯(a)·t^m`. -/
theorem jetThickening.coeff_proj_mul_parameter_pow (V : W.Opens) (n m : ℕ) (hn : n ≤ r) (a : Γ(W, V)) :
    jetThickening.coeff (k := k) r W V n hn
        (((jetThickeningProj (k := k) r W).app V).hom a *
          (((jetThickening (k := k) r W).presheaf.map (homOfLE le_top).op).hom
            (jetThickening.parameter (k := k) r W)) ^ m) =
      if n = m then a else 0 := by
  have h : ((jetThickeningProj (k := k) r W).app V).hom a *
      (((jetThickening (k := k) r W).presheaf.map (homOfLE le_top).op).hom
        (jetThickening.parameter (k := k) r W)) ^ m =
      jetThickening.sectionsHom (k := k) r W V
        (MiyaokaMori.Jet.jetProjection _ r (Polynomial.monomial m a)) := by
    unfold jetThickening.sectionsHom
    rw [MiyaokaMori.Jet.lift_jetProjection]
    simp [Polynomial.eval₂_monomial]
  rw [h, jetThickening.coeff_sectionsHom, MiyaokaMori.Jet.TruncatedJetRing.coeff_jetProjection,
    Polynomial.coeff_monomial]
  simp only [eq_comm]

end
