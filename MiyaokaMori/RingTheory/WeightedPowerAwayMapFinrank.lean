import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPowerChartFinite
import MiyaokaMori.RingTheory.Polynomial.MvPolynomialPowerHomFinrank

/-! # Rank of the weighted power map on an affine chart

The ring map `φ = weightedPowerAwayMap k w hw i₀ : k[x]^{(w)}_(x_{i₀}) → k[u]_(u_{i₀}^{w_{i₀}})`
(with `w_{i₀} = 1`) on a chart makes the target a free module over the source of rank `∏ᵢ wᵢ`
(`k[z]` has basis `z^a`, `0 ≤ a_j < w_j`, over `k[z^w]`). This is the algebraic core of the degree
`∏ wᵢ` of the weighted power map (Lemma 2.2 of the paper).

Proof layout. Write `A = k[x]^{(w)}_{(x_{i₀})}`, `B = k[u]_{(ψ x_{i₀})}`, `ψ x_j = u_j^{w_j}`.
1. `awayCongr`: `ψ x_{i₀} = u_{i₀}^{w_{i₀}} = u_{i₀}` (`h1`), so `B ≃+* k[u]_{(u_{i₀})}` by transport along this equality
   (`awayCongr_mk`: it sends `a / (ψ x_{i₀})^n` to `a / u_{i₀}^n`).
2. `forward_mk`: the dehomogenisation `weightedAwayDegreeOneEquiv.forward` sends `a / x_{i₀}^n` to `a(x_{i₀} := 1)`.
3. `Algebra.finrank_eq_of_equiv_equiv` with `A = A` and `B ≃+* k[z]` (`eB` = transport, then dehomogenisation of
   `k[u]_{(u_{i₀})}`): `finrank_A B = finrank_A k[z]`, where `A` acts on `k[z]` through `eB ∘ φ`.
4. `MvPolynomial.PowerHom.finrank_eq` (module `MvPolynomialPowerHomFinrank`): `k[z]` has rank `∏_{j ≠ i₀} w_j` over
   any ring `R ≃ k[y]` acting through `θ : y_j ↦ z_j^{w_j}`; here `R = A`, `eR = eA⁻¹` with `eA` the dehomogenisation
   of `A`, and the compatibility `eB ∘ φ ∘ eA⁻¹ = θ` is checked on the generators `C c`, `y_j`
   (`Away.map_mk`, `awayCongr_mk`, `forward_mk`, `weightedPowerGradedHom_X`).
5. `∏_{j ≠ i₀} w_j = ∏ᵢ wᵢ` since `w_{i₀} = 1` (`Finset.prod_erase`, `Finset.prod_subtype`).
The dehomogenisations are `weightedAwayDegreeOneEquiv` (module `WeightedAwayDegreeOneVariable`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace WeightedPowerAwayMapFinrank

section AwayCongr

variable {ι : Type*} {A : Type*} {S : Type*} [CommRing A] [SetLike S A] [AddSubgroupClass S A]
  [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → S) [GradedRing 𝒜]

/-- Transport of the homogeneous localisation along an equality `f = g` of the localised element. -/
def awayCongr {f g : A} (h : f = g) :
    HomogeneousLocalization.Away 𝒜 f ≃+* HomogeneousLocalization.Away 𝒜 g :=
  h ▸ RingEquiv.refl _

lemma awayCongr_mk {f g : A} (h : f = g) {d : ι} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    awayCongr 𝒜 h (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      HomogeneousLocalization.Away.mk 𝒜 hg n a ha := by
  subst h; rfl

end AwayCongr

variable (k : Type u) [Field k] {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- The dehomogenisation `forward` on the fraction `a / x_{i₀}^n` is `a(x_{i₀} := 1)`. -/
theorem forward_mk (w : σ → ℕ) (i₀ : σ)
    (hX : (MvPolynomial.X i₀ : MvPolynomial σ k) ∈ MvPolynomial.weightedHomogeneousSubmodule k w 1)
    (n : ℕ) (a : MvPolynomial σ k) (ha : a ∈ MvPolynomial.weightedHomogeneousSubmodule k w (n • 1)) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    weightedAwayDegreeOneEquiv.forward k w i₀ (HomogeneousLocalization.Away.mk _ hX n a ha) =
      weightedAwayDegreeOneEquiv.dehom k i₀ a := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  unfold weightedAwayDegreeOneEquiv.forward
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.awayLift_mk (v := 1) (hv := by simp [weightedAwayDegreeOneEquiv.dehom]), one_pow, mul_one]

/-- A degree-0 element `z` is the fraction `z / x_{i₀}^0`. -/
theorem algebraMap_zero_eq_mk (w : σ → ℕ) (i₀ : σ)
    (hX : (MvPolynomial.X i₀ : MvPolynomial σ k) ∈ MvPolynomial.weightedHomogeneousSubmodule k w 1)
    (z : MvPolynomial.weightedHomogeneousSubmodule k w 0) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
        (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀)) z =
      HomogeneousLocalization.Away.mk _ hX 0 z.1 (by simpa using z.2) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.algebraMap_eq]
  change Localization.mk _ ⟨1, _⟩ = _
  congr 1

/-- `ψ x_j = u_j^{w_j}` on constants: `ψ (C c) = C c`. -/
theorem weightedPowerGradedHom_C (w : σ → ℕ) (c : k) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    weightedPowerGradedHom k w (MvPolynomial.C c) = MvPolynomial.C c := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  change (MvPolynomial.aeval (R := k) (fun j : σ => (MvPolynomial.X j : MvPolynomial σ k) ^ w j))
    (MvPolynomial.C c) = _
  rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem dehom_C (i₀ : σ) (c : k) :
    weightedAwayDegreeOneEquiv.dehom k i₀ (MvPolynomial.C c) = MvPolynomial.C c := by
  change (MvPolynomial.aeval (R := k) _) (MvPolynomial.C c) = _
  rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem dehom_X_of_ne (i₀ : σ) {j : σ} (hj : j ≠ i₀) :
    weightedAwayDegreeOneEquiv.dehom k i₀ (MvPolynomial.X j) = MvPolynomial.X ⟨j, hj⟩ := by
  change (MvPolynomial.aeval (R := k) _) (MvPolynomial.X j) = _
  rw [MvPolynomial.aeval_X, dif_neg hj]

end WeightedPowerAwayMapFinrank

/-- The ring map `φ = weightedPowerAwayMap k w hw i₀ : k[x]^{(w)}_(x_{i₀}) → k[u]_(u_{i₀}^{w_{i₀}})`
(with `w_{i₀} = 1`) on a chart makes the target a free module of rank `∏ᵢ wᵢ` over the source.

Proof. `weightedAwayDegreeOneEquiv k w i₀ h1` gives `k[x]^{(w)}_(x_{i₀}) ≅ k[y_j]_{j ≠ i₀}`
(`y_j = x_j / x_{i₀}^{w_j}`) and `weightedAwayDegreeOneEquiv k 1 i₀ rfl` gives
`k[u]_(u_{i₀}) ≅ k[z_j]_{j ≠ i₀}` (`z_j = u_j / u_{i₀}`). Under these identifications `φ` is the
`k`-algebra map `y_j ↦ z_j^{w_j}` (checked on generators:
`φ(x_j / x_{i₀}^{w_j}) = ψ(x_j)/ψ(x_{i₀})^{w_j} = u_j^{w_j} / u_{i₀}^{w_j} = z_j^{w_j}`, using
`HomogeneousLocalization.Away.map_mk` and `weightedPowerGradedHom_X`).
Note that `ψ(x_{i₀}) = u_{i₀}^{w_{i₀}} = u_{i₀}^1`, so the localizing element on the target side is
`u_{i₀}^1` rather than `u_{i₀}`, and `weightedAwayDegreeOneEquiv` has to be transported along the
target `ψ (X i₀)` of `Away.map`.
It remains to see that `k[z]` is free over `k[y]` (`y_j ↦ z_j^{w_j}`) with basis the monomials `z^a`
(`0 ≤ a_j < w_j`), of rank `∏_{j ≠ i₀} w_j`: every `f ∈ k[z]` decomposes uniquely as
`f = ∑_a z^a · g_a(z^w)` by reducing exponents mod `w` (write `z^e = z^{e mod w} · (z^w)^{e div w}`;
uniqueness by comparing coefficients, since distinct `(a, e')` give distinct `e = a + w · e'`).
Multiplying by `w_{i₀} = 1` gives `∏ᵢ wᵢ` (`Finset.prod_erase` / `Fintype.prod_subtype`), and
`Module.finrank` is the cardinality of a basis (`Module.finrank_eq_card_basis`).

Edge cases: `σ = {i₀}` (`N = 0`): both sides are `k`, rank `1` = empty product; if some `w_j = 1`,
the basis in that variable is just `1`.

Implementation: (a) the monomial basis is `MvPolynomial.PowerHom.finrank_eq` (module
`MvPolynomialPowerHomFinrank`); (b) the commutative diagram and the transport
`Away ℬ (ψ x_{i₀}) ≃ Away ℬ (u_{i₀})` are in the namespace `WeightedPowerAwayMapFinrank` of this
file; (c) the rank is transferred with `Algebra.finrank_eq_of_equiv_equiv`. -/
theorem weightedPowerAwayMap_finrank (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (i₀ : σ) (h1 : w i₀ = 1) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    @Module.finrank
      (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀))
      (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (weightedPowerGradedHom k w (MvPolynomial.X i₀)))
      _ _ (@Algebra.toModule _ _ _ _ (weightedPowerAwayMap k w hw i₀).toAlgebra) = ∏ i, w i := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  -- notation
  have hX : (MvPolynomial.X i₀ : MvPolynomial σ k) ∈ MvPolynomial.weightedHomogeneousSubmodule k w 1 :=
    weightedAwayDegreeOneEquiv.X_mem k w i₀ h1
  have hX1 : (MvPolynomial.X i₀ : MvPolynomial σ k) ∈
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 1 :=
    weightedAwayDegreeOneEquiv.X_mem k (fun _ : σ => 1) i₀ rfl
  have hψX : weightedPowerGradedHom k w (MvPolynomial.X i₀) = (MvPolynomial.X i₀ : MvPolynomial σ k) := by
    rw [weightedPowerGradedHom_X, h1, pow_one]
  -- the `k`-algebra structures on the chart rings (the same terms as in `WeightedAwayDegreeOneVariable`)
  letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i₀)) :=
    ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
        (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
          (MvPolynomial.X i₀))).comp
      (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
  letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
      (MvPolynomial.X i₀)) :=
    ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0)
        (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
          (MvPolynomial.X i₀))).comp
      (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0))).toAlgebra
  -- the ring isomorphisms
  let eA : HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀) ≃+*
      MvPolynomial {j // j ≠ i₀} k := (weightedAwayDegreeOneEquiv k w i₀ h1).toRingEquiv
  let eB0 : HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
      (MvPolynomial.X i₀) ≃+* MvPolynomial {j // j ≠ i₀} k :=
    (weightedAwayDegreeOneEquiv k (fun _ : σ => 1) i₀ rfl).toRingEquiv
  let eB : HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
      (weightedPowerGradedHom k w (MvPolynomial.X i₀)) ≃+* MvPolynomial {j // j ≠ i₀} k :=
    (WeightedPowerAwayMapFinrank.awayCongr _ hψX).trans eB0
  letI : Algebra (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀))
      (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (weightedPowerGradedHom k w (MvPolynomial.X i₀))) := (weightedPowerAwayMap k w hw i₀).toAlgebra
  letI : Algebra (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀))
      (MvPolynomial {j // j ≠ i₀} k) := (eB.toRingHom.comp (weightedPowerAwayMap k w hw i₀)).toAlgebra
  -- step 3: transport the rank along `eB`
  rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) eB (RingHom.ext fun _ => rfl)]
  -- step 4: the compatibility `eB ∘ φ ∘ eA⁻¹ = θ`
  have hw' : ∀ j : {j // j ≠ i₀}, 0 < w j.1 := fun j => hw j.1
  have H : (algebraMap (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) (MvPolynomial {j // j ≠ i₀} k)).comp eA.symm.toRingHom =
      MvPolynomial.PowerHom.powerHom k (fun j : {j // j ≠ i₀} => w j.1) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, MvPolynomial.PowerHom.powerHom_C]
      have e1 : eA.symm.toRingHom (MvPolynomial.C c) =
          HomogeneousLocalization.Away.mk _ hX 0 (MvPolynomial.C c)
            (by simpa using MvPolynomial.isWeightedHomogeneous_C w c) := by
        change weightedAwayDegreeOneEquiv.backward k w i₀ h1 (MvPolynomial.C c) = _
        unfold weightedAwayDegreeOneEquiv.backward
        rw [MvPolynomial.aeval_C]
        exact WeightedPowerAwayMapFinrank.algebraMap_zero_eq_mk k w i₀ hX
          (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0) c)
      rw [e1]
      change eB (weightedPowerAwayMap k w hw i₀ _) = _
      unfold weightedPowerAwayMap
      rw [HomogeneousLocalization.Away.map_mk]
      change eB0 (WeightedPowerAwayMapFinrank.awayCongr _ hψX _) = _
      rw [WeightedPowerAwayMapFinrank.awayCongr_mk _ hψX _ hX1]
      change weightedAwayDegreeOneEquiv.forward k (fun _ : σ => 1) i₀ _ = _
      rw [WeightedPowerAwayMapFinrank.forward_mk, WeightedPowerAwayMapFinrank.weightedPowerGradedHom_C,
        WeightedPowerAwayMapFinrank.dehom_C]
    · intro j
      rw [RingHom.comp_apply, MvPolynomial.PowerHom.powerHom_X]
      have e1 : eA.symm.toRingHom (MvPolynomial.X j) =
          HomogeneousLocalization.Away.mk _ hX (w j.1) (MvPolynomial.X j.1)
            (by rw [smul_eq_mul, mul_one, MvPolynomial.mem_weightedHomogeneousSubmodule]
                exact MvPolynomial.isWeightedHomogeneous_X k w j.1) := by
        change weightedAwayDegreeOneEquiv.backward k w i₀ h1 (MvPolynomial.X j) = _
        exact MvPolynomial.aeval_X _ _
      rw [e1]
      change eB (weightedPowerAwayMap k w hw i₀ _) = _
      unfold weightedPowerAwayMap
      rw [HomogeneousLocalization.Away.map_mk]
      change eB0 (WeightedPowerAwayMapFinrank.awayCongr _ hψX _) = _
      rw [WeightedPowerAwayMapFinrank.awayCongr_mk _ hψX _ hX1]
      change weightedAwayDegreeOneEquiv.forward k (fun _ : σ => 1) i₀ _ = _
      rw [WeightedPowerAwayMapFinrank.forward_mk, weightedPowerGradedHom_X, map_pow,
        WeightedPowerAwayMapFinrank.dehom_X_of_ne k i₀ j.2]
  rw [MvPolynomial.PowerHom.finrank_eq k (fun j : {j // j ≠ i₀} => w j.1) hw' eA.symm H]
  -- step 5: `∏_{j ≠ i₀} w_j = ∏ᵢ wᵢ`
  rw [← Finset.prod_erase Finset.univ h1]
  exact (Finset.prod_subtype _ (fun x => by simp) w).symm

end
