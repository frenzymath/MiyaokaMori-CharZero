import MiyaokaMori.Prelude
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.LocalRing.Module
import MiyaokaMori.RingTheory.RegularLocalRing.KerCotangentToTensorInjectiveOfFormallySmooth
import MiyaokaMori.RingTheory.RegularLocalRing.RegularQuotientKerInfSqLe

/-! # Smoothness from regular localizations over a perfect field

**Stacks 00TV / 0B8X (algebraic form).** Let `k` be a perfect field and `A` a finite type
`k`-algebra all of whose localizations at primes are regular local rings. Then `A` is smooth
over `k`. This is the converse of `Algebra.Smooth.isRegularLocalRing_localization`
(`MiyaokaMori.Stacks.Algebra.Stacks00tt`), and the proof is the mirror image of that one.

Source: Stacks 00TV (Lemma 10.140.5: `k` perfect, `S` finite type over `k`, `S_q` regular ⇒
`k → S` smooth at `q`), 0B8X; Matsumura CRT Thm. 28.7 for the local statement.

## Route

1. `A` is of finite presentation (finite type over a Noetherian ring), so by
   `Algebra.smoothLocus_eq_univ_iff` it suffices to show `A_q` formally smooth over `k` for
   every prime `q` (`Algebra.Smooth = FormallySmooth ∧ FinitePresentation`).
2. Presentation: `A = k[x₁,…,xₙ]/I`, `Q = π⁻¹(q)`, `B = k[x]_Q → A_q` surjective with finitely
   generated kernel `K` (verbatim `Stacks00tt`). `B` is a regular local ring
   (`MvPolynomial.isRegularRing_of_isRegularRing`), formally smooth over `k` with `Ω_{B/k}`
   finite free; `κ = B/m_B` is a finitely generated field extension of the perfect field `k`,
   hence formally smooth over `k` (`Algebra.FormallySmooth.of_perfectField`).
3. Local statement `Algebra.FormallySmooth.of_isRegularLocalRing_of_surjective` (below):
   by the Jacobian criterion (`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange`)
   `A_q ≅ B/K` is formally smooth iff `κ ⊗_B K → κ ⊗_B Ω_{B/k}`, `1 ⊗ b ↦ 1 ⊗ db`, is injective.
   The source is `K/m_B K` (`quotTensorEquivQuotSMul`), and the map factors as
   `K/m_B K → m_B/m_B² → κ ⊗ Ω_{B/k}`, where
   * `K/m_B K → m_B/m_B²` is injective because `K ∩ m_B² ≤ m_B K`
     (`IsRegularLocalRing.ker_inf_maximalIdeal_sq_le_of_quotient`: regular quotient of a regular
     local ring, Stacks 00NU), and
   * `m_B/m_B² → κ ⊗ Ω_{B/k}` is injective because `κ` is formally smooth over `k`
     (`KaehlerDifferential.kerCotangentToTensor_injective_of_formallySmooth`, Stacks 031I).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open TensorProduct IsLocalRing

noncomputable section

section Local

variable {P S : Type*} [CommRing P] [CommRing S] [Algebra P S]

/-- **Local form (Matsumura CRT 28.7 / Stacks 00TV).** Let `P → S` be a surjection of regular local
rings with finitely generated kernel, `P` formally smooth over `R` with `Ω_{P/R}` finite free, and
the residue field `κ = P/m_P` formally smooth over `R`. Then `S` is formally smooth over `R`.
Route in the module docstring (Jacobian criterion + `K ∩ m² ≤ mK` + `m/m² ↪ κ ⊗ Ω_{P/R}`). -/
theorem Algebra.FormallySmooth.of_isRegularLocalRing_of_surjective (R : Type*) [CommRing R]
    [Algebra R P] [Algebra R S] [IsScalarTower R P S]
    [IsRegularLocalRing P] [IsRegularLocalRing S]
    [Algebra.FormallySmooth R P] [Module.Free P (KaehlerDifferential R P)]
    [Module.Finite P (KaehlerDifferential R P)]
    [Algebra.FormallySmooth R (ResidueField P)]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG) :
    Algebra.FormallySmooth R S := by
  classical
  set K := RingHom.ker (algebraMap P S) with hKdef
  have hKle : K ≤ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top _)
  -- make `κ = P/m_P` an `S`-algebra through `S ≅ P/K → P/m_P`
  let g : S →+* ResidueField P :=
    (algebraMap P S).liftOfSurjective h₁ ⟨residue P, by rw [ker_residue]; exact hKle⟩
  have hg : ∀ x : P, g (algebraMap P S x) = residue P x := fun x =>
    RingHom.liftOfSurjective_comp_apply _ h₁ _ x
  let _ : Algebra S (ResidueField P) := g.toAlgebra
  have : IsScalarTower P S (ResidueField P) :=
    IsScalarTower.of_algebraMap_eq fun x => (hg x).symm
  have h₃ : maximalIdeal S ≤ RingHom.ker (algebraMap S (ResidueField P)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := h₁ y
    rw [RingHom.mem_ker, RingHom.algebraMap_toAlgebra, hg, residue_eq_zero_iff]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    exact fun hx => hy (hx.map (algebraMap P S))
  -- `S ≅ P/K` is regular, so `K ∩ m² ≤ mK`
  have hSreg : IsRegularLocalRing (P ⧸ K) :=
    IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective h₁).symm
  have hinf : K ⊓ maximalIdeal P ^ 2 ≤ maximalIdeal P * K :=
    IsRegularLocalRing.ker_inf_maximalIdeal_sq_le_of_quotient K
  -- `m/m² → κ ⊗ Ω_{P/R}` is injective
  have hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  have hinjm := KaehlerDifferential.kerCotangentToTensor_injective_of_formallySmooth R P
    (ResidueField P) residue_surjective
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange (R := R) (S := S)
    P (ResidueField P) h₁ h₂ h₃, injective_iff_map_eq_zero]
  intro z hz
  -- write `z = 1 ⊗ b`
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _
    (quotTensorEquivQuotSMul K (maximalIdeal P) z)
  have hz' : z = (1 : ResidueField P) ⊗ₜ[P] b := by
    apply (quotTensorEquivQuotSMul K (maximalIdeal P)).injective
    rw [← hb]
    exact ((quotTensorEquivQuotSMul_mk_tmul (maximalIdeal P) 1 b).trans (by rw [one_smul])).symm
  -- `1 ⊗ d b = 0` in `κ ⊗ Ω`
  have hD : (1 : ResidueField P) ⊗ₜ[P] KaehlerDifferential.D R P (b : P) = 0 := by
    have := hz
    rw [hz', KaehlerDifferential.cotangentComplexBaseChange_tmul, one_smul,
      KaehlerDifferential.kerToTensor_apply] at this
    exact this
  -- hence `b ∈ m²`
  have hbm : (b : P) ∈ maximalIdeal P := hKle b.2
  have hbm2 : (b : P) ∈ maximalIdeal P ^ 2 := by
    have hb' : (b : P) ∈ RingHom.ker (algebraMap P (ResidueField P)) := hker ▸ hbm
    have h0 : KaehlerDifferential.kerCotangentToTensor R P (ResidueField P)
        (Ideal.toCotangent _ ⟨(b : P), hb'⟩) = 0 := by
      rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
      exact hD
    have := hinjm (h0.trans (map_zero _).symm)
    rw [Ideal.toCotangent_eq_zero] at this
    have h4 : (b : P) ∈ RingHom.ker (algebraMap P (ResidueField P)) ^ 2 := this
    rw [hker] at h4
    exact h4
  -- hence `b ∈ mK`, so `1 ⊗ b = 0`
  have hbmK : (b : P) ∈ maximalIdeal P * K := hinf ⟨b.2, hbm2⟩
  have h2 : b ∈ (maximalIdeal P • ⊤ : Submodule P K) := by
    rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul]
    exact hbmK
  have h3 : quotTensorEquivQuotSMul K (maximalIdeal P) ((1 : ResidueField P) ⊗ₜ[P] b) = 0 :=
    (quotTensorEquivQuotSMul_mk_tmul (maximalIdeal P) 1 b).trans
      (by rw [one_smul]; exact (Submodule.Quotient.mk_eq_zero _).mpr h2)
  rw [hz']
  exact (LinearEquiv.map_eq_zero_iff _).mp h3

end Local

/-- **Stacks 00TV / 0B8X (algebraic form).** `k` a perfect field, `A` a finite type `k`-algebra
whose localizations at all primes are regular local rings; then `A` is smooth over `k`.
Route in the module docstring. -/
theorem Algebra.Smooth.of_isRegularLocalRing_localization {k A : Type u} [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hreg : ∀ (q : Ideal A) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q)) :
    Algebra.Smooth k A := by
  classical
  have hfp : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  refine ⟨?_, hfp⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro q
  have hq : q.asIdeal.IsPrime := q.isPrime
  show Algebra.FormallySmooth k (Localization.AtPrime q.asIdeal)
  -- Step 2: presentation `A = k[x₁,…,xₙ]/I`
  obtain ⟨n, π, hπ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := A)).mp inferInstance
  have hIfg : (RingHom.ker π.toRingHom).FG := Algebra.FinitePresentation.ker_fG_of_surjective π hπ
  set R := MvPolynomial (Fin n) k
  set Q : Ideal R := Ideal.comap π.toRingHom q.asIdeal with hQ
  have : Q.IsPrime := Ideal.IsPrime.comap _
  set B := Localization.AtPrime Q
  set Aq := Localization.AtPrime q.asIdeal
  let f : B →+* Aq := Localization.localRingHom Q q.asIdeal π.toRingHom hQ
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl y
    obtain ⟨a, rfl⟩ := hπ s
    obtain ⟨b, hb⟩ := hπ (t : A)
    have hbQ : b ∈ Q.primeCompl := by
      show b ∉ Q
      rw [hQ, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hb]
      exact t.2
    refine ⟨IsLocalization.mk' B a ⟨b, hbQ⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hb
  have hker : RingHom.ker f = (RingHom.ker π.toRingHom).map (algebraMap R B) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
      rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
      obtain ⟨⟨m, hm⟩, hmx⟩ := hx
      obtain ⟨c, rfl⟩ := hπ m
      have hcQ : c ∈ Q.primeCompl := by
        show c ∉ Q
        rw [hQ, Ideal.mem_comap]
        exact hm
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      refine ⟨c, hcQ, ?_⟩
      rw [RingHom.mem_ker, map_mul]
      exact hmx
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, Localization.localRingHom_to_map,
        RingHom.mem_ker.mp ha, map_zero]
  have hkerFG : (RingHom.ker f).FG := hker ▸ hIfg.map _
  -- Step 3: instances for the local statement
  let _ : Algebra B Aq := f.toAlgebra
  have : IsScalarTower k B Aq := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap k Aq x = f (algebraMap k B x)
    rw [IsScalarTower.algebraMap_apply k R B x, Localization.localRingHom_to_map,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, π.commutes, IsScalarTower.algebraMap_apply k A Aq x]
  have : Module.Free B (KaehlerDifferential k B) := Module.free_of_flat_of_isLocalRing
  have : IsRegularLocalRing Aq := hreg q.asIdeal
  have : Algebra.EssFiniteType k (ResidueField B) :=
    inferInstanceAs (Algebra.EssFiniteType k (B ⧸ maximalIdeal B))
  have : Algebra.FormallySmooth k (ResidueField B) := inferInstance
  exact Algebra.FormallySmooth.of_isRegularLocalRing_of_surjective k (P := B) (S := Aq) hf hkerFG

end
