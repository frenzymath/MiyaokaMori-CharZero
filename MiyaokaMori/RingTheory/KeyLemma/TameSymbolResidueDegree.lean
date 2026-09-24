import MiyaokaMori.Prelude

/-! # The residue degree of a valuation ring equals the inertia degree

`A` a local ring, `B` a Dedekind `A`-algebra with fraction field `K`, `v` a height-one prime of `B`, and
`φ : A → O_v` a local homomorphism to the valuation ring of `v` compatible with `A → B → K`. Then
`[κ(O_v) : κ(A)] = Ideal.inertiaDeg' 𝔪_A v` (`= [B/v : A/𝔪_A]`).

Reference: the `[κ(𝔪_j) : κ(𝔪)]` in the statement of Stacks 02MJ; the proof of 0EAN uses it to replace the
residue field of the valuation ring by `B/v`.
-/

set_option autoImplicit false

universe u

noncomputable section

/-- Proof: (1) `v.asIdeal.comap (algebraMap A B) = 𝔪_A`: `r ∈` LHS `⟺ v(r) < 1` (`valuation_lt_one_iff_mem`)
`⟺ φ r` is not a unit of `O_v` `⟺ r` is not a unit (`φ` is local). Hence the `dif_pos` branch of
`Ideal.inertiaDeg'` applies, with value `finrank (A ⧸ 𝔪_A) (B ⧸ v)`.
(2) A ring isomorphism `B ⧸ v ≃ κ(O_v)`: the kernel of `B → O_v → κ(O_v)` (`valuation_le_one` gives
`B → O_v`) is `v`; surjectivity comes from
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring` (`O_v = B_v`) and the
residue field of the localization (`IsLocalization.AtPrime` + `v` maximal; the bijection from
`Ideal.Quotient` to the residue field of the localization is `IsLocalization.AtPrime.equivQuotMaximalIdeal`).
(3) This isomorphism is compatible with the action of `A/𝔪_A = κ(A)` (`hφ`), hence is a `κ(A)`-linear
isomorphism; `LinearEquiv.finrank_eq`.
Edge case: if `κ(O_v)/κ(A)` is infinite, both `finrank`s are `0` and still agree (isomorphisms preserve
this). -/
theorem Ring.TameSymbol.finrank_residueField_valuationSubring_eq_inertiaDeg' {A B K : Type u}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B] [Field K] [Algebra B K]
    [IsFractionRing B K] (v : IsDedekindDomain.HeightOneSpectrum B)
    (φ : A →+* (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) [IsLocalHom φ]
    (hφ : ∀ r : A, ((φ r : (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) : K)
      = algebraMap B K (algebraMap A B r)) :
    letI : Algebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) :=
      (IsLocalRing.ResidueField.map φ).toAlgebra
    Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring)
      = Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal := by
  classical
  -- (0) the ring map `B → O_v` (every element of `B` has valuation `≤ 1`) and `ψ : B → κ(O_v)`
  let ι : B →+* (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring :=
    (algebraMap B K).codRestrict (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring
      fun b => IsDedekindDomain.HeightOneSpectrum.valuation_le_one v b
  let ψ : B →+* IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring :=
    (IsLocalRing.residue _).comp ι
  have hψ : ∀ b : B, ψ b = IsLocalRing.residue _ (ι b) := fun b => rfl
  have hι : ∀ b : B, ((ι b : (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) : K)
      = algebraMap B K b := fun b => rfl
  -- (2a) kernel of ψ is v
  have hker : RingHom.ker ψ = v.asIdeal := by
    ext b
    rw [RingHom.mem_ker, hψ, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, hι,
      IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  -- (2b) ψ is surjective: every element of O_v is n/d with d ∉ v (O_v = B_v), and d is invertible mod v
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    have hy : (y : K) ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact y.2
    obtain ⟨n, d, hd, hnd⟩ := hy
    have hd' : d ∉ v.asIdeal := hd
    obtain ⟨t, i, hi, hti⟩ := (IsDedekindDomain.HeightOneSpectrum.isMaximal v).exists_inv hd'
    refine ⟨n * t, ?_⟩
    -- residue relations
    have h1 : ψ t * ψ d = 1 := by
      rw [← map_mul, ← sub_eq_zero, ← map_one ψ, ← map_sub]
      have : t * d - 1 = -i := by rw [← hti]; ring
      rw [this, map_neg, neg_eq_zero, ← RingHom.mem_ker, hker]
      exact hi
    have hd0 : algebraMap B K d ≠ 0 := by
      intro h0
      apply hd'
      rw [(IsFractionRing.injective B K).eq_iff.symm.mpr (h0.trans (map_zero _).symm)]
      exact Ideal.zero_mem _
    have h2 : IsLocalRing.residue _ y * ψ d = ψ n := by
      rw [hψ, hψ, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subring.coe_mul, hι, hι, hnd]
      field_simp
    rw [map_mul]
    linear_combination (IsLocalRing.residue _ y) * h1 - ψ t * h2
  -- (1) comap of v along A → B is the maximal ideal of A
  have hcomap : v.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A := by
    ext r
    rw [Ideal.mem_comap, ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
    change IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap B K (algebraMap A B r)) < 1 ↔ _
    rw [← hφ r, ← Valuation.mem_maximalIdeal_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff φ r)
  rw [Ideal.inertiaDeg', dif_pos hcomap]
  -- (3) the ring iso B/v ≃ κ(O_v), compatible with κ(A)
  let e : (B ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ b : B, e (Ideal.Quotient.mk _ b) = ψ b := fun b => rfl
  let _ : Algebra (IsLocalRing.ResidueField A) (B ⧸ v.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap hcomap.ge
  let _ : Algebra (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  have hcomm : ∀ x : IsLocalRing.ResidueField A,
      e (algebraMap (IsLocalRing.ResidueField A) (B ⧸ v.asIdeal) x)
        = algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField
            (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) x := by
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change e (Ideal.quotientMap v.asIdeal (algebraMap A B) hcomap.ge (Ideal.Quotient.mk _ a))
      = IsLocalRing.ResidueField.map φ (IsLocalRing.residue A a)
    rw [Ideal.quotientMap_mk, he, IsLocalRing.ResidueField.map_residue, hψ]
    congr 1
    exact Subtype.ext ((hι _).trans (hφ a).symm)
  exact ((AlgEquiv.ofRingEquiv hcomm).toLinearEquiv.finrank_eq).symm

end
