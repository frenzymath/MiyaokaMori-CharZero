import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme

/-! # Effective Cartier divisors have pure codimension one (Stacks 0BCN)

Stacks 0BCN(2): on a locally Noetherian scheme, at the generic point `ξ` of every irreducible
component of an effective Cartier divisor `D`, `dim O_{X,ξ} = 1`. (This is "`Z(s)` has codimension 1"
in Lazarsfeld 1.2.23 and in the proof of Stacks 0BEV.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 0BCN(2): on a locally Noetherian scheme `X`, at a maximal point `ξ` of an effective
Cartier divisor `D` (the generic point of an irreducible component of `D`), the local ring
`O_{X,ξ}` has dimension `1`, i.e. `coheight ξ = 1` in `X`.

Proof. Let `x = ι ξ`. Take an affine open `U ∋ x` with `I_D(U) = (a)`, `a` a nonzerodivisor
(`EffCartier.exists_localEquation`); `A := Γ(X, U)` is Noetherian, and `x` corresponds to the
prime `𝔭 = U.primeIdealOf x`. `coheight x = dim O_{X,x}` (`ringKrullDim_stalk_eq_coheight`) and
`O_{X,x} = A_𝔭` (`isLocalization_stalk`), so `coheight x = height 𝔭`
(`IsLocalization.AtPrime.ringKrullDim_eq_height`). `𝔭` is minimal over `(a)`: it contains `a`
since `x ∈ Supp I_D`; if `(a) ≤ 𝔮 ≤ 𝔭` then `y := fromSpec 𝔮 ∈ Supp I_D` lifts to `η : D` with
`η ⤳ ξ`, so `ξ ≤ η`, maximality gives `η ≤ ξ`, hence `x ⤳ y` and `𝔭 ≤ 𝔮`. Krull's
Hauptidealsatz (`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`) gives `height 𝔭 ≤ 1`;
`a` a nonzerodivisor gives `1 ≤ height (a) ≤ height 𝔭`
(`Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors`). -/
theorem AlgebraicGeometry.EffectiveCartierDivisor.coheight_eq_one_of_isMax {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (D : AlgebraicGeometry.EffectiveCartierDivisor X)
    (ξ : D.toScheme) (hξ : IsMax ξ) :
    Order.coheight (D.idealSheaf.subschemeι.base ξ) = 1 := by
  set x : X := D.idealSheaf.subschemeι.base ξ
  -- x lies in the support of I_D
  have hxsupp : x ∈ D.idealSheaf.support := by
    have : x ∈ Set.range D.idealSheaf.subschemeι := ⟨ξ, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at this
  -- affine neighbourhood U of x with I_D(U) = (a), a a nonzerodivisor
  obtain ⟨U, hxU, a, ha, hI⟩ := Scheme.EffCartier.exists_localEquation D x
  have hU : IsAffineOpen U.1 := U.2
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  set 𝔭 : PrimeSpectrum Γ(X, U.1) := hU.primeIdealOf ⟨x, hxU⟩
  have hx𝔭 : hU.fromSpec 𝔭 = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  -- membership in the zero locus of I_D(U), read off in Spec Γ(X, U)
  have hzero : ∀ P : PrimeSpectrum Γ(X, U.1),
      hU.fromSpec P ∈ X.zeroLocus (U := U.1) (D.idealSheaf.ideal U : Set Γ(X, U.1)) ↔
        D.idealSheaf.ideal U ≤ P.asIdeal := by
    intro P
    have key := Set.ext_iff.mp
      (hU.fromSpec_preimage_zeroLocus (D.idealSheaf.ideal U : Set Γ(X, U.1))) P
    exact key.trans ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)
  -- coheight x = dim O_{X,x} = dim A_𝔭 = height 𝔭
  have hco : Order.coheight x = 𝔭.asIdeal.height := by
    have h1 := ringKrullDim_stalk_eq_coheight x
    let _ : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    have h2 := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭.asIdeal (X.presheaf.stalk x)
    exact WithBot.coe_inj.mp (h1.symm.trans h2)
  -- 𝔭 is a minimal prime over (a)
  have hmin : 𝔭.asIdeal ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨𝔭.isPrime, ?_⟩, ?_⟩
    · rw [← hI, ← hzero 𝔭, hx𝔭]
      exact (Scheme.IdealSheafData.mem_support_iff_of_mem hxU).mp hxsupp
    · rintro q ⟨hq, hle⟩ hq𝔭
      set Q : PrimeSpectrum Γ(X, U.1) := ⟨q, hq⟩
      have hyU : hU.fromSpec Q ∈ U.1 := by
        have : hU.fromSpec Q ∈ Set.range hU.fromSpec := ⟨Q, rfl⟩
        rwa [hU.range_fromSpec] at this
      have hysupp : hU.fromSpec Q ∈ D.idealSheaf.support := by
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyU, hzero Q, hI]
        exact hle
      obtain ⟨η, hη⟩ : hU.fromSpec Q ∈ Set.range D.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hysupp
      -- Q ⤳ 𝔭 in Spec, hence fromSpec Q ⤳ x in X, hence η ⤳ ξ in D, i.e. ξ ≤ η
      have hQ𝔭 : Q ⤳ 𝔭 := (PrimeSpectrum.le_iff_specializes Q 𝔭).mp hq𝔭
      have hyx : hU.fromSpec Q ⤳ x := by
        have := hQ𝔭.map hU.fromSpec.continuous
        rwa [hx𝔭] at this
      have hηξ : η ⤳ ξ := by
        rw [← D.idealSheaf.subschemeι.isEmbedding.isInducing.specializes_iff, hη]
        exact hyx
      -- ξ is maximal, so η ≤ ξ, i.e. ξ ⤳ η, hence x ⤳ fromSpec Q, hence 𝔭 ⤳ Q, i.e. 𝔭 ≤ Q
      have hξη : ξ ⤳ η := Scheme.le_iff_specializes.mp (hξ (Scheme.le_iff_specializes.mpr hηξ))
      have hxy : x ⤳ hU.fromSpec Q := by
        rw [← hη]
        exact (D.idealSheaf.subschemeι.isEmbedding.isInducing.specializes_iff).mpr hξη
      have h𝔭Q : 𝔭 ⤳ Q :=
        (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp (by rw [hx𝔭]; exact hxy)
      exact (PrimeSpectrum.le_iff_specializes 𝔭 Q).mpr h𝔭Q
  -- Krull's Hauptidealsatz: height 𝔭 ≤ 1; a nonzerodivisor: height 𝔭 ≥ height (a) ≥ 1
  have hle : 𝔭.asIdeal.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) 𝔭.asIdeal hmin
  have hge : 1 ≤ 𝔭.asIdeal.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors ha).trans
      (Ideal.height_mono hmin.1.2)
  rw [hco]
  exact le_antisymm hle hge

end
