import MiyaokaMori.Prelude
import Mathlib.Data.ENat.BigOperators
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdeal
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealBasic
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealEqMapGerm

/-! # The length sum of an ideal sheaf over finitely many points

The length sum Σ_{x ∈ T} length_{O_{X,x}}(O_{X,x}/I_x) of a quasi-coherent ideal sheaf `I`
over a finite set of points `T`, and its basic properties: it is `0` iff all the stalk ideals
`I_x` (`x ∈ T`) are the unit ideal; a point of the support has a proper stalk ideal; and the sum
is finite when `T` is a finite set of closed points containing the support of `I` on a locally
Noetherian scheme.

This is the induction quantity of Stacks 0AHH; Stacks 0AGT also measures its conclusion by it.

Source: Stacks 0AHH (proof: "we argue by induction on Σ length_{O_{X,x}}(O_{X,x}/I_x)");
Stacks 0AGT (statement).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The length sum `Σ_{x ∈ T} length_{O_{X,x}}(O_{X,x} ⧸ I_x)` (in `ℕ∞`), where `I_x` is the
stalk ideal `IdealSheafData.stalkIdeal`. -/
def lengthSum {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (T : Finset X) : ℕ∞ :=
  ∑ x ∈ T, Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ I.stalkIdeal x)

/-- The length sum vanishes iff every stalk ideal over `T` is the unit ideal. -/
theorem lengthSum_eq_zero_iff {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)
    (T : Finset X) : I.lengthSum T = 0 ↔ ∀ x ∈ T, I.stalkIdeal x = ⊤ := by
  unfold lengthSum
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le)]
  simp_rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]

/-- A term of the length sum is finite as soon as the whole sum is. -/
theorem length_ne_top_of_lengthSum_ne_top {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (T : Finset X) (h : I.lengthSum T ≠ ⊤) {x : X} (hx : x ∈ T) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ I.stalkIdeal x) ≠ ⊤ :=
  (ENat.lt_top_of_sum_ne_top h hx).ne

/-- Stalk criterion for the support: at a point of the support the stalk ideal is proper.
(Converse of `stalkIdeal_eq_top_of_notMem_support`.)

Proof: choose an affine open `U ∋ x`; `x ∈ I.support` means `x` lies in the zero locus of
`I(U)`, i.e. no `f ∈ I(U)` has `x ∈ D(f)`, i.e. (`Scheme.mem_basicOpen`) no germ `f_x` is a unit,
i.e. `I(U) ⊆ 𝔮 := primeIdealOf x` (`IsLocalization.AtPrime.isUnit_to_map_iff`, the stalk being
the localization of `Γ(U)` at `𝔮`). Hence `I_x = I(U)·O_{X,x} ⊆ 𝔮·O_{X,x} = 𝔪_x ≠ ⊤`
(`IsLocalization.AtPrime.map_eq_maximalIdeal`). -/
theorem stalkIdeal_ne_top_of_mem_support {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (x : X) (hx : x ∈ I.support) : I.stalkIdeal x ≠ ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ I x U hxU]
  rw [IdealSheafData.mem_support_iff_of_mem hxU, AlgebraicGeometry.Scheme.mem_zeroLocus_iff] at hx
  let _inst := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hxU⟩
  have hle : I.ideal U ≤ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    intro f hf
    by_contra hf'
    apply hx f hf
    rw [AlgebraicGeometry.Scheme.mem_basicOpen X f x hxU]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal f).mpr hf'
  intro htop
  have hmono := Ideal.map_mono (f := (X.presheaf.germ U.1 x hxU).hom) hle
  rw [htop] at hmono
  have hmax : ((U.2.primeIdealOf ⟨x, hxU⟩).asIdeal).map (X.presheaf.germ U.1 x hxU).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal _ (X.presheaf.stalk x)
  rw [hmax] at hmono
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hmono)

/-- `x ∈ I.support ↔ I_x ≠ ⊤`. -/
theorem mem_support_iff_stalkIdeal_ne_top {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (x : X) : x ∈ I.support ↔ I.stalkIdeal x ≠ ⊤ :=
  ⟨stalkIdeal_ne_top_of_mem_support I x, fun h => by
    by_contra hx
    exact h (stalkIdeal_eq_top_of_notMem_support I x hx)⟩

/-- If the length sum over a finite set containing the support vanishes, the ideal sheaf is the
unit ideal (`support_eq_bot_iff`). -/
theorem eq_top_of_lengthSum_eq_zero {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)
    (T : Finset X) (hsupp : (I.support : Set X) ⊆ T) (h : I.lengthSum T = 0) : I = ⊤ := by
  rw [lengthSum_eq_zero_iff] at h
  rw [← IdealSheafData.support_eq_bot_iff]
  ext x
  simp only [TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact stalkIdeal_ne_top_of_mem_support I x hx (h x (hsupp hx))

/-- Finiteness of the length sum: on a locally Noetherian scheme, if `T` is a finite set of
**closed** points containing the support of `I`, then every `O_{X,x}/I_x` (`x ∈ T`) has finite
length, so the length sum is not `⊤`.

Proof (Stacks 0AHH, first paragraph: "O_{X,x}/I_x has finite length since its support is the
closed point"): fix `x ∈ T`, `R := O_{X,x}` (a Noetherian local ring), `J := I_x`.
1. It suffices that `R/J` is an Artinian ring: then `length_R(R/J) = length_{R/J}(R/J) < ∞`
   (`Module.length_eq_of_surjective`, `Module.length_ne_top`).
2. `R/J` is Noetherian; by Hopkins–Levitzki (`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`)
   it suffices that every prime of `R/J` is maximal, i.e. every prime `Q ⊇ J` of `R` equals `𝔪_x`.
3. Choose an affine open `U ∋ x`, `A := Γ(U)`, `𝔮 := primeIdealOf x`, so `R = A_𝔮` and
   `J = I(U)·A_𝔮`. A prime `Q ⊇ J` of `A_𝔮` is `𝔭·A_𝔮` for the prime `𝔭 := Q ∩ A ⊆ 𝔮`, and
   `I(U) ⊆ 𝔭`. Let `y := fromSpec 𝔭 ∈ U`. Then `y ∈ V(I(U))`, so `y ∈ I.support ⊆ T`, so `y` is a
   closed point. Since `𝔭 ⊆ 𝔮`, `y ⤳ x` (`PrimeSpectrum.le_iff_specializes`, `fromSpec`
   continuous), i.e. `x ∈ closure {y} = {y}`, so `y = x`, `𝔭 = 𝔮`, and `Q = 𝔮·A_𝔮 = 𝔪_x`. -/
theorem lengthSum_ne_top {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (I : X.IdealSheafData) (T : Finset X) (hT : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hsupp : (I.support : Set X) ⊆ T) : I.lengthSum T ≠ ⊤ := by
  rw [lengthSum, ENat.sum_ne_top]
  intro x hxT
  -- Step A: every prime `Q ⊇ I_x` of `O_{X,x}` is the maximal ideal.
  have hprime : ∀ Q : Ideal (X.presheaf.stalk x), Q.IsPrime → I.stalkIdeal x ≤ Q →
      Q = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    intro Q hQ hJQ
    obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
    have hU : AlgebraicGeometry.IsAffineOpen U.1 := U.2
    let _inst := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
    -- the prime `𝔭 := Q ∩ Γ(U)` and the point `y := fromSpec 𝔭 ∈ U`
    have h𝔭 : (Q.under Γ(X, U)).IsPrime := Ideal.IsPrime.under Γ(X, U) Q
    have h𝔭𝔮 : Q.under Γ(X, U) ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
      rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
    have hI𝔭 : I.ideal U ≤ Q.under Γ(X, U) := by
      rw [stalkIdeal_eq_map_germ I x U hxU] at hJQ
      exact Ideal.map_le_iff_le_comap.mp hJQ
    set 𝔭 : PrimeSpectrum Γ(X, U) := ⟨Q.under Γ(X, U), h𝔭⟩ with h𝔭def
    have hyU : hU.fromSpec 𝔭 ∈ U.1 := by
      have : hU.fromSpec 𝔭 ∈ Set.range hU.fromSpec := Set.mem_range_self 𝔭
      rwa [hU.range_fromSpec] at this
    have hysupp : hU.fromSpec 𝔭 ∈ I.support := by
      rw [IdealSheafData.mem_support_iff_of_mem hyU, AlgebraicGeometry.Scheme.mem_zeroLocus_iff]
      intro f hf hyf
      have h1 : 𝔭 ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := hyf
      rw [IsAffineOpen.fromSpec_preimage_basicOpen] at h1
      exact h1 (hI𝔭 hf)
    have hyclosed : IsClosed ({hU.fromSpec 𝔭} : Set X) := hT _ (hsupp hysupp)
    -- `y ⤳ x`, hence `y = x` since `y` is closed
    have hyx : hU.fromSpec 𝔭 ⤳ x := by
      have h1 : 𝔭 ⤳ hU.primeIdealOf ⟨x, hxU⟩ :=
        (PrimeSpectrum.le_iff_specializes _ _).mp h𝔭𝔮
      have h2 := h1.map hU.fromSpec.continuous
      rwa [hU.fromSpec_primeIdealOf ⟨x, hxU⟩] at h2
    have hyx' : hU.fromSpec 𝔭 = x := by
      have h1 : x ∈ closure ({hU.fromSpec 𝔭} : Set X) := hyx.mem_closure
      rw [hyclosed.closure_eq, Set.mem_singleton_iff] at h1
      exact h1.symm
    -- hence `𝔭 = 𝔮` and `Q = 𝔮·O_{X,x} = 𝔪_x`
    have h𝔭𝔮' : 𝔭 = hU.primeIdealOf ⟨x, hxU⟩ := by
      apply hU.fromSpec.isOpenEmbedding.injective
      exact hyx'.trans (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm
    have hQ' : Q.under Γ(X, U) = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
      have := congrArg PrimeSpectrum.asIdeal h𝔭𝔮'
      simpa [h𝔭def] using this
    rw [← IsLocalization.map_under (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) Q, hQ']
    exact IsLocalization.AtPrime.map_eq_maximalIdeal _ (X.presheaf.stalk x)
  -- Step B: `O_{X,x} ⧸ I_x` is an Artinian ring (Hopkins–Levitzki).
  have hdim : Ring.KrullDimLE 0 (X.presheaf.stalk x ⧸ I.stalkIdeal x) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    have hle : I.stalkIdeal x ≤ P.comap (Ideal.Quotient.mk (I.stalkIdeal x)) := by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact P.zero_mem
    have hQ := hprime (P.comap (Ideal.Quotient.mk (I.stalkIdeal x))) inferInstance hle
    have hP' : P = (P.comap (Ideal.Quotient.mk (I.stalkIdeal x))).map
        (Ideal.Quotient.mk (I.stalkIdeal x)) :=
      (Ideal.map_comap_of_surjective (Ideal.Quotient.mk (I.stalkIdeal x))
        Ideal.Quotient.mk_surjective P).symm
    rw [hP', hQ]
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (I.stalkIdeal x))
      Ideal.Quotient.mk_surjective
      (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)) with h | h
    · exfalso
      rw [← hQ, ← hP'] at h
      exact hP.ne_top h
    · exact h
  have hart : IsArtinianRing (X.presheaf.stalk x ⧸ I.stalkIdeal x) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  -- Step C: transport the length along the surjection `O_{X,x} → O_{X,x}/I_x`.
  have hlen : Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ I.stalkIdeal x) =
      Module.length (X.presheaf.stalk x ⧸ I.stalkIdeal x)
        (X.presheaf.stalk x ⧸ I.stalkIdeal x) :=
    Module.length_eq_of_surjective (by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective)
  rw [hlen]
  exact Module.length_ne_top

end AlgebraicGeometry.Scheme.IdealSheafData

end
