import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentStalkFinite
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentStalkIsLocalizedModule

/-! # Finite length of the stalk at a maximal point of the support

**Finite length of the stalk of a coherent sheaf at a maximal point of its support.**

`X` locally Noetherian, `F` coherent, `ξ ∈ X` such that no proper generalization of `ξ` lies in
`Supp F` (`∀ η, η ⤳ ξ → η ∈ Supp F → η = ξ`). Then `length_{O_{X,ξ}} F_ξ < ∞`.

This is the finiteness behind the coefficients `m_ξ = length_{O_{X,ξ}} F_ξ` of Stacks 0BEN
(first paragraph of the proof: "`F_ξ` has finite length since `ξ` is a generic
point of an irreducible component of `Supp F`"): 0BEN applies it to the points `ξ` with
`dim closure {ξ} = d = dim Supp F`, which are maximal in `Supp F` (a proper generalization would give an
irreducible closed subset of `Supp F` of dimension `> d`).

Three declarations:

* `MiyaokaMori.StalkLength.length_ne_top_of_forall_isPrime_isMaximal` (pure commutative algebra,
  Stacks 00L5 / 00KZ / 00KH): `A` Noetherian, `M` a finite `A`-module such that every prime containing
  `Ann M` is maximal; then `length_A M < ∞`. Proof: `M` is a module over `A/Ann M`
  (Mathlib `Module.quotientAnnihilator`) with the same submodule lattice, so `length_A M = length_{A/Ann M} M`
  (`Module.length_eq_of_surjective`). The minimal primes over `Ann M` are maximal, so `A/Ann M` has Krull
  dimension `0` (`Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal`); being Noetherian it
  is Artinian (`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`, Stacks 00KH). A finite module over an
  Artinian ring is Artinian and Noetherian, hence of finite length (`Module.length_ne_top`).

* `AlgebraicGeometry.Scheme.Modules.asIdeal_eq_maximalIdeal_of_mem_support_stalk` (the geometric
  input, for any quasi-coherent `F` on any scheme): under the hypothesis on `ξ`, every prime `p` of
  `A := O_{X,ξ}` in `Supp_A F_ξ` is the maximal ideal. Proof (Stacks 01I8 stalk dictionary, 01J7):
  choose an affine open `W ∋ ξ`, `R := Γ(X, W)`, `𝔮 := hW.primeIdealOf ξ`, so `A = R_𝔮`
  (`IsAffineOpen.isLocalization_stalk`) and the germ map `Γ(F, W) → F_ξ` is the localization of the
  `R`-module `N := Γ(F, W)` at `𝔮` (`isLocalizedModule_germₗ_of_isQuasicoherent`,
  `QuasicoherentStalkIsLocalizedModule`). Let `y := p ∩ R` (prime of `R`, `y ≤ 𝔮` since
  elements outside `𝔮` become units of `A`) and `η := hW.fromSpec y ∈ W`. Then `η ⤳ ξ` (`y ⤳ 𝔮` in
  `Spec R` and `fromSpec` is continuous with `fromSpec 𝔮 = ξ`). Suppose `F_η = 0`; `F_η` is the
  localization of `N` at `y` (`primeIdealOf η = y` by injectivity of the open immersion `fromSpec`), so
  every `n ∈ N` is killed by some `t ∉ y`. Given `x ∈ F_ξ`, write `r • x = germ n` with `r ∉ 𝔮`
  (`IsLocalizedModule.surj`); then `(germ t · germ r) • x = germ (t • n) = 0` with `germ t ∉ p`
  (`t ∉ y = p ∩ R`) and `germ r ∉ p` (a unit). Hence `(F_ξ)_p = 0`, contradicting `p ∈ Supp F_ξ`. So
  `η ∈ Supp F`, hence `η = ξ` by hypothesis, hence `y = 𝔮` (injectivity), and
  `p = (p ∩ R)·A = 𝔮·A = 𝔪_ξ` (`IsLocalization.map_under`, `IsLocalization.AtPrime.map_eq_maximalIdeal`).

* `length_stalk_ne_top_of_forall_specializes` (the main statement): `F_ξ` is a finite `O_{X,ξ}`-module
  (`finite_stalk_of_isCoherent`, `CoherentStalkFinite`), `O_{X,ξ}` is Noetherian (`X` locally
  Noetherian, Mathlib instance), and for a finite module `Supp M = V(Ann M)`
  (`Module.mem_support_iff_of_finite`, Stacks 00L2); the two lemmas above give the result.

**Edge cases.** `ξ ∉ Supp F`: `F_ξ = 0`, `Supp_A F_ξ = ∅`, the maximality condition is vacuous, length `0`.
`F = 0`: same. `ξ` a generic point of `X`: `Spec O_{X,ξ}` is a single point, `p = 𝔪_ξ` automatically.
Zero ring stalk cannot occur (stalks of schemes are local rings).

Source: Stacks 0BEN (proof, first paragraph), 00L5, 00KZ, 00KH; 01I8 (stalk of a quasi-coherent module
over an affine open is the localization of its sections).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Pure algebra (Stacks 00L5, 00KZ, 00KH).** A finite module `M` over a Noetherian ring `A` such that
every prime containing `Ann M` is maximal (i.e. `Supp M` consists of closed points) has finite length.
Proof: pass to the Artinian ring `A / Ann M` (Krull dimension `0` + Noetherian), over which `M` is a finite,
hence Artinian and Noetherian, module with the same submodule lattice. -/
theorem MiyaokaMori.StalkLength.length_ne_top_of_forall_isPrime_isMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M]
    (h : ∀ p : Ideal A, p.IsPrime → Module.annihilator A M ≤ p → p.IsMaximal) :
    Module.length A M ≠ ⊤ := by
  let : Module (A ⧸ Module.annihilator A M) M := Module.quotientAnnihilator
  have : IsScalarTower A (A ⧸ Module.annihilator A M) M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator A M)
  have : Ring.KrullDimLE 0 (A ⧸ Module.annihilator A M) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
      fun J hJ => h J hJ.1.1 hJ.1.2
  have : IsArtinianRing (A ⧸ Module.annihilator A M) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have : Module.Finite (A ⧸ Module.annihilator A M) M :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ Module.annihilator A M) M
  have : IsArtinian (A ⧸ Module.annihilator A M) M := isArtinian_of_fg_of_artinian'
  have : IsNoetherian (A ⧸ Module.annihilator A M) M :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  rw [Module.length_eq_of_surjective (R := A ⧸ Module.annihilator A M)
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

/-- **Geometric input (Stacks 01I8, 01J7).** `F` quasi-coherent on a scheme `X`, `ξ ∈ X` with no proper
generalization in `Supp F`. Then every prime `p` of `O_{X,ξ}` lying in `Supp_{O_{X,ξ}} F_ξ` is the maximal
ideal: the generalization `η ↔ p` of `ξ` has `F_η ≅ (F_ξ)_p ≠ 0`, so `η ∈ Supp F`, so `η = ξ`.
See the module docstring for the affine-local argument. -/
theorem AlgebraicGeometry.Scheme.Modules.asIdeal_eq_maximalIdeal_of_mem_support_stalk
    {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (ξ : X)
    (hmax : ∀ η : X, η ⤳ ξ → η ∈ F.support → η = ξ)
    (p : PrimeSpectrum (X.presheaf.stalk ξ))
    (hp : p ∈ Module.support (X.presheaf.stalk ξ) (F.stalk ξ)) :
    p.asIdeal = IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by
  obtain ⟨W, hW, hξW, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show ξ ∈ (⊤ : X.Opens) from trivial)
  replace hW : AlgebraicGeometry.IsAffineOpen W := hW
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨ξ, hξW⟩ : W)
  set 𝔮 := hW.primeIdealOf ⟨ξ, hξW⟩ with h𝔮
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk ξ) 𝔮.asIdeal :=
    hW.isLocalization_stalk ⟨ξ, hξW⟩
  -- the prime `y = p ∩ Γ(X, W)` of the affine coordinate ring, and the point `η = fromSpec y`
  set y : PrimeSpectrum Γ(X, W) := PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk ξ)) p
    with hy
  have hy𝔮 : y ≤ 𝔮 := by
    intro r hr
    by_contra hr𝔮
    have hu : IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk ξ) r) :=
      IsLocalization.map_units (X.presheaf.stalk ξ) (⟨r, hr𝔮⟩ : 𝔮.asIdeal.primeCompl)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hr hu)
  have hηξ : hW.fromSpec y ⤳ ξ := by
    have h1 : y ⤳ 𝔮 := (PrimeSpectrum.le_iff_specializes y 𝔮).mp hy𝔮
    have h2 := hW.fromSpec.base.hom.map_specializes h1
    rwa [h𝔮, hW.fromSpec_primeIdealOf] at h2
  have hηW : hW.fromSpec y ∈ W := by
    rw [← SetLike.mem_coe, ← hW.range_fromSpec]
    exact ⟨y, rfl⟩
  have hinj : Function.Injective hW.fromSpec := hW.fromSpec.isOpenEmbedding.injective
  have hy' : hW.primeIdealOf ⟨hW.fromSpec y, hηW⟩ = y := by
    apply hinj
    rw [hW.fromSpec_primeIdealOf]
  -- `η ∈ Supp F`: otherwise `F_η = 0` forces `(F_ξ)_p = 0`
  have hη_supp : hW.fromSpec y ∈ F.support := by
    by_contra hns
    have hsub : Subsingleton (F.stalk (hW.fromSpec y)) := not_nontrivial_iff_subsingleton.mp hns
    have hsub' : Subsingleton (F.presheaf.stalk (hW.fromSpec y)) := hsub
    let := F.stalkModuleSections W (hW.fromSpec y) hηW
    have hlocη := F.isLocalizedModule_germₗ_of_isQuasicoherent W (hW.fromSpec y) hηW hW
    rw [hy'] at hlocη
    have hkill : ∀ n : Γ(F, W), ∃ t ∈ y.asIdeal.primeCompl, t • n = 0 :=
      (IsLocalizedModule.subsingleton_iff y.asIdeal.primeCompl
        (F.germₗ W (hW.fromSpec y) hηW)).mp hsub'
    let := F.stalkModuleSections W ξ hξW
    have hlocξ := F.isLocalizedModule_germₗ_of_isQuasicoherent W ξ hξW hW
    have hss : Subsingleton (LocalizedModule p.asIdeal.primeCompl (F.presheaf.stalk ξ)) := by
      rw [LocalizedModule.subsingleton_iff]
      intro x
      obtain ⟨⟨n, r⟩, hr⟩ := IsLocalizedModule.surj 𝔮.asIdeal.primeCompl (F.germₗ W ξ hξW) x
      dsimp only at hr
      have hr' : (r : Γ(X, W)) • x = F.germₗ W ξ hξW n := hr
      obtain ⟨t, ht, htn⟩ := hkill n
      have htp : algebraMap Γ(X, W) (X.presheaf.stalk ξ) t ∈ p.asIdeal.primeCompl := ht
      have hrp : algebraMap Γ(X, W) (X.presheaf.stalk ξ) (r : Γ(X, W)) ∈ p.asIdeal.primeCompl := by
        intro hmem
        exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
          (IsLocalization.map_units (X.presheaf.stalk ξ) r))
      refine ⟨_, Submonoid.mul_mem _ htp hrp, ?_⟩
      have e1 : algebraMap Γ(X, W) (X.presheaf.stalk ξ) (r : Γ(X, W)) • x = (r : Γ(X, W)) • x := rfl
      have e2 : algebraMap Γ(X, W) (X.presheaf.stalk ξ) t • F.germₗ W ξ hξW n =
          t • F.germₗ W ξ hξW n := rfl
      rw [mul_smul, e1, hr', e2, ← LinearMap.map_smul (F.germₗ W ξ hξW) t n, htn, map_zero]
    exact not_nontrivial_iff_subsingleton.mpr hss (Module.mem_support_iff.mp hp)
  -- conclude: `η = ξ`, so `y = 𝔮`, so `p = 𝔮 · O_{X,ξ} = 𝔪_ξ`
  have hηeq : hW.fromSpec y = ξ := hmax _ hηξ hη_supp
  have hy𝔮' : y = 𝔮 := by
    apply hinj
    rw [h𝔮, hW.fromSpec_primeIdealOf]
    exact hηeq
  have h1 : p.asIdeal =
      Ideal.map (algebraMap Γ(X, W) (X.presheaf.stalk ξ)) (p.asIdeal.under Γ(X, W)) :=
    (IsLocalization.map_under 𝔮.asIdeal.primeCompl (X.presheaf.stalk ξ) p.asIdeal).symm
  have h2 : p.asIdeal.under Γ(X, W) = 𝔮.asIdeal := by
    rw [← hy𝔮']
    rfl
  rw [h1, h2]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮.asIdeal (X.presheaf.stalk ξ)

/-- The stalk of a coherent sheaf at a point with
no proper generalization in the support has finite length (see the module docstring). -/
theorem AlgebraicGeometry.Scheme.Modules.length_stalk_ne_top_of_forall_specializes
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (ξ : X)
    (hmax : ∀ η : X, η ⤳ ξ → η ∈ F.support → η = ξ) :
    Module.length (X.presheaf.stalk ξ) (F.stalk ξ) ≠ ⊤ := by
  have : F.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have : Module.Finite (X.presheaf.stalk ξ) (F.stalk ξ) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F ξ
  apply MiyaokaMori.StalkLength.length_ne_top_of_forall_isPrime_isMaximal
  intro p hp hann
  have hmem : (⟨p, hp⟩ : PrimeSpectrum (X.presheaf.stalk ξ)) ∈
      Module.support (X.presheaf.stalk ξ) (F.stalk ξ) := Module.mem_support_iff_of_finite.mpr hann
  have := AlgebraicGeometry.Scheme.Modules.asIdeal_eq_maximalIdeal_of_mem_support_stalk F ξ hmax
    ⟨p, hp⟩ hmem
  simp only at this
  rw [this]
  exact IsLocalRing.maximalIdeal.isMaximal _

end
