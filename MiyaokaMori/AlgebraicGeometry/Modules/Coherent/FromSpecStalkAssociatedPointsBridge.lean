import MiyaokaMori.Prelude
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModulesAssociatedPoints
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentStalkIsLocalizedModule

/-! # Associated points and support along `Spec O_{X,x} → X`

Bridge along `φ := (X.fromSpecStalk x).base : Spec O_{X,x} → X` (Stacks 01J7): primes `𝔭` of the local
ring `O_{X,x}` are the generizations `φ 𝔭` of `x`, compatibly with associated points (Stacks 05AI) and
support (Stacks 01BA) of a quasi-coherent module `F`. Used for the generization of stalk primes in
`RegularMeromorphicDenominatorMaps_StalkRegular`.

* `MiyaokaMori.Module.mem_support_iff_comap_mem_of_isLocalizedModule` (pure algebra): for `R' = S⁻¹R` and
  `M' = S⁻¹M`, `p ∈ Supp_{R'} M' ↔ p ∩ R ∈ Supp_R M`.
* `fromSpecStalk_mem_of_mem`, `primeIdealOf_fromSpecStalk` (any scheme): for an affine open `W ∋ x`,
  `φ 𝔭 ∈ W` and its prime of `Γ(X, W)` is `𝔭 ∩ Γ(X, W)` (contraction along the germ map).
* `mem_support_fromSpecStalk_iff` (`F` quasi-coherent): `φ 𝔭 ∈ Supp F ↔ 𝔭 ∈ Supp_{O_{X,x}} F_x`.
* `isAssociatedPoint_fromSpecStalk_iff_of_isQuasicoherent` (`F` quasi-coherent, `X` locally Noetherian):
  `φ 𝔭` is an associated point of `F` iff `𝔭 ∈ Ass_{O_{X,x}} F_x`.

Method: both stalks `F_x`, `F_{φ 𝔭}` are localizations of the same section module `Γ(F, W)` over
`A = Γ(X, W)` (`isLocalizedModule_germₗ_of_isQuasicoherent`, Stacks 01I8), so `Ass` and `Supp` are compared
over `A` (Mathlib `preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule`, Stacks 0310 (3),
and the support lemma above); no direct comparison `F_{φ 𝔭} ≅ (F_x)_𝔭` is needed. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Support of a localized module** (Stacks 00L2/01BA-style bookkeeping). Let `R' = S⁻¹R` and
`f : M → M'` exhibit `M'` as `S⁻¹M`. A prime `p` of `R'` lies in `Supp_{R'} M'` iff its contraction
`p ∩ R` lies in `Supp_R M`. -/
theorem MiyaokaMori.Module.mem_support_iff_comap_mem_of_isLocalizedModule
    {R R' M M' : Type*} [CommRing R] (S : Submonoid R) [CommRing R'] [Algebra R R']
    [IsLocalization S R'] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [Module R' M'] [IsScalarTower R R' M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (p : PrimeSpectrum R') :
    p ∈ Module.support R' M' ↔ PrimeSpectrum.comap (algebraMap R R') p ∈ Module.support R M := by
  have hunit : ∀ s : S, algebraMap R R' s ∉ p.asIdeal := fun s hs =>
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (IsLocalization.map_units R' s))
  have hcomap : ∀ a : R, a ∈ (PrimeSpectrum.comap (algebraMap R R') p).asIdeal ↔
      algebraMap R R' a ∈ p.asIdeal := fun a => by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rw [Module.mem_support_iff', Module.mem_support_iff']
  constructor
  · rintro ⟨m', hm'⟩
    obtain ⟨⟨m, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f m'
    refine ⟨m, fun r hr h0 => ?_⟩
    have h1 : (algebraMap R R' r * algebraMap R R' t) • IsLocalizedModule.mk' f m t = 0 := by
      rw [mul_smul, algebraMap_smul R' (t : R), ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
        algebraMap_smul R' r, ← map_smul, h0, map_zero]
    refine hm' _ (fun h => ?_) h1
    rcases p.isPrime.mem_or_mem h with h | h
    · exact hr ((hcomap r).mpr h)
    · exact hunit t h
  · rintro ⟨m, hm⟩
    refine ⟨f m, fun r hr => ?_⟩
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective S r
    have ha : a ∉ (PrimeSpectrum.comap (algebraMap R R') p).asIdeal := fun ha =>
      hr (IsLocalization.mk'_mem_iff.mpr ((hcomap a).mp ha))
    intro h0
    rw [← IsLocalizedModule.mk'_one S f, IsLocalizedModule.mk'_smul_mk' R' f,
      IsLocalizedModule.mk'_eq_zero'] at h0
    obtain ⟨s', hs'⟩ := h0
    have hsa : (s' : R) * a ∉ (PrimeSpectrum.comap (algebraMap R R') p).asIdeal := by
      intro h
      rcases (PrimeSpectrum.comap (algebraMap R R') p).isPrime.mem_or_mem h with h | h
      · exact hunit s' ((hcomap s').mp h)
      · exact ha h
    exact hm _ hsa (by rw [mul_smul]; exact hs')

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The image of a prime `𝔭` of `O_{X,x}` under `Spec O_{X,x} → X` lies in every open `W ∋ x`
(it is a generization of `x`). -/
theorem fromSpecStalk_mem_of_mem {W : X.Opens} {x : X} (hx : x ∈ W)
    (𝔭 : AlgebraicGeometry.Spec (X.presheaf.stalk x)) : (X.fromSpecStalk x).base 𝔭 ∈ W := by
  have hspec : (X.fromSpecStalk x).base 𝔭 ⤳ x := by
    have : (X.fromSpecStalk x).base 𝔭 ∈ Set.range (X.fromSpecStalk x) := ⟨𝔭, rfl⟩
    rwa [AlgebraicGeometry.Scheme.range_fromSpecStalk] at this
  exact hspec.mem_open W.2 hx

/-- **The prime of `Γ(X, W)` of the generization `fromSpecStalk x 𝔭`** (Stacks 01J7): for an affine
open `W ∋ x`, the point `y = fromSpecStalk x 𝔭 ∈ W` corresponds to the prime `𝔭 ∩ Γ(X, W)`, the
contraction of `𝔭` along the germ map `Γ(X, W) → O_{X,x}`. -/
theorem primeIdealOf_fromSpecStalk {W : X.Opens} (hW : AlgebraicGeometry.IsAffineOpen W) {x : X}
    (hx : x ∈ W) (𝔭 : AlgebraicGeometry.Spec (X.presheaf.stalk x)) :
    hW.primeIdealOf ⟨(X.fromSpecStalk x).base 𝔭, fromSpecStalk_mem_of_mem hx 𝔭⟩ =
      PrimeSpectrum.comap (X.presheaf.germ W x hx).hom 𝔭 := by
  apply hW.fromSpec.isOpenEmbedding.injective
  rw [hW.fromSpec_primeIdealOf]
  show (X.fromSpecStalk x).base 𝔭 = hW.fromSpec ((AlgebraicGeometry.Spec.map (X.presheaf.germ W x hx)) 𝔭)
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, ← hW.fromSpecStalk_eq_fromSpecStalk hx]
  rfl

section Bridge

variable (F : X.Modules) {x : X}

/-- `Γ(X, W)` acts on the stalk `F_x` through `Γ(X, W) → O_{X,x}` (scalar tower for
`stalkModuleSections`). -/
theorem isScalarTower_stalkModuleSections {W : X.Opens} (hx : x ∈ W) :
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    letI := F.stalkModuleSections W x hx
    IsScalarTower Γ(X, W) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let := F.stalkModuleSections W x hx
  ⟨fun a r m => mul_smul (X.presheaf.germ W x hx a) r m⟩

variable [F.IsQuasicoherent]

/-- **Support along `Spec O_{X,x} → X`** (Stacks 01BA + 01J7): for a quasi-coherent `F` and a prime `𝔭`
of `O_{X,x}`, the generization `y = fromSpecStalk x 𝔭` lies in `Supp F` iff `𝔭 ∈ Supp_{O_{X,x}} F_x`.

Proof. Choose an affine open `W ∋ x`, `A := Γ(X, W)`, `N := Γ(F, W)`; `y ∈ W` and its prime is
`𝔮' = 𝔭 ∩ A` (`primeIdealOf_fromSpecStalk`). `F_x = N_𝔮` and `F_y = N_{𝔮'}` as `A`-modules
(`isLocalizedModule_germₗ_of_isQuasicoherent`). Then `y ∈ Supp F ↔ F_y ≠ 0 ↔ 𝔮' ∈ Supp_A N`
(`Module.mem_support_iff`), and `𝔭 ∈ Supp_{A_𝔮}(N_𝔮) ↔ 𝔭 ∩ A ∈ Supp_A N`
(`mem_support_iff_comap_mem_of_isLocalizedModule`). -/
theorem mem_support_fromSpecStalk_iff (𝔭 : AlgebraicGeometry.Spec (X.presheaf.stalk x)) :
    (X.fromSpecStalk x).base 𝔭 ∈ F.support ↔
      𝔭 ∈ Module.support (X.presheaf.stalk x) (F.stalk x) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyW : (X.fromSpecStalk x).base 𝔭 ∈ W := fromSpecStalk_mem_of_mem hxW 𝔭
  have hq' := primeIdealOf_fromSpecStalk hW hxW 𝔭
  let := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hlocx : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  let := F.stalkModuleSections W x hxW
  have := F.isLocalizedModule_germₗ_of_isQuasicoherent W x hxW hW
  have := F.isScalarTower_stalkModuleSections hxW
  let := F.stalkModuleSections W _ hyW
  have := F.isLocalizedModule_germₗ_of_isQuasicoherent W _ hyW hW
  have e1 : 𝔭 ∈ Module.support (X.presheaf.stalk x) (F.stalk x) ↔
      PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) 𝔭 ∈
        Module.support Γ(X, W) Γ(F, W) :=
    MiyaokaMori.Module.mem_support_iff_comap_mem_of_isLocalizedModule
      (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl (F.germₗ W x hxW) 𝔭
  have e2 : (X.fromSpecStalk x).base 𝔭 ∈ F.support ↔
      hW.primeIdealOf ⟨_, hyW⟩ ∈ Module.support Γ(X, W) Γ(F, W) := by
    show Nontrivial (F.stalk _) ↔ _
    rw [Module.mem_support_iff]
    exact (IsLocalizedModule.iso _ (F.germₗ W _ hyW)).toEquiv.nontrivial_congr.symm
  have e4 : PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) 𝔭 =
      hW.primeIdealOf ⟨_, hyW⟩ := by rw [hq']; rfl
  rw [e2, e1, e4]

/-- **Associated points along `Spec O_{X,x} → X`** (Stacks 05AI + 01J7 + 0310): for a quasi-coherent `F`
on a locally Noetherian `X` and a prime `𝔭` of `O_{X,x}`, the generization `y = fromSpecStalk x 𝔭` is an
associated point of `F` iff `𝔭 ∈ Ass_{O_{X,x}} F_x`.

Proof. As in `mem_support_fromSpecStalk_iff`: `A := Γ(X, W)` (Noetherian), `N := Γ(F, W)`,
`𝔮' = 𝔭 ∩ A` the prime of `y`. By Mathlib
`preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule` (Stacks 0310 (3)),
`𝔭 ∈ Ass_{A_𝔮}(N_𝔮) ↔ 𝔭 ∩ A ∈ Ass_A N` and `𝔪_y ∈ Ass_{A_{𝔮'}}(N_{𝔮'}) ↔ 𝔪_y ∩ A ∈ Ass_A N`, where
`𝔪_y ∩ A = 𝔮'` (`IsLocalization.AtPrime.under_maximalIdeal`). -/
theorem isAssociatedPoint_fromSpecStalk_iff_of_isQuasicoherent
    [AlgebraicGeometry.IsLocallyNoetherian X] (𝔭 : AlgebraicGeometry.Spec (X.presheaf.stalk x)) :
    F.IsAssociatedPoint ((X.fromSpecStalk x).base 𝔭) ↔
      𝔭.asIdeal ∈ associatedPrimes (X.presheaf.stalk x) (F.stalk x) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyW : (X.fromSpecStalk x).base 𝔭 ∈ W := fromSpecStalk_mem_of_mem hxW 𝔭
  have hq' := primeIdealOf_fromSpecStalk hW hxW 𝔭
  have : IsNoetherianRing Γ(X, W) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hlocx : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  let := F.stalkModuleSections W x hxW
  have := F.isLocalizedModule_germₗ_of_isQuasicoherent W x hxW hW
  have := F.isScalarTower_stalkModuleSections hxW
  let := X.presheaf.algebra_section_stalk ⟨_, hyW⟩
  have hlocy : IsLocalization.AtPrime (X.presheaf.stalk ((X.fromSpecStalk x).base 𝔭))
      (hW.primeIdealOf ⟨_, hyW⟩).asIdeal := hW.isLocalization_stalk ⟨_, hyW⟩
  let := F.stalkModuleSections W _ hyW
  have := F.isLocalizedModule_germₗ_of_isQuasicoherent W _ hyW hW
  have := F.isScalarTower_stalkModuleSections hyW
  have e1 : 𝔭.asIdeal ∈ associatedPrimes (X.presheaf.stalk x) (F.stalk x) ↔
      𝔭.asIdeal.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) ∈
        associatedPrimes Γ(X, W) Γ(F, W) := by
    show 𝔭.asIdeal ∈ associatedPrimes (X.presheaf.stalk x) (F.presheaf.stalk x) ↔ _
    rw [← Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl (X.presheaf.stalk x) (F.germₗ W x hxW)]
    rfl
  have e2 : F.IsAssociatedPoint ((X.fromSpecStalk x).base 𝔭) ↔
      (IsLocalRing.maximalIdeal (X.presheaf.stalk ((X.fromSpecStalk x).base 𝔭))).comap
        (algebraMap Γ(X, W) _) ∈ associatedPrimes Γ(X, W) Γ(F, W) := by
    show IsLocalRing.maximalIdeal _ ∈ associatedPrimes (X.presheaf.stalk ((X.fromSpecStalk x).base 𝔭))
      (F.presheaf.stalk ((X.fromSpecStalk x).base 𝔭)) ↔ _
    rw [← Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      (hW.primeIdealOf ⟨_, hyW⟩).asIdeal.primeCompl
      (X.presheaf.stalk ((X.fromSpecStalk x).base 𝔭)) (F.germₗ W _ hyW)]
    rfl
  have e3 : (IsLocalRing.maximalIdeal (X.presheaf.stalk ((X.fromSpecStalk x).base 𝔭))).comap
      (algebraMap Γ(X, W) _) = (hW.primeIdealOf ⟨_, hyW⟩).asIdeal :=
    IsLocalization.AtPrime.under_maximalIdeal _ _
  have e4 : 𝔭.asIdeal.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) =
      (hW.primeIdealOf ⟨_, hyW⟩).asIdeal := by rw [hq']; rfl
  rw [e2, e3, e1, e4]

end Bridge

end AlgebraicGeometry.Scheme.Modules

end
