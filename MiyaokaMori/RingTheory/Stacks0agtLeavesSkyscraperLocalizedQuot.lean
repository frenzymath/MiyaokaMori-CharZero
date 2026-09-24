import MiyaokaMori.Prelude
import Mathlib.RingTheory.Support
import MiyaokaMori.RingTheory.Stacks0agtLeavesFiniteSupportDecomposition

/-! # Algebraic helpers for the skyscraper decomposition of quotient families of ideal sheaves

Pure commutative algebra, at the variable level (no schemes):

* `quotLocMap`: for `B → R` with `R` a localization of `B` at `S`, ideals `J', K' ⊆ B` and
  `Jx, Kx ⊆ R` with `J'·R ≤ Jx`, `K'·R ≤ Kx`, the induced `B`-linear map
  `K'/J' → Kx/Jx` (on the images `Submodule.map J'.mkQ K'` and `Submodule.map Jx.mkQ Kx`);
* `isLocalizedModule_quotLocMap`: when `Jx = J'·R` and `Kx = K'·R` this map is the localization
  of the `B`-module `K'/J'` at `S` (`IsLocalizedModule`) — "localization commutes with quotients
  of ideals";
* `notMem_support_quot_of_eq`: if moreover `Kx = Jx` for `R = B_𝔭`, then `𝔭 ∉ supp (K'/J')`;
* `bijective_pi_of_isLocalizedModule`: the finite-support decomposition
  `Module.bijective_pi_localizedModule_of_support_subset` transported along arbitrary
  localization maps `f_q : G → N_q` (`IsLocalizedModule.iso`), for a finite *set* of maximal
  ideals.

Used by the affine-local step of Stacks 0AGT, step 2 (module `Stacks0agtLeavesSkyscraperAffine`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

noncomputable section

namespace MiyaokaMori.Skyscraper0agt

section LocalizedQuot

variable {B : Type u} {R : Type v} [CommRing B] [CommRing R] [Algebra B R]
variable (J' K' : Ideal B) (Jx Kx : Ideal R)

/-- The `B`-linear map `K'/J' → Kx/Jx` induced by `algebraMap B R`, for `J'·R ≤ Jx`, `K'·R ≤ Kx`. -/
def quotLocMap (hJ : J'.map (algebraMap B R) ≤ Jx) (hK : K'.map (algebraMap B R) ≤ Kx) :
    Submodule.map J'.mkQ K' →ₗ[B] (Submodule.map Jx.mkQ Kx).restrictScalars B :=
  (Ideal.quotientMapₐ Jx (Algebra.ofId B R) (Ideal.map_le_iff_le_comap.mp hJ)).toLinearMap.restrict
    (by
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨algebraMap B R k, hK (Ideal.mem_map_of_mem _ hk), rfl⟩)

theorem quotLocMap_coe_apply_mk (hJ : J'.map (algebraMap B R) ≤ Jx)
    (hK : K'.map (algebraMap B R) ≤ Kx) (k : B) (hk : J'.mkQ k ∈ Submodule.map J'.mkQ K') :
    ((quotLocMap J' K' Jx Kx hJ hK ⟨J'.mkQ k, hk⟩ :
      (Submodule.map Jx.mkQ Kx).restrictScalars B) : R ⧸ Jx) =
      Ideal.Quotient.mk Jx (algebraMap B R k) := rfl

theorem quotLocMap_coe_apply (hJ : J'.map (algebraMap B R) ≤ Jx)
    (hK : K'.map (algebraMap B R) ≤ Kx) (g : Submodule.map J'.mkQ K') :
    ((quotLocMap J' K' Jx Kx hJ hK g : (Submodule.map Jx.mkQ Kx).restrictScalars B) : R ⧸ Jx) =
      Ideal.quotientMap Jx (algebraMap B R) (Ideal.map_le_iff_le_comap.mp hJ) g.1 := rfl

/-- **Localization commutes with quotients of ideals.** If `R` is the localization of `B` at
`S`, `Jx = J'·R` and `Kx = K'·R`, then `K'/J' → Kx/Jx` is the localization of the `B`-module
`K'/J'` at `S`.

Proof: the three axioms of `IsLocalizedModule`. (i) `s ∈ S` acts on `Kx/Jx` through the unit
`algebraMap s` of `R`, hence bijectively. (ii) Every element of `Kx/Jx` is `mk r`, `r ∈ K'·R`, and
`r · s = k/1` for some `s ∈ S`, `k ∈ K'` (`IsLocalization.mem_map_algebraMap_iff`), so
`s • mk r = mk (k/1)` is in the image. (iii) If `mk (k₁/1) = mk (k₂/1)` then `(k₁ - k₂)/1 ∈ J'·R`,
so `(k₁ - k₂) s = j/1` for some `s ∈ S`, `j ∈ J'`, so `c (k₁ - k₂) s = c j ∈ J'` for some `c ∈ S`
(`IsLocalization.eq_iff_exists`), i.e. `(c s) • mk k₁ = (c s) • mk k₂`. -/
theorem isLocalizedModule_quotLocMap (S : Submonoid B) [IsLocalization S R]
    (hJ : Jx = J'.map (algebraMap B R)) (hK : Kx = K'.map (algebraMap B R)) :
    IsLocalizedModule S (quotLocMap J' K' Jx Kx hJ.ge hK.ge) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap B R s) := IsLocalization.map_units R s
    constructor
    · intro a b e
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at e
      apply Subtype.ext
      have e' := congrArg Subtype.val e
      simp only [Submodule.coe_smul] at e'
      rw [← algebraMap_smul R (s : B), ← algebraMap_smul R (s : B)] at e'
      exact hu.smul_left_cancel.mp e'
    · intro a
      refine ⟨((hu.unit⁻¹ : Rˣ) : R) • a, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul R (s : B), smul_smul, IsUnit.mul_val_inv,
        one_smul]
  surj := by
    rintro ⟨_, r, hr, rfl⟩
    rw [hK] at hr
    obtain ⟨⟨k, s⟩, hks⟩ := (IsLocalization.mem_map_algebraMap_iff S R).mp hr
    refine ⟨(⟨J'.mkQ k, Submodule.mem_map_of_mem k.2⟩, s), ?_⟩
    apply Subtype.ext
    rw [quotLocMap_coe_apply_mk]
    show (s : B) • Ideal.Quotient.mk Jx r = Ideal.Quotient.mk Jx (algebraMap B R k)
    rw [← Ideal.Quotient.mkₐ_eq_mk B, ← map_smul, Algebra.smul_def, mul_comm, hks]
  exists_of_eq := by
    rintro ⟨_, k₁, hk₁, rfl⟩ ⟨_, k₂, hk₂, rfl⟩ h
    have h' : Ideal.Quotient.mk Jx (algebraMap B R k₁) = Ideal.Quotient.mk Jx (algebraMap B R k₂) :=
      congrArg Subtype.val h
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, hJ] at h'
    obtain ⟨⟨j, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff S R).mp h'
    rw [← map_mul, IsLocalization.eq_iff_exists S] at hjs
    obtain ⟨c, hc⟩ := hjs
    refine ⟨c * s, ?_⟩
    apply Subtype.ext
    show ((c * s : S) : B) • Ideal.Quotient.mk J' k₁ = ((c * s : S) : B) • Ideal.Quotient.mk J' k₂
    rw [← Ideal.Quotient.mkₐ_eq_mk B, ← map_smul, ← map_smul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← smul_sub, smul_eq_mul, Submonoid.coe_mul]
    have : (c : B) * s * (k₁ - k₂) = c * j := by rw [← hc]; ring
    rw [this]
    exact J'.mul_mem_left _ j.2

/-- If `R = B_𝔭` and `K'·R = J'·R`, then `𝔭 ∉ supp_B (K'/J')`. -/
theorem notMem_support_quot_of_eq (𝔭 : PrimeSpectrum B) [IsLocalization.AtPrime R 𝔭.asIdeal]
    (hJ : Jx = J'.map (algebraMap B R)) (hK : Kx = K'.map (algebraMap B R)) (hJK : Kx = Jx) :
    𝔭 ∉ Module.support B (Submodule.map J'.mkQ K') := by
  have := isLocalizedModule_quotLocMap J' K' Jx Kx 𝔭.asIdeal.primeCompl hJ hK
  have hsub : Subsingleton ((Submodule.map Jx.mkQ Kx).restrictScalars B) := by
    refine (subsingleton_iff_forall_eq 0).mpr ?_
    rintro ⟨_, r, hr, rfl⟩
    apply Subtype.ext
    show Ideal.Quotient.mk Jx r = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hJK]
    exact hr
  rw [Module.notMem_support_iff']
  intro m
  obtain ⟨r, hr, hrm⟩ := (IsLocalizedModule.subsingleton_iff 𝔭.asIdeal.primeCompl
    (quotLocMap J' K' Jx Kx hJ.ge hK.ge)).mp hsub m
  exact ⟨r, hr, hrm⟩

end LocalizedQuot

/-- **Finite-support decomposition along arbitrary localization maps.** `B` Noetherian, `G` a
finitely generated `B`-module, `S` a finite set of maximal ideals containing `supp G`, and for
every `q ∈ S` a `B`-linear map `f_q : G → N_q` which is a localization of `G` at `q`
(`IsLocalizedModule`). Then `g ↦ (f_q g)_{q ∈ S}` is bijective.

Proof: `Module.bijective_pi_localizedModule_of_support_subset` gives the statement for
`N_q = G_q` (`LocalizedModule`), and `IsLocalizedModule.iso` identifies `G_q ≅ N_q` compatibly
with the maps from `G` (`IsLocalizedModule.iso_mk_one`). -/
theorem bijective_pi_of_isLocalizedModule {B : Type u} [CommRing B] [IsNoetherianRing B]
    (G : Type u) [AddCommGroup G] [Module B G] [Module.Finite B G]
    (S : Set (PrimeSpectrum B)) (hSfin : S.Finite) (hmax : ∀ q ∈ S, q.asIdeal.IsMaximal)
    (hsupp : Module.support B G ⊆ S)
    (N : S → Type w) [∀ q, AddCommGroup (N q)] [∀ q, Module B (N q)]
    (f : ∀ q : S, G →ₗ[B] N q) (hf : ∀ q : S, IsLocalizedModule q.1.asIdeal.primeCompl (f q)) :
    Function.Bijective (fun g : G => fun q : S => f q g) := by
  have hbij := Module.bijective_pi_localizedModule_of_support_subset G hSfin.toFinset
    (fun q hq => hmax q (hSfin.mem_toFinset.mp hq))
    (fun q hq => hSfin.mem_toFinset.mpr (hsupp hq))
  let φ : ∀ q : S, LocalizedModule q.1.asIdeal.primeCompl G ≃ₗ[B] N q := fun q =>
    haveI := hf q
    IsLocalizedModule.iso q.1.asIdeal.primeCompl (f q)
  have hφ : ∀ (q : S) (g : G), φ q (LocalizedModule.mkLinearMap q.1.asIdeal.primeCompl G g) = f q g :=
    fun q g => by
      have := hf q
      exact IsLocalizedModule.iso_mk_one q.1.asIdeal.primeCompl (f q) g
  constructor
  · intro g₁ g₂ h
    apply hbij.1
    funext q
    have hq : q.1 ∈ S := hSfin.mem_toFinset.mp q.2
    apply (φ ⟨q.1, hq⟩).injective
    rw [hφ ⟨q.1, hq⟩ g₁, hφ ⟨q.1, hq⟩ g₂]
    exact congrFun h ⟨q.1, hq⟩
  · intro n
    obtain ⟨g, hg⟩ := hbij.2 (fun q => (φ ⟨q.1, hSfin.mem_toFinset.mp q.2⟩).symm
      (n ⟨q.1, hSfin.mem_toFinset.mp q.2⟩))
    refine ⟨g, funext fun q => ?_⟩
    have hq' : q.1 ∈ hSfin.toFinset := hSfin.mem_toFinset.mpr q.2
    have := congrFun hg ⟨q.1, hq'⟩
    dsimp only at this
    show f q g = n q
    rw [← hφ q g]
    exact (congrArg (φ q) this).trans ((φ q).apply_symm_apply (n q))

end MiyaokaMori.Skyscraper0agt

end
