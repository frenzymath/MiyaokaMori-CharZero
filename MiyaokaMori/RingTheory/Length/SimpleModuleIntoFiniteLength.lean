import MiyaokaMori.Prelude

/-! # A simple module embeds into every nontrivial module of finite length

**A simple module killed by the maximal ideal embeds into every nontrivial module of finite length**
(over a local ring). Pure module theory, used in the dévissage of coherent sheaves
(`CoherentDevissageSupportSubset`) to compare the stalk `G_ξ ≅ κ(ξ)` of the generator sheaf with the
stalk `F_ξ` of the sheaf being dévissaged.

`R` local, `G` with `length_R G = 1`, `M` nontrivial with `length_R M < ∞`. Then there is an injective
`R`-linear map `G → M`. (The hypothesis `m_R ≤ Ann G` of `hgen` in the dévissage is not needed: a simple
module over a local ring is automatically killed by the maximal ideal, step 4.)

Proof (Stacks 00J4-style socle argument, written out).
1. `length G = 1` means `G` is simple (Mathlib `Module.length_eq_one_iff`).
2. `length M ≠ ⊤` means `M` has finite length (`Module.length_ne_top_iff`), hence is Artinian
   (`isFiniteLength_iff_isNoetherian_isArtinian`), so the lattice of submodules of `M` is well-founded
   and atomic (`isAtomic_of_orderBot_wellFounded_lt`); `M ≠ 0` gives an atom `S` (a minimal nonzero
   submodule), which is a simple module (`isSimpleModule_iff_isAtom`).
3. The annihilator of a simple module is a maximal ideal (`IsSimpleModule.annihilator_isMaximal`), and
   the only maximal ideal of `R` is `m_R` (`IsLocalRing.eq_maximalIdeal`): so `m_R` kills `S`. Pick
   `0 ≠ m ∈ S`; then `m_R • m = 0`.
4. Pick `0 ≠ g ∈ G`. `R → G`, `a ↦ a • g`, is surjective (`IsSimpleModule.toSpanSingleton_surjective`)
   with kernel a maximal ideal (`IsSimpleModule.ker_toSpanSingleton_isMaximal`), hence `= m_R`.
   `R → M`, `a ↦ a • m`, has kernel containing `m_R` (step 3) and `≠ ⊤` (`m ≠ 0`), hence `= m_R`.
5. So `G ≅ R ⧸ m_R` (`LinearMap.quotKerEquivOfSurjective`) and `a ↦ a • m` descends to an injective
   map `R ⧸ m_R → M` (`Submodule.liftQ`, `Submodule.ker_liftQ_eq_bot'`). Compose.

Edge cases: `M` nontrivial is needed (otherwise no injective map from `G ≠ 0`); `G` nontrivial follows
from `length G = 1`. The zero ring is excluded by `IsLocalRing`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace MiyaokaMori.CoherentDevissage

/-- **Socle of an Artinian module over a local ring.** A nontrivial Artinian module over a local ring
contains a nonzero element killed by the maximal ideal (step 2–3 of the module docstring). -/
theorem exists_ne_zero_maximalIdeal_smul_eq_zero {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Nontrivial M] [IsArtinian R M] :
    ∃ m : M, m ≠ 0 ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, a • m = 0 := by
  have : IsAtomic (Submodule R M) :=
    isAtomic_of_orderBot_wellFounded_lt (wellFounded_lt (α := Submodule R M))
  have : Nontrivial (Submodule R M) := ⟨⟨⊥, ⊤, bot_ne_top⟩⟩
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (α := Submodule R M)
  have hsimple : IsSimpleModule R S := isSimpleModule_iff_isAtom.mpr hS
  have hmax : (Module.annihilator R S).IsMaximal := IsSimpleModule.annihilator_isMaximal
  have hann : Module.annihilator R S = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  obtain ⟨m, hmS, hm0⟩ := (Submodule.ne_bot_iff S).mp hS.1
  refine ⟨m, hm0, fun a ha => ?_⟩
  have ha' : a ∈ Module.annihilator R S := hann ▸ ha
  have := Module.mem_annihilator.mp ha' ⟨m, hmS⟩
  exact congrArg Subtype.val this

/-- Over a local ring `R`, a module `G` of length `1` embeds into every nontrivial module `M` of finite length (see the module
docstring). -/
theorem exists_injective_linearMap_of_length_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    {G M : Type*} [AddCommGroup G] [Module R G] [AddCommGroup M] [Module R M]
    (hlen : Module.length R G = 1) [Nontrivial M] (hM : Module.length R M ≠ ⊤) :
    ∃ f : G →ₗ[R] M, Function.Injective f := by
  have hsimple : IsSimpleModule R G := Module.length_eq_one_iff.mp hlen
  have hfl : IsFiniteLength R M := Module.length_ne_top_iff.mp hM
  have hart : IsArtinian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  obtain ⟨m, hm0, hmkill⟩ := exists_ne_zero_maximalIdeal_smul_eq_zero (R := R) (M := M)
  have : Nontrivial G := IsSimpleModule.nontrivial R G
  obtain ⟨g, hg0⟩ := exists_ne (0 : G)
  -- the two "evaluation" maps `R → G`, `R → M`
  set φg : R →ₗ[R] G := LinearMap.toSpanSingleton R G g with hφg
  set φm : R →ₗ[R] M := LinearMap.toSpanSingleton R M m with hφm
  have hsurj : Function.Surjective φg := IsSimpleModule.toSpanSingleton_surjective R hg0
  have hkerg : LinearMap.ker φg = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (IsSimpleModule.ker_toSpanSingleton_isMaximal R hg0)
  have hkerm : LinearMap.ker φm = IsLocalRing.maximalIdeal R := by
    symm
    apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
    · intro htop
      have h1 : (1 : R) ∈ LinearMap.ker φm := by rw [htop]; trivial
      rw [LinearMap.mem_ker, hφm, LinearMap.toSpanSingleton_apply, one_smul] at h1
      exact hm0 h1
    · intro a ha
      rw [LinearMap.mem_ker, hφm, LinearMap.toSpanSingleton_apply]
      exact hmkill a ha
  have hker : LinearMap.ker φg = LinearMap.ker φm := hkerg.trans hkerm.symm
  let e : (R ⧸ LinearMap.ker φg) ≃ₗ[R] G := LinearMap.quotKerEquivOfSurjective φg hsurj
  let ψ : (R ⧸ LinearMap.ker φg) →ₗ[R] M := (LinearMap.ker φg).liftQ φm (le_of_eq hker)
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ φm hker
  exact ⟨ψ ∘ₗ e.symm.toLinearMap, hψ.comp e.symm.injective⟩

end MiyaokaMori.CoherentDevissage

end
