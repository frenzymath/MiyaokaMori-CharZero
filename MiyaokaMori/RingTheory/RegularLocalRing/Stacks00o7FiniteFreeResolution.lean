import MiyaokaMori.Prelude
import Mathlib.RingTheory.Regular.ProjectiveDimension

/-! # Finite free resolutions from bounded projective dimension (Stacks 00O7)

Over a Noetherian local ring `R`, a finite module `M` with `pd M ≤ n` has a projective resolution
`P` all of whose terms are finite free and with `P.X i = 0` for `i > n`
(`ModuleCat.exists_projectiveResolution_finite_free_of_hasProjectiveDimensionLE`).

Source: this is the standard "syzygy" construction (Stacks 00O5, algebra-lemma-independent-resolution:
if `pd M ≤ n` then in any resolution by finite free modules the `n`-th syzygy is projective; Stacks 00NX
/ Mathlib `Module.free_of_flat_of_isLocalRing`: finite projective over a local ring is free).

Construction. For a finite module `K` pick a *cover* `F → K`: `F` finite free, surjective, and chosen
to be the identity when `K` is projective (then `K` is itself finite free). Iterate on kernels
(finite, since `R` is Noetherian): `K₀ = M`, `K_{i+1} = ker (F_i → K_i)`, `F_i = cover K_i`.
The complex `⋯ → F_{i+1} → K_{i+1} ↪ F_i → ⋯ → F_0` is exact in degrees `≥ 1` and has `H_0 = M`
(elementwise), so it is a projective resolution of `M` (`ProjectiveResolution` with `π` induced by
`F_0 → M`, exactly as Mathlib builds `ProjectiveResolution.of`). If `pd M ≤ n`, dimension shifting
along `0 → K_{i+1} → F_i → K_i → 0` gives `pd K_n ≤ 0`, i.e. `K_n` projective; then `F_n = K_n`,
`K_{n+1} = 0`, and all later `K_i`, `F_i` are zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Abelian

noncomputable section

namespace ModuleCat.FiniteFreeResolution

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A finite free cover of `K`: `F` finite free, `π : F → K` surjective, and `π` injective when `K`
is projective (the cover is then `K` itself). -/
structure Cover (K : ModuleCat.{u} R) where
  F : ModuleCat.{u} R
  π : F ⟶ K
  surj : Function.Surjective π.hom
  finite : Module.Finite R F
  free : Module.Free R F
  inj_of_projective : Projective K → Function.Injective π.hom

attribute [instance] Cover.finite Cover.free

omit [IsNoetherianRing R] in
theorem exists_cover (K : ModuleCat.{u} R) [Module.Finite R K] : Nonempty (Cover K) := by
  by_cases hK : Projective K
  · have hproj : Module.Projective R K := (IsProjective.iff_projective (R := R) K).mpr hK
    have hfree : Module.Free R K := Module.free_of_flat_of_isLocalRing
    exact ⟨⟨K, 𝟙 K, Function.surjective_id, inferInstance, hfree, fun _ => Function.injective_id⟩⟩
  · obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R K
    exact ⟨⟨ModuleCat.of R (Fin m → R), ModuleCat.ofHom f, hf, inferInstance, inferInstance,
      fun h => absurd h hK⟩⟩

/-- A chosen cover. -/
def cover (K : ModuleCat.{u} R) [Module.Finite R K] : Cover K := Classical.choice (exists_cover K)

/-- A finite module, packaged with its finiteness. -/
structure FinMod (R : Type u) [CommRing R] where
  K : ModuleCat.{u} R
  fin : Module.Finite R K

attribute [instance] FinMod.fin

/-- The kernel of the chosen cover, as a finite module. -/
def FinMod.next (A : FinMod R) : FinMod R :=
  ⟨ModuleCat.of R (LinearMap.ker (cover A.K).π.hom), inferInstance⟩

/-- The iterated syzygies `K₀ = M`, `K_{i+1} = ker (cover K_i → K_i)`. -/
def syz (M : FinMod R) : ℕ → FinMod R
  | 0 => M
  | i + 1 => (syz M i).next

variable (M : FinMod R)

/-- The terms of the resolution: `F_i = cover K_i`. -/
def X (i : ℕ) : ModuleCat.{u} R := (cover (syz M i).K).F

instance (i : ℕ) : Module.Finite R (X M i) := (cover (syz M i).K).finite
instance (i : ℕ) : Module.Free R (X M i) := (cover (syz M i).K).free
instance (i : ℕ) : Projective (X M i) :=
  ModuleCat.projective_of_free (M := X M i) (Module.Free.chooseBasis R (X M i))

/-- The cover map `F_i → K_i`. -/
def π (i : ℕ) : X M i ⟶ (syz M i).K := (cover (syz M i).K).π

/-- The inclusion `K_{i+1} = ker (F_i → K_i) ↪ F_i`. -/
def ι (i : ℕ) : (syz M (i + 1)).K ⟶ X M i :=
  ModuleCat.ofHom (LinearMap.ker (cover (syz M i).K).π.hom).subtype

/-- The differential `F_{i+1} → K_{i+1} ↪ F_i`. -/
def d (i : ℕ) : X M (i + 1) ⟶ X M i := π M (i + 1) ≫ ι M i

theorem ι_π (i : ℕ) : ι M i ≫ π M i = 0 := by
  ext ⟨v, hv⟩
  exact hv

theorem d_d (i : ℕ) : d M (i + 1) ≫ d M i = 0 := by
  simp only [d, Category.assoc]
  rw [← Category.assoc (ι M (i + 1)), ι_π, zero_comp, comp_zero]

theorem π_surjective (i : ℕ) : Function.Surjective (π M i).hom := (cover (syz M i).K).surj

theorem ι_injective (i : ℕ) : Function.Injective (ι M i).hom := Subtype.val_injective

/-- Exactness of `F_{i+1} → F_i → K_i` (the kernel of `π_i` is hit by `d_i`). -/
theorem exact_d_π (i : ℕ) : (ShortComplex.mk (d M i) (π M i)
    (by rw [d, Category.assoc, ι_π, comp_zero])).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  obtain ⟨w, hw⟩ := π_surjective M (i + 1) (⟨y, hy⟩ : LinearMap.ker (cover (syz M i).K).π.hom)
  refine ⟨w, ?_⟩
  show (ι M i).hom ((π M (i + 1)).hom w) = y
  rw [hw]
  rfl

/-- The chain complex `⋯ → F_2 → F_1 → F_0`. -/
def complex : ChainComplex (ModuleCat.{u} R) ℕ := ChainComplex.of (X M) (d M) (d_d M)

theorem complex_X (i : ℕ) : (complex M).X i = X M i := rfl

theorem complex_d (i : ℕ) : (complex M).d (i + 1) i = d M i := ChainComplex.of_d _ _ i

/-- Exactness in degrees `≥ 1`. -/
theorem complex_exactAt_succ (i : ℕ) : (complex M).ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 1 + 1) (i + 1) i (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', complex,
    ChainComplex.of_d]
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  -- `hy : (d M i) y = 0`, i.e. `ι_i (π_{i+1} y) = 0`, so `π_{i+1} y = 0`
  have h1 : (π M (i + 1)).hom y = 0 := by
    apply ι_injective M i
    rw [map_zero]
    exact hy
  obtain ⟨w, hw⟩ := π_surjective M (i + 2)
    (⟨y, h1⟩ : LinearMap.ker (cover (syz M (i + 1)).K).π.hom)
  refine ⟨w, ?_⟩
  show (ι M (i + 1)).hom ((π M (i + 2)).hom w) = y
  rw [hw]
  rfl

/-- The augmentation `F_0 → M`, typed as a map out of `(complex M).X 0`. -/
def π₀ : (complex M).X 0 ⟶ M.K := π M 0

theorem d_zero_comp_π₀ : (complex M).d 1 0 ≫ π₀ M = 0 := by
  change d M 0 ≫ π M 0 = 0
  rw [d, Category.assoc, ι_π, comp_zero]

/-- The projective resolution of `M.K` by the finite free modules `F_i`. -/
def resolution : ProjectiveResolution M.K where
  complex := complex M
  projective n := inferInstanceAs (Projective (X M n))
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨π₀ M, d_zero_comp_π₀ M⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨exact_d_π M 0, (ModuleCat.epi_iff_surjective _).mpr (π_surjective M 0)⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp (d M 0)).trans (Category.comp_id (d M 0)).symm)
          ((Category.id_comp (π M 0)).trans (Category.comp_id (π₀ M)).symm)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · apply complex_exactAt_succ
      · apply ChainComplex.exactAt_succ_single_obj⟩

theorem resolution_complex_X (i : ℕ) : (resolution M).complex.X i = X M i := rfl

/-! ### Vanishing beyond the projective dimension -/

/-- Dimension shift along `0 → K_{i+1} → F_i → K_i → 0`. -/
theorem hasProjectiveDimensionLT_syz_succ (i k : ℕ)
    (h : HasProjectiveDimensionLT (syz M i).K (k + 2)) :
    HasProjectiveDimensionLT (syz M (i + 1)).K (k + 1) := by
  have hS := LinearMap.shortExact_shortComplexKer (π_surjective M i)
  have hproj : Projective (ModuleCat.of R (X M i)) := inferInstanceAs (Projective (X M i))
  exact (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp h

theorem hasProjectiveDimensionLT_syz (n : ℕ) (h : HasProjectiveDimensionLE M.K n) :
    ∀ i, i ≤ n → HasProjectiveDimensionLT (syz M i).K (n + 1 - i) := by
  intro i
  induction i with
  | zero =>
    intro _
    show HasProjectiveDimensionLT M.K (n + 1 - 0)
    rw [Nat.sub_zero]
    exact h
  | succ i ih =>
    intro hi
    have := hasProjectiveDimensionLT_syz_succ M i (n - (i + 1)) (by
      have := ih (by omega)
      have e : n + 1 - i = n - (i + 1) + 2 := by omega
      rwa [e] at this)
    have e : n + 1 - (i + 1) = n - (i + 1) + 1 := by omega
    rwa [e]

theorem isZero_syz_succ_of_projective (i : ℕ) (h : Projective (syz M i).K) :
    IsZero (syz M (i + 1)).K := by
  have hinj := (cover (syz M i).K).inj_of_projective h
  have : Subsingleton (syz M (i + 1)).K :=
    Subsingleton.intro fun a b => Subtype.ext (hinj (a.2.trans b.2.symm))
  exact ModuleCat.isZero_of_subsingleton _

theorem isZero_X_of_isZero (i : ℕ) (h : IsZero (syz M i).K) : IsZero (X M i) := by
  have hp : Projective (syz M i).K := h.projective
  have hinj := (cover (syz M i).K).inj_of_projective hp
  have : Subsingleton (syz M i).K := ModuleCat.isZero_iff_subsingleton.mp h
  have : Subsingleton (X M i) := hinj.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem isZero_syz_of_gt (n : ℕ) (h : HasProjectiveDimensionLE M.K n) :
    ∀ i, n < i → IsZero (syz M i).K := by
  intro i hi
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hin : n < i
    · exact isZero_syz_succ_of_projective M i (ih hin).projective
    · have hi' : i = n := by omega
      subst hi'
      have := hasProjectiveDimensionLT_syz M i h i le_rfl
      have e : i + 1 - i = 1 := by omega
      rw [e] at this
      exact isZero_syz_succ_of_projective M i inferInstance

/-- **Finite free resolution of bounded length.** Over a Noetherian local ring, a finite module `M`
with `pd M ≤ n` has a projective resolution by finite free modules with `P.X i = 0` for `i > n`. -/
theorem _root_.ModuleCat.exists_projectiveResolution_finite_free_of_hasProjectiveDimensionLE
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of R M) n) :
    ∃ P : ProjectiveResolution (ModuleCat.of R M),
      (∀ i, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) ∧
      ∀ i, n < i → IsZero (P.complex.X i) := by
  let A : FinMod R := ⟨ModuleCat.of R M, inferInstance⟩
  refine ⟨resolution A, fun i => ⟨inferInstanceAs (Module.Finite R (X A i)),
    inferInstanceAs (Module.Free R (X A i))⟩, fun i hi => ?_⟩
  exact isZero_X_of_isZero A i (isZero_syz_of_gt A n h i hi)

end ModuleCat.FiniteFreeResolution

end
