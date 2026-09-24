import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearLongExact
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyZeroEquiv
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyShift

/-! # Two-out-of-three for finiteness of sheaf cohomology

Two-out-of-three for finiteness of sheaf cohomology over a Noetherian ring (step (1) of the
dévissage in the proof of Stacks 02O5 / 02O6): X an R-scheme, R Noetherian, 0 → M₁ → M₂ → M₃ → 0 a
short exact sequence of O_X-modules. If for two of the three modules every H^i is a finite R-module,
then so it is for the third. Also: the cohomology of a zero module is finite.

Source: Stacks 02O5 (proof, step (1) of the dévissage); Hartshorne III.8.8 argument; the R-linear long
exact sequence is in `SheafCohomologyLinearLongExact.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Pure algebra: over a Noetherian ring, the middle term of an exact sequence `M₁ → M₂ → M₃`
(`range f = ker g`) with `M₁`, `M₃` finite is finite. Proof: `ker g = range f` is finitely generated
(image of a finite module), `range g ⊆ M₃` is finitely generated (submodule of a Noetherian module),
and `Submodule.fg_of_fg_map_of_fg_inf_ker`. -/
theorem Module.Finite.of_range_eq_ker_of_isNoetherianRing {R M₁ M₂ M₃ : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (h : LinearMap.range f = LinearMap.ker g) [Module.Finite R M₁] [Module.Finite R M₃] :
    Module.Finite R M₂ := by
  have hker : (LinearMap.ker g).FG := by
    rw [← h, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map f
  have hrange : (LinearMap.range g).FG := IsNoetherian.noetherian _
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rwa [← LinearMap.range_eq_map]
  · rwa [top_inf_eq]

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A mono of `O_X`-modules is injective on `H^0 = Γ(-, ⊤)`: `H^0 = Γ(-, ⊤)` naturally
(`sheafCohomologyZeroEquiv_naturality`), `SheafOfModules.forget` preserves monos, and a mono of
presheaves of modules is injective on sections (`PresheafOfModules.injective_of_mono`). -/
theorem sheafCohomology.map_zero_injective_of_mono {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective (sheafCohomology.map f 0) := by
  intro x y hxy
  have hm : Mono (C := SheafOfModules.{u} X.ringCatSheaf) f := ‹Mono f›
  have : Mono f.val := (SheafOfModules.forget.{u} X.ringCatSheaf).map_mono f
  apply (sheafCohomologyZeroEquiv M).injective
  apply PresheafOfModules.injective_of_mono f.val (op ⊤)
  have := congrArg (sheafCohomologyZeroEquiv N) hxy
  rwa [sheafCohomologyZeroEquiv_naturality, sheafCohomologyZeroEquiv_naturality] at this

/-- The cohomology of a zero module is a subsingleton in every degree: in degree `n + 1` because a
zero object is injective (`IsZero.injective`) and injectives have no higher cohomology
(`sheafCohomology.subsingleton_of_injective`); in degree `0` because `H^0(X, F) ≃ Γ(F, ⊤)`
(`sheafCohomologyZeroEquiv`) and every global section `s` satisfies
`s = (𝟙 F).app ⊤ s = (0 : F ⟶ F).app ⊤ s = 0`. -/
theorem sheafCohomology.subsingleton_of_isZero (F : X.Modules) (hF : IsZero F) (n : ℕ) :
    Subsingleton (sheafCohomology X F n) := by
  cases n with
  | zero =>
    refine (sheafCohomologyZeroEquiv F).toEquiv.subsingleton_congr.mpr ⟨fun s t => ?_⟩
    have h0 : (𝟙 F : F ⟶ F) = 0 := hF.eq_of_src _ _
    have hs : (𝟙 F : F ⟶ F).app ⊤ s = s := rfl
    have ht : (𝟙 F : F ⟶ F).app ⊤ t = t := rfl
    rw [← hs, ← ht, h0]
    simp
  | succ p =>
    have : Injective F := hF.injective
    exact sheafCohomology.subsingleton_of_injective F p

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  [X.Over (Spec (CommRingCat.of R))]

omit [IsNoetherianRing R] in
/-- The cohomology of a zero module is a finite `R`-module in every degree: it is a subsingleton
(`sheafCohomology.subsingleton_of_isZero`), and a subsingleton module is finite. -/
theorem sheafCohomology.finite_of_isZero (F : X.Modules) (hF : IsZero F) (n : ℕ) :
    Module.Finite R (sheafCohomology X F n) := by
  have := sheafCohomology.subsingleton_of_isZero F hF n
  infer_instance

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS in
/-- P(M₁), P(M₂) ⇒ P(M₃).
Proof: the `R`-linear long exact sequence gives `range (H^i(g)) = ker δ` with
`δ : H^i(M₃) → H^{i+1}(M₁)` (`sheafCohomology.range_mapOver_g_eq_ker_δOver`), so
`H^i(M₂) → H^i(M₃) → H^{i+1}(M₁)` is exact with finite ends; apply
`Module.Finite.of_range_eq_ker_of_isNoetherianRing`. -/
theorem sheafCohomology.finite_X₃_of_finite_X₁_X₂
    (h₁ : ∀ i, Module.Finite R (sheafCohomology X S.X₁ i))
    (h₂ : ∀ i, Module.Finite R (sheafCohomology X S.X₂ i)) (i : ℕ) :
    Module.Finite R (sheafCohomology X S.X₃ i) :=
  have := h₂ i
  have := h₁ (i + 1)
  Module.Finite.of_range_eq_ker_of_isNoetherianRing (sheafCohomology.mapOver R S.g i)
    (sheafCohomology.δOver hS i (i + 1) rfl R)
    (sheafCohomology.range_mapOver_g_eq_ker_δOver hS i (i + 1) rfl R)

include hS in
/-- P(M₁), P(M₃) ⇒ P(M₂).
Proof: `H^i(M₁) → H^i(M₂) → H^i(M₃)` is exact (`sheafCohomology.range_mapOver_f_eq_ker_mapOver_g`)
with finite ends; apply `Module.Finite.of_range_eq_ker_of_isNoetherianRing`. -/
theorem sheafCohomology.finite_X₂_of_finite_X₁_X₃
    (h₁ : ∀ i, Module.Finite R (sheafCohomology X S.X₁ i))
    (h₃ : ∀ i, Module.Finite R (sheafCohomology X S.X₃ i)) (i : ℕ) :
    Module.Finite R (sheafCohomology X S.X₂ i) :=
  have := h₁ i
  have := h₃ i
  Module.Finite.of_range_eq_ker_of_isNoetherianRing (sheafCohomology.mapOver R S.f i)
    (sheafCohomology.mapOver R S.g i)
    (sheafCohomology.range_mapOver_f_eq_ker_mapOver_g hS R i)

include hS in
/-- P(M₂), P(M₃) ⇒ P(M₁).
Proof: for `i = n + 1`, `H^n(M₃) → H^{n+1}(M₁) → H^{n+1}(M₂)` is exact
(`sheafCohomology.range_δOver_eq_ker_mapOver_f`) with finite ends. For `i = 0`,
`H^0(M₁) → H^0(M₂)` is injective (`sheafCohomology.map_zero_injective_of_mono`, using `hS.mono_f`);
a submodule of a finite module over a Noetherian ring is finite (`Module.Finite.of_injective`). -/
theorem sheafCohomology.finite_X₁_of_finite_X₂_X₃
    (h₂ : ∀ i, Module.Finite R (sheafCohomology X S.X₂ i))
    (h₃ : ∀ i, Module.Finite R (sheafCohomology X S.X₃ i)) (i : ℕ) :
    Module.Finite R (sheafCohomology X S.X₁ i) := by
  cases i with
  | zero =>
    have := h₂ 0
    have : Mono S.f := hS.mono_f
    exact Module.Finite.of_injective (sheafCohomology.mapOver R S.f 0)
      (sheafCohomology.map_zero_injective_of_mono S.f)
  | succ n =>
    have := h₃ n
    have := h₂ (n + 1)
    exact Module.Finite.of_range_eq_ker_of_isNoetherianRing (sheafCohomology.δOver hS n (n + 1) rfl R)
      (sheafCohomology.mapOver R S.f (n + 1))
      (sheafCohomology.range_δOver_eq_ker_mapOver_f hS n (n + 1) rfl R)

end AlgebraicGeometry

end
