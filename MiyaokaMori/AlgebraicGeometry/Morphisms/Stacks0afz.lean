import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.ModuleDetFiniteFreeResolution
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00o7
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # The Picard group of a localization of a regular local ring is trivial

Stacks Project, Tag 0AFZ: for a regular local ring `R` and `f ∈ R`, `Pic(R_f)` is trivial
(used in the proof of Stacks 0AG0: `p_x = (y)`).

**Route.** Let `L` be an invertible `R_f`-module.
1. `L` is a finite `R_f`-module; the `R`-span `M ⊆ L` of a finite generating set is a finite
   `R`-module and `M → L` is a localization map at `S = ⟨f⟩` (`exists_finite_isLocalizedModule_of_finite`
   below, Mathlib only).
2. `R` regular local ⇒ `M` has a finite free resolution `0 → F_d → ⋯ → F_0 → M → 0`
   (Stacks 00O7, `IsRegularLocalRing.exists_finite_free_resolution` with `e = 0`).
3. `R → R_f` is flat, so `R_f ⊗_R -` keeps the resolution exact and `R_f ⊗_R M ≅ L`
   (`IsLocalizedModule.isBaseChange`); this gives a finite free `R_f`-resolution of `L`.
4. `Module.Invertible.free_of_finite_free_resolution` (the determinant argument of Stacks 0AFX/0AFY/0FJB) then says `L` is free.
5. `CommRing.Pic.subsingleton_iff`: every invertible module free ⇒ `Pic` trivial.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-- **Finite modules over a localization descend** (the `I = 0`, finite case of Stacks 05N5, proved
directly from Mathlib). Let `A` be a localization of `R` at `S` and `L` a finite `A`-module.
Then there is a finite `R`-module `M` together with an `R`-linear localization map `M → L` at `S`.

Proof: pick a finite `A`-generating set `s ⊆ L` and let `M := span_R s ⊆ L`, a finite `R`-module.
Since every `s ∈ S` acts invertibly on the `A`-module `L`, `id : L → L` is a localization map at `S`
(`isLocalizedModule_id`), so the inclusion of `M` into its `A`-span `M.localized' = span_A s = ⊤ = L`
is a localization map (`Submodule.toLocalized'`, `Submodule.localized'_span`). -/
theorem IsLocalization.exists_finite_isLocalizedModule_of_finite
    {R : Type u} [CommRing R] (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A]
    [IsLocalization S A] (L : Type u) [AddCommGroup L] [Module R L] [Module A L]
    [IsScalarTower R A L] [Module.Finite A L] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M) (g : M →ₗ[R] L),
      Module.Finite R M ∧ IsLocalizedModule S g := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := L)
  have := isLocalizedModule_id S L A
  let M' : Submodule R L := Submodule.span R (s : Set L)
  have htop : M'.localized' A S (LinearMap.id : L →ₗ[R] L) = ⊤ := by
    rw [Submodule.localized'_span, LinearMap.id_coe, Set.image_id]; exact hs
  exact ⟨M', inferInstance, inferInstance,
    ((LinearEquiv.ofTop _ htop).restrictScalars R).toLinearMap ∘ₗ M'.toLocalized' A S LinearMap.id,
    Module.Finite.span_of_finite R s.finite_toSet, inferInstance⟩

/-- **Base change of a finite free resolution along a flat algebra kills an invertible module**
(Stacks 0AFZ, the core step). Let `A` be a flat `R`-algebra, `L` an invertible `A`-module with
`A ⊗_R M ≅ L`, and `P` a projective resolution of `M` by finite free `R`-modules with `P_i = 0`
for `i > n`. Then `L` is a free `A`-module.

Proof: `C := A ⊗_R P` (built with `ChainComplex.of` from the base-changed differentials) is a chain
complex of finite free `A`-modules (`Basis.baseChange`, `Module.Finite.base_change`), zero above `n`,
exact in positive degrees because `A` is flat (`Module.Flat.lTensor_exact` applied to
`P.exact_succ`), and `A ⊗_R P_0 → A ⊗_R M ≅ L` is surjective with kernel `im(A ⊗ d_1)`
(flatness again, applied to `P.exact₀`). `Module.Invertible.free_of_finite_free_resolution`
(the determinant argument of Stacks 0AFX/0AFY/0FJB) then gives `L` free. -/
theorem Module.Invertible.free_of_flat_baseChange_finite_free_resolution
    {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
    (L : Type u) [AddCommGroup L] [Module A L] [Module.Invertible A L]
    (M : Type u) [AddCommGroup M] [Module R M]
    (e : A ⊗[R] M ≃ₗ[A] L)
    (P : ProjectiveResolution (ModuleCat.of R M)) (n : ℕ)
    (hfree : ∀ i, Module.Free R (P.complex.X i)) (hfin : ∀ i, Module.Finite R (P.complex.X i))
    (hzero : ∀ i, n < i → IsZero (P.complex.X i)) : Module.Free A L := by
  classical
  -- the base-changed complex `A ⊗[R] P`
  let X : ℕ → ModuleCat.{u} A := fun i => ModuleCat.of A (A ⊗[R] P.complex.X i)
  let d : ∀ i, X (i + 1) ⟶ X i := fun i =>
    ModuleCat.ofHom ((P.complex.d (i + 1) i).hom.baseChange A)
  have sq : ∀ i, d (i + 1) ≫ d i = 0 := by
    intro i
    ext : 1
    simp only [d, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    rw [← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, P.complex.d_comp_d,
      ModuleCat.hom_zero, LinearMap.baseChange_zero]
  let C : ChainComplex (ModuleCat.{u} A) ℕ := ChainComplex.of X d sq
  have hfreeC : ∀ i, Module.Free A (C.X i) := fun i => by
    have := hfree i
    exact Module.Free.of_basis ((Module.Free.chooseBasis R (P.complex.X i)).baseChange A)
  have hfinC : ∀ i, Module.Finite A (C.X i) := fun i => by
    have := hfin i
    show Module.Finite A (A ⊗[R] P.complex.X i)
    infer_instance
  have hbd : ∀ i, n < i → Subsingleton (C.X i) := fun i hi => by
    have hz : Subsingleton (P.complex.X i) := ModuleCat.isZero_iff_subsingleton.1 (hzero i hi)
    show Subsingleton (A ⊗[R] P.complex.X i)
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ z : A ⊗[R] P.complex.X i, z = 0 := fun z =>
      TensorProduct.induction_on z rfl
        (fun a m => by rw [Subsingleton.elim m 0, TensorProduct.tmul_zero])
        (fun x y hx hy => by rw [hx, hy, add_zero])
    rw [h0 x, h0 y]
  -- exactness over `R`, transported along the flat base change
  have hexR : ∀ i, Function.Exact (P.complex.d (i + 1 + 1) (i + 1)).hom (P.complex.d (i + 1) i).hom :=
    fun i => LinearMap.exact_iff.mpr (P.exact_succ i).moduleCat_range_eq_ker.symm
  have hexA : ∀ i, Function.Exact ((P.complex.d (i + 1 + 1) (i + 1)).hom.baseChange A)
      ((P.complex.d (i + 1) i).hom.baseChange A) := fun i => by
    have := Module.Flat.lTensor_exact A (hexR i)
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at this
  have hexC : ∀ i, C.ExactAt (i + 1) := fun i => by
    rw [HomologicalComplex.exactAt_iff' C (i + 1 + 1) (i + 1) i (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
      HomologicalComplex.shortComplexFunctor'_obj_g, C, ChainComplex.of_d, d]
    exact (LinearMap.exact_iff.mp (hexA i)).symm
  -- the augmentation `A ⊗[R] P₀ → A ⊗[R] M ≃ L`
  let q : P.complex.X 0 →ₗ[R] M := (P.π.f 0).hom
  have hq : Function.Surjective q := (ModuleCat.epi_iff_surjective (P.π.f 0)).1 inferInstance
  have hexq : Function.Exact (P.complex.d 1 0).hom q :=
    LinearMap.exact_iff.mpr P.exact₀.moduleCat_range_eq_ker.symm
  have hexqA : Function.Exact ((P.complex.d 1 0).hom.baseChange A) (q.baseChange A) := by
    have := Module.Flat.lTensor_exact A hexq
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at this
  let ε : C.X 0 →ₗ[A] L := e.toLinearMap ∘ₗ q.baseChange A
  have hε : Function.Surjective ε := by
    refine e.surjective.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective A hq
  have hker : LinearMap.ker ε = LinearMap.range (C.d 1 0).hom := by
    have h10 : C.d 1 0 = d 0 := ChainComplex.of_d X d 0
    rw [h10]
    simp only [ε, d, ModuleCat.hom_ofHom, LinearEquiv.ker_comp]
    exact LinearMap.exact_iff.mp hexqA
  exact Module.Invertible.free_of_finite_free_resolution L C n hfreeC hfinC hbd hexC ε hε hker

/-- **Stacks 0AFZ**: for a regular local ring `R` and `f ∈ R`, `Pic(R_f)` is trivial.
See the module docstring for the route. Inputs outside Mathlib: Stacks 00O7
(`IsRegularLocalRing.exists_finite_free_resolution`, finite free resolutions over a regular local
ring) and `Module.Invertible.free_of_finite_free_resolution`. -/
theorem IsRegularLocalRing.pic_localizationAway_subsingleton (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (f : R) : Subsingleton (CommRing.Pic (Localization.Away f)) := by
  classical
  rw [CommRing.Pic.subsingleton_iff]
  intro L _ _ hL
  let _ : Module R L := Module.compHom L (algebraMap R (Localization.Away f))
  have : IsScalarTower R (Localization.Away f) L :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- Step 1: descend `L` to a finite `R`-module `M`.
  obtain ⟨M, _, _, g, hMfin, hg⟩ :=
    IsLocalization.exists_finite_isLocalizedModule_of_finite (Submonoid.powers f)
      (Localization.Away f) L
  -- Step 2: finite free resolution of `M` over the regular local ring `R`.
  obtain ⟨P, hP, hPzero⟩ := IsRegularLocalRing.exists_finite_free_resolution M
    (IsLocalRing.maximalIdeal R).spanFinrank 0 IsRegularLocalRing.spanFinrank_maximalIdeal.symm
    ⟨[], rfl, by simp, RingTheory.Sequence.IsWeaklyRegular.nil R M⟩
  -- Steps 3–4: base change along the flat map `R → R_f` and take determinants.
  exact Module.Invertible.free_of_flat_baseChange_finite_free_resolution (Localization.Away f) L M
    (IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f) g).equiv P
    ((IsLocalRing.maximalIdeal R).spanFinrank - 0) (fun i => (hP i).2) (fun i => (hP i).1) hPzero

end
