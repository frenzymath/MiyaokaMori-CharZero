import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrames
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFrames

/-! # A trivialization gives a basis of the sections of the dual

A trivialization `M|_U ≅ O_U^{(I)}` (`I` finite) gives a `Γ(U)`-basis of `Γ(U, M^∨)` indexed by `I`
(the dual basis). Sources: `Γ(U, M^∨) = Hom_{O_U}(M|_U, O_U)` (definition of `Modules.dual` =
`moduleSheafDual`, sections are local functionals), `Hom(O_U^{(I)}, O_U) = Γ(U)^I` for finite `I`
(Stacks 01AJ / Hartshorne II Ex. 5.1(a): the dual of a free module of finite rank is free on the dual basis).
Used for the local description of the weighted symmetric algebra as a weighted polynomial ring
(§2.2 of the paper); proved from the frame / dual-frame machinery of `FiniteFrames` and `DualFrames`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

/-- **Dual basis of a trivialized module.** If `e : M|_U ≅ O_U^{(I)}` with `I` finite, then the
`Γ(X, U)`-module `Γ(U, M^∨)` has a basis indexed by `I` (the dual basis).

Proof (as formalized):
1. **Frame from the trivialization.** Let `g' := e⁻¹ ∘ (restrictFunctorIsoPullback U.ι)⁻¹ :
   O_U^{(I)} ≅ M.restrict U.ι`. Its global sections `s i := freeHomEquiv g'.hom i` (images of the basis
   sections `e_i`), read on `⊤` and restricted along `U = U.ι ''ᵁ ⊤`, give `v : I → Γ(M, U)`.
   `frameHom M U v = g'.hom` (check both sides under `freeHomEquiv`, open by open), so `frameHom` is an
   isomorphism and `IsFrameOn M v` (`MiyaokaMori.DualPullback.isFrameOn_of_isIso_frameHom`): on every
   `W ≤ U`, `Γ(M, W) = ⨁_i Γ(X, W) · v_i|_W`. This is the argument of
   `MiyaokaMori.DualPullback.exists_frame`, run for the given `U`, `I`, `e` instead of a chosen chart.
2. **Sections of the dual are compatible families of functionals.** `Modules.dual M = moduleSheafDual M`
   is the sheafification of the presheaf `U ↦ LocalDualSections X M U` (families of `O`-linear
   functionals `Γ(M, V) → Γ(X, V)`, `V ≤ U`, compatible with restriction), which is already a sheaf,
   so `MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U : LocalDualSections X M U ≃ₗ[Γ(X,U)] Γ(M^∨, U)`.
3. **Dual coordinates.** In the frame `v`, a compatible family `φ` is determined by the values
   `φ_U(v_i) ∈ Γ(X, U)`, and every tuple occurs:
   `MiyaokaMori.DualPullback.dualCoordLinearEquiv hv le_rfl : LocalDualSections X M U ≃ₗ[Γ(X,U)] (I → Γ(X,U))`.
4. Compose the two linear isomorphisms and transport the standard basis `Pi.basisFun` along the inverse
   (`Module.Basis.map`).

Edge cases: `I` empty (both sides zero, basis indexed by the empty type); `U = ⊥` (zero ring, everything
zero) — no special treatment needed, the equivalences are unconditional. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_basis_dual_sections_of_pullback_iso_free
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (U : X.Opens) (I : Type u) [Finite I]
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :
    Nonempty (Module.Basis I Γ(X, U) Γ(AlgebraicGeometry.Scheme.Modules.dual M, U)) := by
  cases nonempty_fintype I
  -- Step 1: the trivialization gives a finite frame `v : I → Γ(M, U)` (`IsFrameOn`), exactly as in
  -- `MiyaokaMori.DualPullback.exists_frame`: `v i` is the image of the `i`-th basis section under
  -- `e.inv`, read as a section of `M` over `U`.
  let g' : MiyaokaMori.FreeStalk.freeM U.toScheme I ≅ M.restrict U.ι :=
    e.symm ≪≫ ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm
  let s : I → (M.restrict U.ι).sections := (M.restrict U.ι).freeHomEquiv g'.hom
  let v : I → Γ(M, U) := fun i =>
    AlgebraicGeometry.Scheme.Modules.res M (le_of_eq U.ι_image_top.symm)
      ((s i).val (op ⊤) : Γ(M, U.ι ''ᵁ ⊤))
  have hfr : MiyaokaMori.DualPullback.frameHom M U v = g'.hom := by
    apply (M.restrict U.ι).freeHomEquiv.injective
    rw [MiyaokaMori.DualPullback.freeHomEquiv_frameHom]
    funext i
    apply PresheafOfModules.sections_ext
    rintro ⟨W⟩
    rw [MiyaokaMori.DualPullback.frameSection_val]
    have h1 := AlgebraicGeometry.Scheme.Modules.res_res M (U.ι_image_le W)
      (le_of_eq U.ι_image_top.symm) ((s i).val (op ⊤))
    refine h1.trans ?_
    have := PresheafOfModules.sections_property (s i)
      ((homOfLE (le_top : W ≤ ⊤)).op : op (⊤ : U.toScheme.Opens) ⟶ op W)
    rw [← this]
    rfl
  have : IsIso (MiyaokaMori.DualPullback.frameHom M U v) := by rw [hfr]; infer_instance
  have hv : MiyaokaMori.DualPullback.IsFrameOn M v :=
    MiyaokaMori.DualPullback.isFrameOn_of_isIso_frameHom M U v
  -- Step 2: `Γ(U, M^∨) ≃ₗ LocalDualSections X M U ≃ₗ (I → Γ(X, U))` (dual coordinates in the frame).
  let L : Γ(AlgebraicGeometry.Scheme.Modules.dual M, U) ≃ₗ[Γ(X, U)] (I → Γ(X, U)) :=
    (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm.trans
      (MiyaokaMori.DualPullback.dualCoordLinearEquiv hv le_rfl)
  -- Step 3: transport the standard basis.
  exact ⟨(Pi.basisFun Γ(X, U) I).map L.symm⟩

end
