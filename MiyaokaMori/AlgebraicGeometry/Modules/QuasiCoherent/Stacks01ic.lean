import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesSectionsLimits
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ShortExactLocalOnOpenCover
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfAffineLocalizing

/-! # Kernels and cokernels of quasi-coherent sheaves are quasi-coherent (Stacks 01IC)

Source: Stacks 01IC (`schemes-lemma-kernel-cokernel-quasi-coherent`).

## Proof

Instead of the exactness of the stalk functor, use Mathlib's criterion "quasi-coherent on `Spec` ⟺
`IsIso fromTildeΓ` ⟺ `IsLocalizing`" (`isQuasicoherent_iff_isIso_fromTildeΓ`,
`isIso_fromTildeΓ_iff_isLocalizing`), with the same skeleton as `isQuasicoherent_colimit` (Stacks 01ID):

1. **Kernels on `Spec R`** (`isQuasicoherent_kernel_spec`). Let `K := ker φ`. To show `IsLocalizing K`: for
   every `f ∈ R`, the restriction `Γ(K, ⊤) → Γ(K, D(f))` is the localization at `f`. The section functor
   `Γ(-, U)` preserves finite limits (`ModulesSectionsOfLimits`), so `Γ(K, U) ⊆ Γ(M, U)` is exactly the
   kernel of `Γ(φ_U)` (`sections_kernel_ι_injective`, `sections_kernel_exists`), and since `M`, `N` are
   quasi-coherent, `Γ(M,⊤) → Γ(M,D(f))` and `Γ(N,⊤) → Γ(N,D(f))` are localizations. The pure algebra
   lemma `isLocalizedModule_of_kernel_ladder` ("localization commutes with kernels": the map between the
   kernels of two rows of localizations is again a localization; the three axioms of `IsLocalizedModule`
   are checked elementwise) concludes.
2. **Cokernels on `Spec R`** (`isQuasicoherent_cokernel_spec`). `φ ≅ ψ~` (`ψ = Γ(φ)`, the isomorphism from
   the naturality of `fromTildeΓ`); `tilde.functor` is a left adjoint and preserves cokernels
   (`PreservesCokernel.iso`), so `coker φ ≅ (coker ψ)~` is quasi-coherent.
3. **General schemes.** For an affine open `U`, restriction along the open immersion `hU.fromSpec`
   preserves finite limits (it is a right adjoint, `restrictFunctor_preservesFiniteLimits`) and colimits
   (a left adjoint), so `(ker φ)|_U = ker(φ|_U)` and `(coker φ)|_U = coker(φ|_U)`, quasi-coherent by 1 and
   2; `isQuasicoherent_over_of_isLocalizing` (`QuasicoherentOfAffineLocalizing`) gives that `M.over U` is
   quasi-coherent; affine opens cover `X`, and `IsQuasicoherent.of_coversTop` glues
   (`isQuasicoherent_of_restrict_affine`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks01icAux

/-- Elementwise form of "localization commutes with kernels". Let `ρA : A → A'`, `ρB : B → B'` be
localizations at `p`, `ι : K → A`, `ι' : K' → A'` injective and kernels of `ψ : A → B`, `ψ' : A' → B'`
respectively (`Function.Exact`), and `ρK : K → K'` commuting with both squares; then `ρK` is also a
localization at `p`. -/
theorem isLocalizedModule_of_kernel_ladder {R : Type u} [CommRing R] (p : Submonoid R)
    {K K' A A' B B' : Type v} [AddCommGroup K] [Module R K] [AddCommGroup K'] [Module R K']
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (ρK : K →ₗ[R] K') (ρA : A →ₗ[R] A') (hρA : IsLocalizedModule p ρA)
    (ρB : B →ₗ[R] B') (hρB : IsLocalizedModule p ρB)
    (ι : K →ₗ[R] A) (ι' : K' →ₗ[R] A') (ψ : A →ₗ[R] B) (ψ' : A' →ₗ[R] B')
    (hι : Function.Injective ι) (hι' : Function.Injective ι')
    (hex : Function.Exact ι ψ) (hex' : Function.Exact ι' ψ')
    (h1 : ∀ k, ρA (ι k) = ι' (ρK k)) (h2 : ∀ a, ρB (ψ a) = ψ' (ρA a)) :
    IsLocalizedModule p ρK := by
  have := hρA
  have := hρB
  have hA : ∀ s : p, Function.Injective (fun a : A' => (s : R) • a) := fun s =>
    IsLocalizedModule.smul_injective ρA s
  have hB : ∀ s : p, Function.Injective (fun b : B' => (s : R) • b) := fun s =>
    IsLocalizedModule.smul_injective ρB s
  refine ⟨fun s => ?_, fun k' => ?_, fun {k₁ k₂} h => ?_⟩
  · -- `s •` is bijective on `K'`
    rw [Module.End.isUnit_iff]
    constructor
    · intro k₁ k₂ h
      simp only [Module.algebraMap_end_apply] at h
      apply hι'
      apply hA s
      simp only [← map_smul, h]
    · intro k'
      obtain ⟨g, hg⟩ := (IsLocalizedModule.map_units ρA s).exists_right_inv
      set a' : A' := g (ι' k') with ha'
      have hsa' : (s : R) • a' = ι' k' := by
        have := congrArg (fun e : Module.End R A' => e (ι' k')) hg
        simpa [Module.algebraMap_end_apply, ha'] using this
      have hψ' : ψ' a' = 0 := by
        apply hB s
        simp only [← map_smul, hsa', smul_zero]
        exact hex'.apply_apply_eq_zero k'
      obtain ⟨k'', hk''⟩ := (hex' a').mp hψ'
      refine ⟨k'', hι' ?_⟩
      simp only [Module.algebraMap_end_apply, map_smul, hk'', hsa']
  · -- surjectivity up to `p`
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj p ρA (ι' k')
    simp only at hs
    have hψa : ρB (ψ a) = ρB 0 := by
      rw [h2, ← hs, map_zero, Submonoid.smul_def, map_smul, hex'.apply_apply_eq_zero, smul_zero]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := p) (f := ρB) hψa
    rw [smul_zero, Submonoid.smul_def, ← map_smul] at ht
    obtain ⟨k, hk⟩ := (hex ((t : R) • a)).mp ht
    refine ⟨⟨k, t * s⟩, hι' ?_⟩
    have e1 : ι' ((t * s) • k') = (t : R) • ((s : R) • ι' k') := by
      rw [Submonoid.smul_def, map_smul, Submonoid.coe_mul, mul_smul]
    have e2 : ι' (ρK k) = (t : R) • ((s : R) • ι' k') := by
      rw [← h1, hk, map_smul, ← hs]
      rfl
    exact e1.trans e2.symm
  · -- `exists_of_eq`
    have : ρA (ι k₁) = ρA (ι k₂) := by rw [h1, h1, h]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p) (f := ρA) this
    refine ⟨c, hι ?_⟩
    simpa only [Submonoid.smul_def, map_smul] using hc

end Stacks01icAux

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- If the restriction of `M` along `hU.fromSpec` is quasi-coherent for every affine open `U`, then `M` is
quasi-coherent (the final step of `isQuasicoherent_colimit`, extracted). -/
theorem isQuasicoherent_of_restrict_affine {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ U : X.affineOpens, (M.restrict U.2.fromSpec).IsQuasicoherent) : M.IsQuasicoherent := by
  have key : ∀ U : X.affineOpens, (M.over (U : X.Opens)).IsQuasicoherent := fun U => by
    have hiso : IsIso (M.restrict U.2.fromSpec).fromTildeΓ :=
      (isQuasicoherent_iff_isIso_fromTildeΓ _).mp (h U)
    exact QcOfAffineLocalizingAux.isQuasicoherent_over_of_isLocalizing M U.2
      ((isIso_fromTildeΓ_iff_isLocalizing _).mp hiso)
  refine SheafOfModules.IsQuasicoherent.of_coversTop M
    (fun U : X.affineOpens => (U : X.Opens)) ?_
  rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
  exact iSup_affineOpens_eq_top X

set_option backward.isDefEq.respectTransparency false in
/-- The case of `Spec` (kernels): the kernel of a morphism of quasi-coherent sheaves on `Spec R` is
quasi-coherent. -/
theorem isQuasicoherent_kernel_spec {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) : (kernel φ).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  have hM : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  have hN : IsLocalizing (modulesSpecToSheaf.obj N) :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance
  intro f
  let S := modulesSpecToSheaf (R := R)
  have hinj : ∀ U : (Spec R).Opens,
      Function.Injective (((S.map (kernel.ι φ)).1.app (op U)).hom) := fun U a b h =>
    sections_kernel_ι_injective φ U h
  have hexact : ∀ U : (Spec R).Opens,
      Function.Exact (((S.map (kernel.ι φ)).1.app (op U)).hom) (((S.map φ).1.app (op U)).hom) := by
    intro U x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := sections_kernel_exists φ U x hx
      exact ⟨s, hs⟩
    · rintro ⟨s, rfl⟩
      change φ.app U ((kernel.ι φ).app U s) = 0
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, kernel.condition]
      rfl
  refine Stacks01icAux.isLocalizedModule_of_kernel_ladder (Submonoid.powers f)
    _ _ (hM f) _ (hN f)
    ((S.map (kernel.ι φ)).1.app (op ⊤)).hom
    ((S.map (kernel.ι φ)).1.app (op (PrimeSpectrum.basicOpen f))).hom
    ((S.map φ).1.app (op ⊤)).hom ((S.map φ).1.app (op (PrimeSpectrum.basicOpen f))).hom
    (hinj ⊤) (hinj _) (hexact ⊤) (hexact _) ?_ ?_
  · intro k
    exact congr($((S.map (kernel.ι φ)).1.naturality (PrimeSpectrum.basicOpen f).leTop.op).hom k).symm
  · intro a
    exact congr($((S.map φ).1.naturality (PrimeSpectrum.basicOpen f).leTop.op).hom a).symm

set_option backward.isDefEq.respectTransparency false in
/-- The case of `Spec` (cokernels): the cokernel of a morphism of quasi-coherent sheaves on `Spec R` is
quasi-coherent. -/
theorem isQuasicoherent_cokernel_spec {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) : (cokernel φ).IsQuasicoherent := by
  let ψ : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N := moduleSpecΓFunctor.map φ
  have hM : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  have hN : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  have hsq : (tilde.functor R).map ψ ≫ N.fromTildeΓ = M.fromTildeΓ ≫ φ :=
    (fromTildeΓNatTrans (R := R)).naturality φ
  let e : cokernel ((tilde.functor R).map ψ) ≅ cokernel φ :=
    cokernel.mapIso _ _ (asIso M.fromTildeΓ) (asIso N.fromTildeΓ) hsq
  let e' : (tilde.functor R).obj (cokernel ψ) ≅ cokernel ((tilde.functor R).map ψ) :=
    PreservesCokernel.iso (tilde.functor R) ψ
  have ht : ((tilde.functor R).obj (cokernel ψ)).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso (e' ≪≫ e) ht

end AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Stacks 01IC: kernels and cokernels of morphisms of quasi-coherent `O_X`-modules are quasi-coherent.
See the module docstring (the `Spec` cases `isQuasicoherent_kernel_spec` / `isQuasicoherent_cokernel_spec`,
glued along affine opens by `isQuasicoherent_of_restrict_affine`). -/
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (CategoryTheory.Limits.kernel φ).IsQuasicoherent ∧ (CategoryTheory.Limits.cokernel φ).IsQuasicoherent := by
  constructor
  · refine isQuasicoherent_of_restrict_affine _ fun U => ?_
    have hU := U.2
    have hpres : PreservesFiniteLimits (restrictFunctor hU.fromSpec) :=
      restrictFunctor_preservesFiniteLimits _
    let i : (kernel φ).restrict hU.fromSpec ≅ kernel ((restrictFunctor hU.fromSpec).map φ) :=
      PreservesKernel.iso (restrictFunctor hU.fromSpec) φ
    have hk : (kernel ((restrictFunctor hU.fromSpec).map φ)).IsQuasicoherent :=
      isQuasicoherent_kernel_spec _
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso i.symm hk
  · refine isQuasicoherent_of_restrict_affine _ fun U => ?_
    have hU := U.2
    have hpres : PreservesColimitsOfSize.{u, u} (restrictFunctor hU.fromSpec) := inferInstance
    let i : (cokernel φ).restrict hU.fromSpec ≅ cokernel ((restrictFunctor hU.fromSpec).map φ) :=
      PreservesCokernel.iso (restrictFunctor hU.fromSpec) φ
    have hk : (cokernel ((restrictFunctor hU.fromSpec).map φ)).IsQuasicoherent :=
      isQuasicoherent_cokernel_spec _
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso i.symm hk

end
