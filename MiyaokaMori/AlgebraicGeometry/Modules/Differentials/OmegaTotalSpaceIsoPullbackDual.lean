import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.GradedRing.KaehlerBasisOfIsSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.IsIsoOfAffineOpensCoverBijective
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeExistsAffineOpenBasis
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsBasisOfBasis
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaPushforwardDerivationHom
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraSectionsIsSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionConstructions
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.TotalSpaceLinearCoordinate

/-! # Relative differentials of the total space of a vector bundle

Relative differentials of the total space of a vector bundle: for `V` locally free of finite type on `B`
and `p : Tot(V) = Spec_B Sym(V^∨) → B`, there is an isomorphism `Ω_{Tot(V)/B} ≅ p^*(V^∨)`.

Source: Eisenbud, *Commutative Algebra*, Prop. 16.1 (Ω of a polynomial algebra is free on the `dx_i`),
Stacks 01US/01UT (Ω over an affine open pair is the Kähler module of the sections, `Omega_appHom_bijective`),
Stacks 01I9 (sections of a pullback over the preimage of an affine open). Used to show that the
Euler section of the twisted affine cone is nowhere vanishing (§2.1 of the paper).

Route. Write `T := Tot(V)`, `p : T → B`, `W := V^∨`.
* `ψ : W ⟶ p_* Ω_{T/B}` is `ξ ↦ d(ℓ_ξ)`, the universal derivation applied to the linear function `ℓ_ξ`
  of `ξ` (`totalSpace.linearFunctionHom`, the degree-one inclusion `W ⟶ p_* O_T`, followed by
  `Omega.pushforwardDerivationHom`, the `O_B`-linear pushforward of `d`); `φ : p^* W ⟶ Ω_{T/B}` is its
  adjoint transpose (`pullbackDualToOmega`), so `φ(η_U ξ) = d ℓ_ξ` (`pullbackDualToOmega_app_unit`).
* `φ` is an isomorphism iff it is bijective on sections over `p⁻¹U` for `U` running through affine opens
  of `B` on which `Γ(W, U)` is free (these `p⁻¹U` are affine and cover `T`; both sides are quasi-coherent):
  `Modules.isIso_of_affineOpens_cover_bijective`, `Modules.exists_affineOpen_basis_sections`.
* Over such `U` with basis `b` of `Γ(W, U)`: `Γ(p^*W, p⁻¹U)` is free on `η_U(b i)`
  (`Modules.pullback_sections_exists_basis`, from Stacks 01I9), and
  `Γ(Ω_{T/B}, p⁻¹U) ≅ Ω_{Γ(T,p⁻¹U)/Γ(B,U)}` (`Omega_appHom_bijective`) is free on `d ℓ_{b i}` because
  `Γ(T, p⁻¹U) = Sym(V^∨)(U)` is the symmetric algebra of `Γ(W, U)`
  (`symGradedAlgebra_sectionsRing_isSymmetricAlgebra`, transported through `relativeSpec.sectionsIso`
  in `isSymmetricAlgebra_linearFunctionLinearMap`) and the Kähler module of a symmetric algebra of a
  free module is free on the `d` of the basis (`KaehlerDifferential.exists_basis_of_isSymmetricAlgebra`).
  A linear map sending a basis to a basis is bijective.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.totalSpace

variable {B : AlgebraicGeometry.Scheme.{u}} (V : B.Modules) [V.IsLocallyFree] [V.IsFiniteType]

/-- `Tot(V) → B` is an affine morphism (it is a relative Spec). Not registered as a global instance;
install locally with `haveI`. -/
theorem isAffineHom_hom : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.totalSpace V).hom :=
  AlgebraicGeometry.Scheme.relativeSpec_isAffineHom _

/-- `ψ : V^∨ ⟶ p_* Ω_{Tot(V)/B}`, `ξ ↦ d(ℓ_ξ)`: the linear function of `ξ` followed by the universal
derivation. -/
def dualToPushforwardOmega :
    AlgebraicGeometry.Scheme.Modules.dual V ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace V).hom).obj
        (AlgebraicGeometry.Omega (AlgebraicGeometry.Scheme.totalSpace V).hom) :=
  linearFunctionHom V ≫ AlgebraicGeometry.Omega.pushforwardDerivationHom (AlgebraicGeometry.Scheme.totalSpace V).hom

theorem dualToPushforwardOmega_app (U : B.Opens) (ξ : Γ(AlgebraicGeometry.Scheme.Modules.dual V, U)) :
    (dualToPushforwardOmega V).app U ξ =
      (AlgebraicGeometry.Omega.universalDerivation (AlgebraicGeometry.Scheme.totalSpace V).hom).d
        (X := op ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U)) (linearFunction V U ξ) := rfl

/-- `φ : p^* V^∨ ⟶ Ω_{Tot(V)/B}`, the adjoint transpose of `dualToPushforwardOmega`. -/
def pullbackDualToOmega :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace V).hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      AlgebraicGeometry.Omega (AlgebraicGeometry.Scheme.totalSpace V).hom :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.Scheme.totalSpace V).hom).homEquiv _ _).symm (dualToPushforwardOmega V)

/-- `φ (η_U ξ) = d ℓ_ξ` on `p⁻¹U`, where `η` is the unit of the pullback–pushforward adjunction. -/
theorem pullbackDualToOmega_app_unit (U : B.Opens) (ξ : Γ(AlgebraicGeometry.Scheme.Modules.dual V, U)) :
    (pullbackDualToOmega V).app ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.Scheme.totalSpace V).hom).unit.app (AlgebraicGeometry.Scheme.Modules.dual V)).app U ξ) =
      (AlgebraicGeometry.Omega.universalDerivation (AlgebraicGeometry.Scheme.totalSpace V).hom).d
        (X := op ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U)) (linearFunction V U ξ) := by
  have h1 := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.Scheme.totalSpace V).hom).homEquiv_unit
    (X := AlgebraicGeometry.Scheme.Modules.dual V)
    (Y := AlgebraicGeometry.Omega (AlgebraicGeometry.Scheme.totalSpace V).hom) (f := pullbackDualToOmega V)
  rw [show (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.Scheme.totalSpace V).hom).homEquiv _ _ (pullbackDualToOmega V) =
      dualToPushforwardOmega V from Equiv.apply_symm_apply _ _] at h1
  exact (congrArg (fun f => f.app U ξ) h1).symm

/-- The linear-function map `ξ ↦ ℓ_ξ` as a `Γ(B, U)`-linear map `Γ(V^∨, U) → Γ(T, p⁻¹U)`, the target
being a `Γ(B, U)`-algebra through `p.appLE U (p⁻¹U)` (the algebra structure used by `Omega_appHom`). -/
def linearFunctionLinearMap (U : B.Opens) :
    letI := ((AlgebraicGeometry.Scheme.totalSpace V).hom.appLE U
      ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    Γ(AlgebraicGeometry.Scheme.Modules.dual V, U) →ₗ[Γ(B, U)]
      Γ((AlgebraicGeometry.Scheme.totalSpace V).left, (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U) :=
  letI := ((AlgebraicGeometry.Scheme.totalSpace V).hom.appLE U
    ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  { toFun := fun ξ => linearFunction V U ξ
    map_add' := fun a b => map_add ((linearFunctionHom V).app U).hom a b
    map_smul' := fun r a => by
      change (linearFunctionHom V).app U (r • a) =
        ((AlgebraicGeometry.Scheme.totalSpace V).hom.appLE U
          ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U) le_rfl).hom r * linearFunction V U a
      rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul, ← AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
      rfl }

/-- Over an affine open `U ⊆ B`, `Γ(T, p⁻¹U)` is the symmetric algebra of `Γ(V^∨, U)` through
`ξ ↦ ℓ_ξ`: transport of `symGradedAlgebra_sectionsRing_isSymmetricAlgebra` along the ring isomorphism
`Sym(V^∨)(U) ≅ Γ(T, p⁻¹U)` (`relativeSpec.sectionsIso`; `structureHom_app_affine`,
`sectionsUnit_comp_sectionsToFunctions` for the compatibility with the algebra structures). -/
theorem isSymmetricAlgebra_linearFunctionLinearMap (U : B.affineOpens) :
    letI := ((AlgebraicGeometry.Scheme.totalSpace V).hom.appLE U.1
      ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
    IsSymmetricAlgebra (linearFunctionLinearMap V U.1) := by
  letI := ((AlgebraicGeometry.Scheme.totalSpace V).hom.appLE U.1
    ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  letI := ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsUnit U.1).toAlgebra
  have : (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree V
  have hS := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_sectionsRing_isSymmetricAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V) U
  let re : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsRing U.1 ≃+*
      Γ((AlgebraicGeometry.Scheme.totalSpace V).left, (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) :=
    (AlgebraicGeometry.Scheme.relativeSpec.sectionsIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total U).commRingCatIsoToRingEquiv
  have hre : ∀ r : Γ(B, U.1),
      re ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsUnit U.1 r) =
        ((AlgebraicGeometry.Scheme.totalSpace V).hom.appLE U.1
          ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) le_rfl).hom r := by
    intro r
    have h := congrArg (fun f => f.hom r)
      (AlgebraicGeometry.Scheme.relativeSpec.sectionsUnit_comp_sectionsToFunctions
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total U)
    rw [← AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
    exact h
  let ae : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsRing U.1 ≃ₐ[Γ(B, U.1)]
      Γ((AlgebraicGeometry.Scheme.totalSpace V).left, (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) :=
    AlgEquiv.ofRingEquiv hre
  refine IsSymmetricAlgebra.of_equiv (hS.equiv.trans ae) ?_
  ext ξ
  change ae (hS.equiv (SymmetricAlgebra.ι _ _ ξ)) = linearFunction V U.1 ξ
  rw [IsSymmetricAlgebra.equiv_apply, SymmetricAlgebra.lift_ι_apply]
  exact (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_affine
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total U
    ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).totalIncl 1).app U.1 ξ)).symm

/-- Over an affine open `U` with `b` a basis of `Γ(V^∨, U)`, the sections `Γ(Ω_{T/B}, p⁻¹U)` form a free
`Γ(T, p⁻¹U)`-module on `d ℓ_{b i}`: `Γ(Ω, p⁻¹U) ≅ Ω_{Γ(T,p⁻¹U)/Γ(B,U)}` (`Omega_appHom_bijective`,
Stacks 01UT) and the Kähler module of the symmetric algebra of a free module is free on the `d` of the
basis (`KaehlerDifferential.exists_basis_of_isSymmetricAlgebra`, Eisenbud 16.1). -/
theorem omega_sections_exists_basis (U : B.affineOpens) {I : Type u}
    (b : Module.Basis I Γ(B, U.1) Γ(AlgebraicGeometry.Scheme.Modules.dual V, U.1)) :
    ∃ c : Module.Basis I Γ((AlgebraicGeometry.Scheme.totalSpace V).left,
        (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1)
        Γ(AlgebraicGeometry.Omega (AlgebraicGeometry.Scheme.totalSpace V).hom,
          (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1),
      ∀ i, c i = (AlgebraicGeometry.Omega.universalDerivation (AlgebraicGeometry.Scheme.totalSpace V).hom).d
        (X := op ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1)) (linearFunction V U.1 (b i)) := by
  letI := ((AlgebraicGeometry.Scheme.totalSpace V).hom.appLE U.1
    ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  obtain ⟨c, hc⟩ := KaehlerDifferential.exists_basis_of_isSymmetricAlgebra
    (isSymmetricAlgebra_linearFunctionLinearMap V U) b
  have := isAffineHom_hom V
  have hU : AlgebraicGeometry.IsAffineOpen ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) :=
    U.2.preimage (AlgebraicGeometry.Scheme.totalSpace V).hom
  let e := LinearEquiv.ofBijective
    (AlgebraicGeometry.Omega_appHom (AlgebraicGeometry.Scheme.totalSpace V).hom U.1
      ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) le_rfl)
    (AlgebraicGeometry.Omega_appHom_bijective (AlgebraicGeometry.Scheme.totalSpace V).hom U.2 hU le_rfl)
  refine ⟨c.map e, fun i => ?_⟩
  rw [Module.Basis.map_apply, hc]
  exact AlgebraicGeometry.Omega_appHom_D (AlgebraicGeometry.Scheme.totalSpace V).hom U.1
    ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) le_rfl _

/-- The affine-local check: over an affine open `U ⊆ B` on which `Γ(V^∨, U)` is free, `φ` is bijective
on sections over `p⁻¹U` (it sends the basis `η_U(b i)` of `Γ(p^*V^∨, p⁻¹U)` to the basis `d ℓ_{b i}`
of `Γ(Ω, p⁻¹U)`). -/
theorem pullbackDualToOmega_app_preimage_bijective (U : B.affineOpens) {I : Type u} [Finite I]
    (b : Module.Basis I Γ(B, U.1) Γ(AlgebraicGeometry.Scheme.Modules.dual V, U.1)) :
    Function.Bijective
      ((pullbackDualToOmega V).app ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1)).hom := by
  have : (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree V
  have := isAffineHom_hom V
  obtain ⟨c, hc⟩ := AlgebraicGeometry.Scheme.Modules.pullback_sections_exists_basis
    (AlgebraicGeometry.Scheme.totalSpace V).hom (AlgebraicGeometry.Scheme.Modules.dual V) U b
  obtain ⟨c', hc'⟩ := omega_sections_exists_basis V U b
  let e := c.equiv c' (Equiv.refl I)
  let L : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace V).hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V), (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) →ₗ[Γ(
        (AlgebraicGeometry.Scheme.totalSpace V).left, (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1)]
      Γ(AlgebraicGeometry.Omega (AlgebraicGeometry.Scheme.totalSpace V).hom,
        (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1) :=
    ((pullbackDualToOmega V).val.app (op ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U.1))).hom
  have key : L = e.toLinearMap := by
    apply c.ext
    intro i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, hc, hc']
    exact pullbackDualToOmega_app_unit V U.1 (b i)
  change Function.Bijective L
  rw [key]
  exact e.bijective

/-- `φ : p^* V^∨ ⟶ Ω_{Tot(V)/B}` is an isomorphism: both sides are quasi-coherent, the affine opens
`p⁻¹U` (for `U ⊆ B` affine with `Γ(V^∨, U)` free) cover `Tot(V)`, and `φ` is bijective on sections over
each of them. -/
theorem isIso_pullbackDualToOmega : IsIso (pullbackDualToOmega V) := by
  have : (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree V
  have : (AlgebraicGeometry.Omega (AlgebraicGeometry.Scheme.totalSpace V).hom).IsQuasicoherent :=
    AlgebraicGeometry.Omega_isQuasicoherent (AlgebraicGeometry.Scheme.totalSpace V).hom
  have : (AlgebraicGeometry.Scheme.Modules.dual V).IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' V
  have : (AlgebraicGeometry.Scheme.Modules.dual V).IsFiniteType :=
    AlgebraicGeometry.Scheme.Modules.isFiniteType_dual V inferInstance
  have := isAffineHom_hom V
  have hex := fun t : (AlgebraicGeometry.Scheme.totalSpace V).left =>
    AlgebraicGeometry.Scheme.Modules.exists_affineOpen_basis_sections
      (AlgebraicGeometry.Scheme.Modules.dual V) ((AlgebraicGeometry.Scheme.totalSpace V).hom.base t)
  choose U I hI hmem hb using hex
  refine AlgebraicGeometry.Scheme.Modules.isIso_of_affineOpens_cover_bijective (pullbackDualToOmega V)
    (fun t => (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ (U t).1)
    (fun t => (U t).2.preimage (AlgebraicGeometry.Scheme.totalSpace V).hom) (fun t => ⟨t, hmem t⟩)
    (fun t => ?_)
  have := hI t
  exact pullbackDualToOmega_app_preimage_bijective V (U t) (hb t).some

end AlgebraicGeometry.Scheme.totalSpace

/-- `Ω_{Tot(V)/B} ≅ p^* (V^∨)` for `V` locally free of finite type,
`p = (totalSpace V).hom : Spec_B Sym(V^∨) → B` (Eisenbud, Commutative Algebra, Prop. 16.1; Stacks 01US/01UT).

The isomorphism is the inverse of `totalSpace.pullbackDualToOmega V : p^* V^∨ ⟶ Ω_{Tot(V)/B}`
(`ξ ↦ d ℓ_ξ` on the pulled-back linear forms), an isomorphism by `totalSpace.isIso_pullbackDualToOmega`;
see the module docstring for the route.

Edge cases: `B = ∅` — both sides are zero; rank `0` — `Tot(V) = B`, `Ω_{B/B} = 0` and `p^*0 = 0`; the
statement does not require `V` to be a line bundle. -/
theorem AlgebraicGeometry.Omega_totalSpace_iso_pullback_dual {B : AlgebraicGeometry.Scheme.{u}}
    (V : B.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    Nonempty (AlgebraicGeometry.Omega (AlgebraicGeometry.Scheme.totalSpace V).hom ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace V).hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V)) := by
  have := AlgebraicGeometry.Scheme.totalSpace.isIso_pullbackDualToOmega V
  exact ⟨(asIso (AlgebraicGeometry.Scheme.totalSpace.pullbackDualToOmega V)).symm⟩

end
