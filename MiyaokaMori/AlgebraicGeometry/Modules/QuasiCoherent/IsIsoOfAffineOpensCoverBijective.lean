import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.AffineTildeAdjunction
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleLocalIso

/-! # A morphism of quasi-coherent modules bijective on sections over an affine cover is an isomorphism

Two criteria for a morphism `φ : M ⟶ N` of **quasi-coherent** `O_X`-modules to be an isomorphism:
* (`isIso_of_isAffine_of_bijective_top`) `X` affine and `φ` bijective on global sections. Proof: for
  quasi-coherent modules on an affine scheme the counit `T(Γ N) ⟶ N` of the tilde–Γ adjunction is an
  isomorphism (`AffineTilde.isIso_counit_app`, Stacks 01I6/01I8), so `φ = ε_M⁻¹ ≫ T(Γ φ) ≫ ε_N`, and
  `Γ φ` is an isomorphism of modules because it is bijective.
* (`isIso_of_affineOpens_cover_bijective`) `φ` bijective on the sections over each member of a family
  of affine opens covering `X`. Proof: isomorphisms of module sheaves are detected on stalks
  (`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`, Stacks 01AI); a point `x` lies in some `U_i`; the
  restriction `φ|_{U_i}` is a morphism of quasi-coherent modules on the affine scheme `U_i`
  (`restrictFunctorIsoPullback`, `isQuasicoherent_pullback`) whose global sections map is
  `φ.app (U_i)` (the restriction has sections `Γ(M, ι ''ᵁ ⊤) = Γ(M, U_i)`), hence an isomorphism by the
  first criterion; the stalk of `φ` at `x` is the stalk of `φ|_{U_i}` at `x`
  (`AlgebraicGeometry.Scheme.Modules.moduleStalkMap_bijective_of_restrict_isIso`).

Source: Stacks 01AI (isomorphisms are local), 01I6/01I8 (quasi-coherent modules on affines are `M~`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme, a morphism of quasi-coherent modules that is bijective on global sections
is an isomorphism. -/
theorem isIso_of_isAffine_of_bijective_top {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : Function.Bijective (φ.app ⊤).hom) : IsIso φ := by
  have hG : IsIso ((AlgebraicGeometry.Scheme.Modules.pushforward X.isoSpec.hom ⋙
      AlgebraicGeometry.moduleSpecΓFunctor).map φ) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact h
  have hF : IsIso ((AlgebraicGeometry.tilde.functor Γ(X, ⊤) ⋙
      AlgebraicGeometry.Scheme.Modules.pullback X.isoSpec.hom).map
        ((AlgebraicGeometry.Scheme.Modules.pushforward X.isoSpec.hom ⋙
          AlgebraicGeometry.moduleSpecΓFunctor).map φ)) := inferInstance
  have h1 : IsIso (AffineTilde.adj.counit.app M) := AffineTilde.isIso_counit_app M
  have h2 : IsIso (AffineTilde.adj.counit.app N) := AffineTilde.isIso_counit_app N
  have hnat := AffineTilde.adj.counit.naturality φ
  have key : φ = inv (AffineTilde.adj.counit.app M) ≫
      ((AlgebraicGeometry.Scheme.Modules.pushforward X.isoSpec.hom ⋙ AlgebraicGeometry.moduleSpecΓFunctor) ⋙
        (AlgebraicGeometry.tilde.functor Γ(X, ⊤) ⋙ AlgebraicGeometry.Scheme.Modules.pullback X.isoSpec.hom)).map φ ≫
      AffineTilde.adj.counit.app N := by
    rw [hnat, IsIso.inv_hom_id_assoc]
    rfl
  have hF' : IsIso (((AlgebraicGeometry.Scheme.Modules.pushforward X.isoSpec.hom ⋙
      AlgebraicGeometry.moduleSpecΓFunctor) ⋙
        (AlgebraicGeometry.tilde.functor Γ(X, ⊤) ⋙ AlgebraicGeometry.Scheme.Modules.pullback X.isoSpec.hom)).map φ) :=
    hF
  rw [key]
  exact IsIso.comp_isIso

/-- Bijectivity of `φ.app` is transported along an equality of opens. -/
theorem bijective_app_of_eq {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {U V : X.Opens} (e : U = V) (h : Function.Bijective (φ.app V).hom) :
    Function.Bijective (φ.app U).hom := by
  subst e
  exact h

/-- A morphism of quasi-coherent modules that is bijective on the sections over each member of a
family of affine opens covering `X` is an isomorphism. -/
theorem isIso_of_affineOpens_cover_bijective {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) {ι : Type*} (Us : ι → X.Opens)
    (haff : ∀ i, AlgebraicGeometry.IsAffineOpen (Us i)) (hcov : ∀ x : X, ∃ i, x ∈ Us i)
    (h : ∀ i, Function.Bijective (φ.app (Us i)).hom) : IsIso φ := by
  rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
  intro x
  obtain ⟨i, hx⟩ := hcov x
  have : AlgebraicGeometry.IsAffine (Us i).toScheme := haff i
  haveI : (M.restrict (Us i).ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Us i).toScheme.ringCatSheaf).prop_of_iso
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (Us i).ι).app M).symm
      (inferInstanceAs ((AlgebraicGeometry.Scheme.Modules.pullback (Us i).ι).obj M).IsQuasicoherent)
  haveI : (N.restrict (Us i).ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Us i).toScheme.ringCatSheaf).prop_of_iso
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (Us i).ι).app N).symm
      (inferInstanceAs ((AlgebraicGeometry.Scheme.Modules.pullback (Us i).ι).obj N).IsQuasicoherent)
  have e : (Us i).ι ''ᵁ (⊤ : (Us i).toScheme.Opens) = Us i := by
    rw [AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange, AlgebraicGeometry.Scheme.Opens.opensRange_ι]
  have hb : Function.Bijective
      (((AlgebraicGeometry.Scheme.Modules.restrictFunctor (Us i).ι).map φ).app ⊤).hom :=
    bijective_app_of_eq φ e (h i)
  haveI : IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (Us i).ι).map φ) :=
    isIso_of_isAffine_of_bijective_top _ hb
  exact AlgebraicGeometry.Scheme.Modules.moduleStalkMap_bijective_of_restrict_isIso (Us i).ι φ ⟨x, hx⟩

end AlgebraicGeometry.Scheme.Modules

end
