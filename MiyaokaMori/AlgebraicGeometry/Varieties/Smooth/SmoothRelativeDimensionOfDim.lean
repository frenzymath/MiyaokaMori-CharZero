import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyLocalDimensionEqDim
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaFiniteType
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfFreeAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback

/-! # A smooth variety of dimension `n` is smooth of relative dimension `n`

The structure morphism of a smooth projective variety of dimension `n` over a field is smooth of
relative dimension `n`.

Proof sketch:
1. `Smooth.exists_isStandardSmooth` gives a standard smooth affine chart at every point; the affine
   open of the base field is necessarily `⊤`.
2. `Omega_appIso` identifies the module of sections of the relative differentials on the chart with
   the Kähler differentials; standard smoothness makes this module free and finite.
3. A basis of the section module gives an isomorphism with a free sheaf on the affine open;
   `rankAtStalk_of_restrict_iso_free` identifies the finite rank of the section module with the
   rank at the stalks.
4. `IsSmoothOver.isLocallyFree_omega` and the hypothesis on `Variety.dim` give that this rank is
   `n`, and the Kähler rank criterion for standard smooth algebras gives the relative dimension of
   the chart.

Sources: Stacks 01UT, 02G1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

namespace smoothBridgeFreeAffine

private theorem basis_restrict {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) (I : Type u)
    (b : Module.Basis I Γ(X, U) Γ(M, U)) :
    Nonempty (Module.Basis I Γ(X, U) Γ(M.restrict hU.fromSpec, ⊤)) := by
  have hV : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let e : Γ(X, U) ≃+* Γ(X, U) :=
    ((X.presheaf.mapIso (eqToIso hV).op) ≪≫ (hU.fromSpec.appIso ⊤) ≪≫
      Scheme.ΓSpecIso Γ(X, U)).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  have key : ∀ (r : Γ(X, hU.fromSpec ''ᵁ ⊤)) (y : Γ(M, hU.fromSpec ''ᵁ ⊤)),
      (M.restrictAppIso hU.fromSpec ⊤).inv (r • y) =
        ((hU.fromSpec.appIso ⊤).hom r) • (M.restrictAppIso hU.fromSpec ⊤).inv y := fun r y => by
    have := Scheme.Modules.smul_restrictAppIso_inv_apply hU.fromSpec M ⊤ r y
    exact this
  let g : Γ(M, U) →ₛₗ[(e : Γ(X, U) →+* Γ(X, U))] Γ(M.restrict hU.fromSpec, ⊤) :=
    { toFun := fun m => (M.restrictAppIso hU.fromSpec ⊤).inv (M.presheaf.map (eqToHom hV).op m)
      map_add' := fun a b => by simp
      map_smul' := fun a m => by
        rw [Scheme.Modules.map_smul, key, Scheme.Modules.smul_Spec_def]
        congr 1
        simp only [e]
        have h1 : (Opens.leTop (⊤ : (Spec Γ(X, U)).Opens)).op = 𝟙 _ := Subsingleton.elim _ _
        rw [h1, CategoryTheory.Functor.map_id]
        simp [Iso.commRingCatIsoToRingEquiv] }
  have hg : Function.Bijective g :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec ⊤).inv).comp
      (ConcreteCategory.bijective_of_isIso (M.presheaf.map (eqToHom hV).op))
  obtain ⟨b'⟩ := MiyaokaMori.basis_of_semilinearEquiv (LinearEquiv.ofBijective g hg) b
  exact ⟨b'⟩

private theorem spec_iso_free {R : CommRingCat.{u}} (N : (Spec R).Modules) [N.IsQuasicoherent]
    (I : Type u) (b : Module.Basis I R Γ(N, ⊤)) :
    Nonempty (N ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) I) := by
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let P := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let l : P ≅ ModuleCat.of R (I →₀ R) := b.repr.toModuleIso
  exact ⟨(asIso N.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso l ≪≫ tildeFinsupp I⟩

private theorem restrict_fromSpec_iso_free {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (I : Type u)
    (b : Module.Basis I Γ(X, U) Γ(M, U)) :
    Nonempty (M.restrict hU.fromSpec ≅
      SheafOfModules.free (R := (Spec Γ(X, U)).ringCatSheaf) I) := by
  obtain ⟨b'⟩ := basis_restrict M hU I b
  exact spec_iso_free (M.restrict hU.fromSpec) I b'

private theorem pullback_iso_free {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (I : Type u)
    (b : Module.Basis I Γ(X, U) Γ(M, U)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) := by
  obtain ⟨ψ⟩ := restrict_fromSpec_iso_free M hU I b
  let F : SheafOfModules.{u} (Spec Γ(X, U)).ringCatSheaf ⥤
      SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor hU.isoSpec.hom
  have hF : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction hU.isoSpec.hom).leftAdjoint_preservesColimits.{u, u}
  let e0 := ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M ≪≫
    F.mapIso ψ
  exact ⟨e0 ≪≫
    (SheafOfModules.mapFreeIso F I (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm).symm⟩

end smoothBridgeFreeAffine

/-- A smooth variety of dimension `n` over `K` is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_of_dim {K : Type u} [Field K]
    {X : SmoothProjectiveVariety K} {n : ℕ}
    (hn : X.toVariety.dim = n) :
    AlgebraicGeometry.SmoothOfRelativeDimension n
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := by
  let f := X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)
  have hsm : AlgebraicGeometry.Smooth f := by
    simpa [f, IsSmoothOver] using X.smooth
  letI : AlgebraicGeometry.Smooth f := hsm
  have hloc := IsSmoothOver.isLocallyFree_omega X.toVariety X.smooth
  have hrank : ∀ x : X.toScheme,
      AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (AlgebraicGeometry.Omega f) x = n := by
    intro x
    have hx := hloc.2 x
    have hxdim : X.toVariety.dim = n := hn
    exact (by simpa [f, hxdim] using hx)
  have hft : (AlgebraicGeometry.Omega f).IsFiniteType := by
    exact AlgebraicGeometry.Omega_isFiniteType f
  letI : (AlgebraicGeometry.Omega f).IsFiniteType := hft
  letI : (AlgebraicGeometry.Omega f).IsQuasicoherent :=
    AlgebraicGeometry.Omega_isQuasicoherent f
  apply AlgebraicGeometry.SmoothOfRelativeDimension.mk
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ :=
    AlgebraicGeometry.Smooth.exists_isStandardSmooth f x
  have hUtop : U = ⊤ := by
    apply le_antisymm le_top
    intro y hy
    have hy' : y = f x := Subsingleton.elim _ _
    rw [hy']
    exact e hx
  subst U
  have hVnonempty : Nonempty V := ⟨⟨x, hx⟩⟩
  letI : Algebra Γ(AlgebraicGeometry.Spec (CommRingCat.of K), ⊤) Γ(X.toScheme, V) :=
    (f.appLE ⊤ V e).hom.toAlgebra
  have hsalg : Algebra.IsStandardSmooth Γ(AlgebraicGeometry.Spec (CommRingCat.of K), ⊤)
      Γ(X.toScheme, V) := hs.toAlgebra
  have hfree : Module.Free Γ(X.toScheme, V) Γ(AlgebraicGeometry.Omega f, V) := by
    exact Module.Free.of_equiv (AlgebraicGeometry.Omega_appIso f (isAffineOpen_top _) hV e).symm
  have hfinmod : Module.Finite Γ(X.toScheme, V) Γ(AlgebraicGeometry.Omega f, V) := by
    exact Module.Finite.equiv (AlgebraicGeometry.Omega_appIso f (isAffineOpen_top _) hV e).symm
  have hfin : Module.finrank Γ(X.toScheme, V)
      Γ(AlgebraicGeometry.Omega f, V) = n := by
    let I := Module.Free.ChooseBasisIndex Γ(X.toScheme, V)
      Γ(AlgebraicGeometry.Omega f, V)
    letI : Fintype I := Module.Free.ChooseBasisIndex.fintype
      Γ(X.toScheme, V) Γ(AlgebraicGeometry.Omega f, V)
    let b : Module.Basis I Γ(X.toScheme, V) Γ(AlgebraicGeometry.Omega f, V) :=
      Module.Free.chooseBasis Γ(X.toScheme, V) Γ(AlgebraicGeometry.Omega f, V)
    obtain ⟨ψ⟩ := smoothBridgeFreeAffine.pullback_iso_free
      (AlgebraicGeometry.Omega f) hV I b
    have hr := AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
      (AlgebraicGeometry.Omega f) V I ψ x hx
    calc
      Module.finrank Γ(X.toScheme, V) Γ(AlgebraicGeometry.Omega f, V) = Fintype.card I := by
        simpa [I] using (Module.finrank_eq_card_chooseBasisIndex
          Γ(X.toScheme, V) Γ(AlgebraicGeometry.Omega f, V))
      _ = AlgebraicGeometry.Scheme.Modules.rankAtStalk (AlgebraicGeometry.Omega f) x := hr.symm
      _ = n := hrank x
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension n
      (f.appLE ⊤ V e).hom := by
    apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr
    have hrankomega : Module.rank Γ(X.toScheme, V)
        (KaehlerDifferential Γ(AlgebraicGeometry.Spec (CommRingCat.of K), ⊤) Γ(X.toScheme, V)) = n := by
      rw [← Module.finrank_eq_rank]
      rw [← (AlgebraicGeometry.Omega_appIso f (isAffineOpen_top _) hV e).finrank_eq]
      exact_mod_cast hfin
    exact hrankomega
  exact ⟨⊤, isAffineOpen_top _, V, hV, hx, e, hstd⟩

end
