import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleStalkFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.GenericSaturationQuotientTorsionFree
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.GenericSaturationSubsheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankConstantConnected
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.TorsionFreeOnCurveLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.TorsionFreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # A saturated line subbundle of a vector bundle on a curve

Choose a line in the generic fibre of a vector bundle `E` on a smooth projective curve and
saturate it; this gives a rank-one subbundle `L ⊆ E` whose quotient is torsion-free, hence
locally free.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The inclusion `genericSaturation.ι` of the saturated subsheaf is injective on every stalk:
on each open it is the inclusion of a submodule, and
`TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective` passes injectivity to stalks. -/
theorem AlgebraicGeometry.Scheme.Modules.genericSaturation_stalkMap_injective
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    (W : Submodule X.functionField (E.stalk (genericPoint X))) (x : X) :
    Function.Injective
      (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W)) := by
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    (f := (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W).mapPresheaf)
  intro U a b hab
  exact Subtype.ext hab

/-- The stalks of a locally free sheaf are free modules, hence torsion-free. -/
theorem AlgebraicGeometry.Scheme.Modules.isTorsionFree_of_isLocallyFree
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) [E.IsLocallyFree] [E.IsFiniteType] :
    AlgebraicGeometry.Scheme.Modules.IsTorsionFree E := by
  intro x
  obtain ⟨U, I, hxU, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree E x
  have : Finite I :=
    AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free E U I e x hxU
  have := AlgebraicGeometry.Scheme.Modules.free_stalk_of_restrict_iso_free E U I e x hxU
  infer_instance

/-- The saturated subsheaf is torsion-free: its stalks embed into the torsion-free modules `E_x`. -/
theorem AlgebraicGeometry.Scheme.Modules.isTorsionFree_genericSaturation
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    [E.IsLocallyFree] [E.IsFiniteType] (W : Submodule X.functionField (E.stalk (genericPoint X))) :
    AlgebraicGeometry.Scheme.Modules.IsTorsionFree
      (AlgebraicGeometry.Scheme.Modules.genericSaturation E W) := by
  intro x
  have hE := AlgebraicGeometry.Scheme.Modules.isTorsionFree_of_isLocallyFree E x
  exact (AlgebraicGeometry.Scheme.Modules.genericSaturation_stalkMap_injective E W x).moduleIsTorsionFree
    _ (fun r m => LinearMap.map_smul _ r m)

/-- At the generic point the stalk of the saturated subsheaf is linearly isomorphic to `W`, so
its rank there is `dim_{K(X)} W`. -/
theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_genericSaturation_genericPoint
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    (W : Submodule X.functionField (E.stalk (genericPoint X))) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk
      (AlgebraicGeometry.Scheme.Modules.genericSaturation E W) (genericPoint X) =
      Module.finrank X.functionField W := by
  set ξ := genericPoint X
  set L₀ := AlgebraicGeometry.Scheme.Modules.genericSaturation E W
  let f := ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map
    (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W)).hom
  have hinj : Function.Injective f :=
    AlgebraicGeometry.Scheme.Modules.genericSaturation_stalkMap_injective E W ξ
  have hrange : LinearMap.range f = W :=
    AlgebraicGeometry.Scheme.Modules.genericSaturation_stalk_generic E W
  have h1 : Module.finrank X.functionField (L₀.stalk ξ) = Module.finrank X.functionField W := by
    have h := (LinearEquiv.ofInjective f hinj).finrank_eq
    rw [hrange] at h
    exact h
  unfold AlgebraicGeometry.Scheme.Modules.rankAtStalk
  let := (X.residue ξ).hom.toAlgebra
  rw [Module.finrank_baseChange]
  exact h1

/-- A vector bundle `E` of positive rank on a smooth projective curve has a line subbundle
`L ⟶ E` (a monomorphism) with locally free cokernel. -/
theorem exists_line_subbundle {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : 0 < E.rank) :
    ∃ (L : LineBundle C.toVariety) (ι : L.toModules ⟶ E.toModules),
      CategoryTheory.Mono ι ∧
      (CategoryTheory.Limits.cokernel ι).IsLocallyFree := by
  set ξ := genericPoint C.toScheme
  have hconn : ConnectedSpace C.toScheme := C.connected
  have hElf : E.toModules.IsLocallyFree := E.locallyFree
  have hEft : E.toModules.IsFiniteType := E.isFiniteType
  -- Step 1: the generic fibre is nonzero; choose a line `W` in it
  have hnt : Nontrivial (E.toModules.stalk ξ) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 : AlgebraicGeometry.Scheme.Modules.rankAtStalk E.toModules ξ = 0 := by
      unfold AlgebraicGeometry.Scheme.Modules.rankAtStalk
      let := (C.toScheme.residue ξ).hom.toAlgebra
      exact Module.finrank_zero_of_subsingleton
    rw [E.rankAtStalk_eq] at h0
    omega
  obtain ⟨v, hv⟩ := exists_ne (0 : E.toModules.stalk ξ)
  let W : Submodule C.toScheme.functionField (E.toModules.stalk ξ) :=
    Submodule.span C.toScheme.functionField {v}
  -- Step 2: the saturated subsheaf `L₀` and its inclusion `ι₀`
  set L₀ := AlgebraicGeometry.Scheme.Modules.genericSaturation E.toModules W
  set ι₀ := AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E.toModules W
  -- Step 4: coherence
  have hEcoh : E.toModules.IsCoherent :=
    AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree E.toModules
  have hEqc : E.toModules.IsQuasicoherent := hEcoh.quasicoherent
  have hL₀qc : L₀.IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.genericSaturation_isQuasicoherent E.toModules W
  have hL₀coh : L₀.IsCoherent := AlgebraicGeometry.Scheme.Modules.isCoherent_of_mono ι₀
  have hQqc : (cokernel ι₀).IsQuasicoherent :=
    (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel ι₀).2
  have hQcoh : (cokernel ι₀).IsCoherent :=
    AlgebraicGeometry.Scheme.Modules.isCoherent_of_epi (cokernel.π ι₀)
  -- Steps 3 and 5: the quotient is torsion-free ⇒ locally free; `L₀` is torsion-free ⇒ locally free
  have hQlf : (cokernel ι₀).IsLocallyFree :=
    isLocallyFree_of_torsionFree_on_curve C _
      (AlgebraicGeometry.Scheme.Modules.isTorsionFree_cokernel_genericSaturation E.toModules W)
  have hL₀lf : L₀.IsLocallyFree :=
    isLocallyFree_of_torsionFree_on_curve C L₀
      (AlgebraicGeometry.Scheme.Modules.isTorsionFree_genericSaturation E.toModules W)
  have hL₀ft : L₀.IsFiniteType := hL₀coh.finiteType
  -- Step 6: the rank is 1
  have hrank : AlgebraicGeometry.Scheme.Modules.rankAtStalk L₀ ξ = 1 := by
    rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_genericSaturation_genericPoint]
    exact finrank_span_singleton hv
  have hrank_all : ∀ x : C.toScheme, AlgebraicGeometry.Scheme.Modules.rankAtStalk L₀ x = 1 :=
    fun x => (AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_of_connected L₀ x ξ).trans hrank
  exact ⟨⟨⟨L₀, 1, hL₀lf, hL₀ft, hrank_all⟩, rfl⟩, ι₀, inferInstance, hQlf⟩

end
