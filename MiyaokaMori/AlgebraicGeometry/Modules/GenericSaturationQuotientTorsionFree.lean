import MiyaokaMori.AlgebraicGeometry.Modules.Flat.GenericSaturationSubsheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.TorsionFreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact

/-! # The quotient by the generic saturation is torsion-free

The quotient of a locally free sheaf by the saturation of a subspace of the generic fibre is
torsion-free: every stalk of `E/E_W` is a torsion-free module.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.Modules.isTorsionFree_cokernel_genericSaturation
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    [E.IsLocallyFree] (W : Submodule X.functionField (E.stalk (genericPoint X))) :
    AlgebraicGeometry.Scheme.Modules.IsTorsionFree
      (CategoryTheory.Limits.cokernel (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W)) := by
  intro x
  let i := AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W
  let F := AlgebraicGeometry.Scheme.Modules.stalkFunctor x
  have hp := AlgebraicGeometry.Scheme.Modules.stalk_preservesFiniteLimits_colimits x
  let hlim : PreservesFiniteLimits F := hp.1
  let hcolAll : PreservesColimits F := hp.2
  let hcol : PreservesFiniteColimits F := by
    let _ : PreservesColimits F := hcolAll
    infer_instance
  let hzero : F.PreservesZeroMorphisms := by
    let _ : PreservesFiniteLimits F := hlim
    infer_instance
  let T := @ShortComplex.map _ _ _ _ _ _ (ShortComplex.cokernelSequence i) F hzero
  have hseq : (ShortComplex.cokernelSequence i).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact i
      mono_f := by change Mono i; dsimp [i]; infer_instance
      epi_g := by change Epi (cokernel.π i); infer_instance }
  have hT : T.ShortExact := by
    exact @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _
      hseq F hzero hlim hcol
  have hf : T.f.hom = AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x i := by
    ext m
    rfl
  have hg : T.g.hom = AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π i) := by
    ext m
    rfl
  have hsurj : Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π i)) := by
    rw [← hg]
    exact hT.moduleCat_surjective_g
  have hex (m : E.presheaf.stalk x) :
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π i) m = 0 ↔
        m ∈ LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x i) := by
    have hm :=
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact) m
    change T.g.hom m = 0 ↔ ∃ y, T.f.hom y = m at hm
    rw [hf, hg] at hm
    exact hm
  have hS (m : E.presheaf.stalk x) :
      m ∈ LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x i) ↔
        AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X E x m ∈ W := by
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨U, hx, s, rfl⟩ :=
        (AlgebraicGeometry.Scheme.Modules.genericSaturation E W).presheaf.exists_germ_eq n
      rw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ]
      exact s.property _
    · intro hm
      obtain ⟨U, hx, s, rfl⟩ := E.presheaf.exists_germ_eq m
      have hs : s ∈ AlgebraicGeometry.Scheme.Modules.genericSaturationSections E W U := by
        intro hη
        simpa only [AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ] using hm
      refine ⟨(AlgebraicGeometry.Scheme.Modules.genericSaturation E W).presheaf.germ U x hx
        ⟨s, hs⟩, ?_⟩
      convert AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x i U hx ⟨s, hs⟩ using 1
      rfl
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r q hrq
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨m, rfl⟩ := hsurj q
  have hrm : r • m ∈ LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x i) := by
    apply (hex (r • m)).mp
    rw [(AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π i)).map_smul]
    exact hrq
  have hW : algebraMap (X.presheaf.stalk x) X.functionField r •
      AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X E x m ∈ W := by
    rw [← (AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X E x).map_smulₛₗ r m]
    exact (hS (r • m)).mp hrm
  have hrK : algebraMap (X.presheaf.stalk x) X.functionField r ≠ 0 := by
    intro h
    apply hr
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      (h.trans (map_zero _).symm)
  exact (hex m).mpr ((hS m).mpr ((W.smul_mem_iff hrK).mp hW))

end
