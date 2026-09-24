import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackLineBundlePow
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Ampleness is preserved by restriction to closed subschemes (Stacks 01PU)

Stacks 01PU: the restriction of an ample invertible sheaf to any closed subscheme is ample.

Reference: Stacks 01PU (used in the proof of 0BEV: "replace `X` by `Z` and `L_i` by `L_i|_Z`").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The pullback of a section vanishing at `g x` vanishes at `x`. -/
private theorem isZeroAt_sectionPullbackAlong_of_isZeroAt
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (hzero : IsZeroAt s (g.base x)) :
    IsZeroAt (sectionPullbackAlong g s) x := by
  letI := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra g x
  have hgerm :
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.germ ⊤ x trivial).hom
          (sectionPullbackAlong g s) =
        AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x
          ((M.presheaf.germ ⊤ (g.base x) trivial).hom s) :=
    (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ g M x ⊤ trivial s).symm
  change (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.germ ⊤ x trivial).hom
      (sectionPullbackAlong g s) ∈
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x))
  rw [hgerm]
  change ((M.presheaf.germ ⊤ (g.base x) trivial).hom s) ∈
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x))) •
      (⊤ : Submodule (Y.presheaf.stalk (g.base x)) (M.presheaf.stalk (g.base x))) at hzero
  refine Submodule.smul_induction_on hzero ?_ ?_
  · intro r hr m hm
    change AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom g M x (r • m) ∈ _
    rw [AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_smul]
    exact Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk x)
      (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x)))
      ((IsLocalRing.map_maximalIdeal_le (g.stalkMap x).hom)
        (Ideal.mem_map_of_mem (g.stalkMap x).hom hr)) Submodule.mem_top
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

/-- **Stacks 01PU.** The pullback of an ample invertible sheaf along a closed immersion is ample. -/
theorem AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion {X Z : AlgebraicGeometry.Scheme.{u}}
    (ι : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι] (L : X.Modules) [L.IsLineBundle]
    (hL : AlgebraicGeometry.IsAmple L) :
    AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L) := by
  letI : CompactSpace X := hL.1
  letI : CompactSpace Z := ι.isClosedEmbedding.compactSpace
  refine ⟨inferInstance, fun z ↦ ?_⟩
  obtain ⟨m, hm, sΓ, hzs, hsa⟩ := hL.2 (ι.base z)
  letI hpow_m : (AlgebraicGeometry.Scheme.Modules.tensorPow L m).IsLineBundle :=
    SheafOfModules.IsLineBundle.tensorPow L m
  letI hpull : ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback ι L
  letI hpull_pow :
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow L m)).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback ι
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
  letI hpull_mpow :
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L) m).IsLineBundle :=
    SheafOfModules.IsLineBundle.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L) m
  let s : ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).val.obj
      (Opposite.op ⊤) : Type u) := by
    change Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤)
    exact sΓ
  have hs_nonzero : ¬ IsZeroAt s (ι.base z) := by
    have hiff : ¬ IsZeroAt s (ι.base z) ↔
        ι.base z ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus sΓ := by
      rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
      rfl
    exact hiff.mpr hzs
  let θ := AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι L m
  let u : Γ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m), ⊤) := by
    change (((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m)).val.obj
      (Opposite.op ⊤) : Type u)
    exact sectionPullbackAlong ι s
  let t := θ.hom.app ⊤ u
  have hzt : z ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L) m).nonvanishingLocus t := by
    dsimp [t]
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso θ]
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
    change ¬ IsZeroAt (sectionPullbackAlong ι s) z
    exact not_isZeroAt_sectionPullbackAlong ι (AlgebraicGeometry.Scheme.Modules.tensorPow L m) s z
      hs_nonzero
  have hloc : (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L) m).nonvanishingLocus t =
      ι ⁻¹ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus sΓ := by
    ext z
    change z ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L) m).nonvanishingLocus
        (θ.hom.app ⊤ u) ↔ ι.base z ∈
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus sΓ
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso θ]
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus,
      AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
    change ¬ IsZeroAt (sectionPullbackAlong ι s) z ↔ ¬ IsZeroAt s (ι.base z)
    constructor
    · intro h hz
      exact h (isZeroAt_sectionPullbackAlong_of_isZeroAt ι
        (AlgebraicGeometry.Scheme.Modules.tensorPow L m) s z hz)
    · intro h
      exact not_isZeroAt_sectionPullbackAlong ι
        (AlgebraicGeometry.Scheme.Modules.tensorPow L m) s z h
  refine ⟨m, hm, t, hzt, ?_⟩
  rw [hloc]
  exact hsa.preimage ι

end
