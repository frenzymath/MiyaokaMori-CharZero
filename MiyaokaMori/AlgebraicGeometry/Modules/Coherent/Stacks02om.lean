import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModulesAssociatedPoints
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.FlatFamilyRestrictAffineBase
-- Not used by this module's proof; kept because `EulerCharZeroDimDegree` reaches
-- `AffineMorphismRelativeSpec` only through this import.
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AffineMorphismRelativeSpec
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.AnnihilatorIdealSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ClosedImmersionPullbackStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ClosedImmersionUnitIsoOfAnnihilated
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.AnnihilatorSubschemeNoEmbeddedPoints

/-! # A coherent sheaf without embedded points is pushed forward from its support (Stacks 02OM)

If `F` has no embedded associated points, then `I = ker(O_X → End(F))` defines a closed subscheme `Z`
without embedded points, and `F = i_*G` with `G` coherent on `Z`, without embedded points and
`Supp G = Z`.

Source: Stacks 02OM.

**Proof.** Let `I = Ann(F)` be the
annihilator ideal sheaf (`IdealSheafData.exists_isAnnihilatorOf`, `Stacks02omAnnihilator`), `ι : Z → X` its
closed subscheme and `G := ι^* F`.
* `G` is coherent (`isCoherent_pullback`).
* `ι_* G ≅ F` (`nonempty_pushforward_pullback_iso`, `Stacks02omUnitIso`): the unit `F → ι_* ι^* F` is an
  isomorphism because `ker(O_{X,ι z} → O_{Z,z}) = Ann(F_{ι z})` kills `F_{ι z}`
  (`IsAnnihilatorOf.smul_stalk_eq_zero`) and `Supp F = Supp I = ι(Z)` (`IsAnnihilatorOf.support_subset_range`).
* `G` has no embedded associated points and `Supp G = Z`: stalkwise `G_z ≅ F_{ι z}`
  (`isAssociatedPoint_pullback_iff`, `mem_support_pullback_iff`, `Stacks02omPullbackStalk`), `ι` is an injective
  continuous map, and `ι(Z) = Supp F`.
* `Z` has no embedded points (`IsAnnihilatorOf.subscheme_hasNoEmbeddedPoints`,
  `Stacks02omSubschemeNoEmbedded`): Stacks 02M8 on each stalk, via the local criterion for embedded points.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 02OM: a coherent sheaf `F` without embedded associated points on a locally Noetherian scheme
is `i_* G` for a coherent `G` without embedded associated points, with full support, on a closed
subscheme without embedded points. -/
theorem AlgebraicGeometry.Scheme.Modules.eq_pushforward_of_noEmbeddedPoints {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : F.HasNoEmbeddedAssociatedPoints) :
    ∃ (I : X.IdealSheafData) (G : I.subscheme.Modules),
      G.IsCoherent ∧ G.HasNoEmbeddedAssociatedPoints ∧ G.support = Set.univ ∧
      I.subscheme.HasNoEmbeddedPoints ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj G ≅ F) := by
  obtain ⟨I, hI⟩ := AlgebraicGeometry.Scheme.IdealSheafData.exists_isAnnihilatorOf F
  have hker : ∀ z : I.subscheme, ∀ a ∈ RingHom.ker (I.subschemeι.stalkMap z).hom,
      ∀ m : F.stalk (I.subschemeι.base z), a • m = 0 :=
    fun z a ha m => hI.smul_stalk_eq_zero z ha m
  refine ⟨I, (AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj F,
    AlgebraicGeometry.Scheme.Modules.isCoherent_pullback _ F, ?_, ?_,
    hI.subscheme_hasNoEmbeddedPoints hF,
    AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_pullback_iso I.subschemeι F hker
      hI.support_subset_range⟩
  · -- no embedded associated points: transport along the injective continuous map `ι`
    intro z z' hz hz' hzz'
    rw [AlgebraicGeometry.Scheme.Modules.isAssociatedPoint_pullback_iff _ F z (hker z)] at hz
    rw [AlgebraicGeometry.Scheme.Modules.isAssociatedPoint_pullback_iff _ F z' (hker z')] at hz'
    exact I.subschemeι.isClosedEmbedding.injective
      (hF _ _ hz hz' (hzz'.map I.subschemeι.base.hom.continuous))
  · -- `Supp G = Z`
    refine Set.eq_univ_of_forall fun z => ?_
    rw [AlgebraicGeometry.Scheme.Modules.mem_support_pullback_iff _ F z (hker z), ← hI.coe_support_eq,
      ← I.range_subschemeι]
    exact ⟨z, rfl⟩

end
