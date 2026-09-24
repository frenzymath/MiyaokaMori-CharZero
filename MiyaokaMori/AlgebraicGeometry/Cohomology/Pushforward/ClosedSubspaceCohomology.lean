import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.ExtAdjunctionExact
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.TopcatSheafOpenClosedFunctors
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.PushforwardClosedEmbeddingEpi

/-! # Cohomology of a closed subspace (Stacks 02UV, topological version)

Stacks 02UV (topological version): for the inclusion `i : Z → X` of a closed subspace and an abelian sheaf
`G` on `Z`, `H^p(Z, G) ≅ H^p(X, i_*G)` (`i_*` is exact and preserves injectives).

Source: Stacks 02UV (cohomology-lemma-cohomology-and-closed-immersions).

Same argument as the scheme version
`Stacks02uv.lean` (`sheafCohomologyClosedImmersionAddEquiv`), for an arbitrary closed subset of a topological space:
`H^p(X, i_*G) = Ext^p(ℤ_X, i_*G) ≃ Ext^p(i^{-1}ℤ_X, G) ≃ Ext^p(ℤ_Z, G) = H^p(Z, G)`, where
* `i^{-1} ⊣ i_*` is `TopCat.Sheaf.pullbackPushforwardAdjunction`;
* `i^{-1}` preserves finite limits by Mathlib's `Functor.sheafPullbackConstruction.preservesFiniteLimits`,
  and colimits as a left adjoint;
* `i_*` preserves finite limits as a right adjoint and epimorphisms for a closed embedding
  (Stacks 01AX), hence is exact (`Functor.preservesHomology_of_preservesEpis_and_kernels`,
  `Functor.preservesFiniteColimits_of_preservesHomology`);
* exact adjoint pairs induce `Ext` isomorphisms (`Adjunction.extAddEquiv`);
* `i^{-1}ℤ_X ≅ ℤ_Z` because both are left adjoint to global sections (`constantSheafAdj`, `i^{-1}⊤ = ⊤`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- `i_*` along a closed embedding preserves finite colimits (it is exact): it preserves finite limits as a
right adjoint and epimorphisms by Stacks 01AX. Returned as `Nonempty` so that data built from it stays free of
instance arguments (as in `Stacks02uv.lean`). -/
theorem pushforward_nonempty_preservesFiniteColimits_of_isClosedEmbedding {Z : TopCat.{u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i) :
    Nonempty (PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)) := by
  have _hepi : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).PreservesEpimorphisms :=
    TopCat.Sheaf.pushforward_preservesEpimorphisms_of_isClosedEmbedding i hi
  haveI := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).rightAdjoint_preservesLimits
  haveI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact ⟨Functor.preservesFiniteColimits_of_preservesHomology _⟩

/-- `i^{-1}` of the constant sheaf is the constant sheaf: both `constantSheaf_X ⋙ i^{-1}` and `constantSheaf_Z`
are left adjoint to `Γ(Z, −)` (`i^{-1}⊤ = ⊤`). -/
def constantSheafPullbackIso {Z : TopCat.{u}} (i : Z ⟶ X) :
    constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ≅
      constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} i :=
  Adjunction.natIsoOfRightAdjointNatIso
    (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u} isTerminalTop)
    ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i))
    (Iso.refl _)

/-- **02UV (topological), concrete form**: `H^p(Z, G) ≃+ H^p(X, i_*G)` for a closed embedding `i : Z → X`. -/
def HPushforwardAddEquiv {Z : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (p : ℕ) :
    CategoryTheory.Sheaf.H G p ≃+
      CategoryTheory.Sheaf.H (show CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} from
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) p := by
  haveI := (pushforward_nonempty_preservesFiniteColimits_of_isClosedEmbedding i hi).some
  haveI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} i) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  let e := (constantSheafPullbackIso i).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let e₁ := (((Abelian.extFunctor p).mapIso e.op).app G).addCommGroupIsoToAddEquiv
  exact e₁.symm.trans
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).extAddEquiv
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) G p)

end TopCat.Sheaf

/-- **Stacks 02UV, topological version**: `Z ⊆ X` closed, `G` an abelian sheaf on `Z`; then
`H^p(Z, G) ≃+ H^p(X, i_*G)`. Proof (see the module docstring): both sides of `i^{-1} ⊣ i_*` are exact
(`i^{-1}` by Mathlib's `sheafPullbackConstruction.preservesFiniteLimits`, `i_*` by 01AX for epimorphisms
plus preservation of limits as a right adjoint), an exact adjoint pair gives
`Ext(i^{-1}ℤ_X, G) ≃ Ext(ℤ_X, i_*G)` (`Adjunction.extAddEquiv`), and `i^{-1}ℤ_X ≅ ℤ_Z`. -/
theorem TopCat.Sheaf.H_pushforwardClosed_equiv {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (p : ℕ) :
    Nonempty (CategoryTheory.Sheaf.H G p ≃+ CategoryTheory.Sheaf.H (TopCat.Sheaf.pushforwardClosed Z G) p) :=
  ⟨TopCat.Sheaf.HPushforwardAddEquiv
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X)
    hZ.isClosedEmbedding_subtypeVal G p⟩

end
