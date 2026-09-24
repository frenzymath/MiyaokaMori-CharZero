import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.LineBundleDualEvalIso

/-! # The pairing `contract` is an isomorphism

`eval : pr₂^*O_X(−1) ⊗ pr₂^*O_X(1) ⟶ O_{C×X}` and `contract : L ⊗ pr₂^*O_X(1) ⟶ pr₁^*A`
(`PuncturedConeIsPuncturedLineBundleContract`) are isomorphisms: the middle factor of `eval` is `pr₂^*`
applied to the evaluation isomorphism of a line bundle
`internalHomEval O_X(1) O_X : 𝓗om(O_X(1), O_X) ⊗ O_X(1) ⟶ O_X` (Stacks 01CT,
`Stacks01ct_DualEval.isIso_internalHomEval_dual`), and its two ends are `pullbackTensorObjIso.inv` and
`pullbackUnitIso.hom`; `contract` is the composite of `tensorIsoTensorObj.hom ▷ _`, the associator,
`_ ◁ eval` and the right unitor.

**Why a separate module (compile time)**: the body of `eval` places `internalHomEval O_X(1) O_X` (whose
domain is spelled `𝓗om(O_X(1), O_X) ⊗ O_X(1)`) at a position whose domain is spelled
`moduleSheafDual O_X(1) ⊗ O_X(1)`; the two are only definitionally equal, and checking this equality
(`internalHom ≡ moduleSheafDual`, both sheafifications) is expensive. Every proof that unfolds `eval` redoes
this check in the elaborator and in the kernel, so `isIso_eval` is isolated here, and the main module
`…ContractInjective` uses only its statement.

Source: Stacks 01CT; eq. (2.1) of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `e^*O_{P^N}(1)` is a line bundle (`O_{P^N}(1)` is a line bundle, and the pullback of a line bundle is a
line bundle). -/
theorem ProjectiveEmbedding.oX_one_isLineBundle {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ} (e : ProjectiveEmbedding k X N) :
    (e.oX 1).IsLineBundle :=
  have h1 : (projectiveSpaceTwist k N 1).IsLineBundle := projectiveSpaceTwist_isLineBundle k N 1
  @AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _ e.emb (projectiveSpaceTwist k N 1) h1

set_option maxHeartbeats 1000000 in
/-- The evaluation `eval : pr₂^*O_X(−1) ⊗ pr₂^*O_X(1) ⟶ O_{C×X}` is an isomorphism: its three factors are
`pullbackTensorObjIso.inv`, `pr₂^*` applied to the isomorphism `internalHomEval O_X(1) O_X` (Stacks 01CT,
`isIso_internalHomEval_unit`), and `pullbackUnitIso.hom`. -/
theorem conePuncturedLineBundle.isIso_eval {k : Type u} [Field k] (C : AlgebraicGeometry.Scheme.{u})
    {X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ} (e : ProjectiveEmbedding k X N) :
    CategoryTheory.IsIso (conePuncturedLineBundle.eval C e) := by
  have h2 := ProjectiveEmbedding.oX_one_isLineBundle e
  -- Instantiate on the scheme `X`, with the spelling `dual L`: `dual L = moduleSheafDual L` up to one unfolding.
  have hev := @AlgebraicGeometry.Scheme.Modules.isIso_internalHomEval_dual X
    (e.oX 1) h2
  unfold conePuncturedLineBundle.eval
  refine @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ (CategoryTheory.Iso.isIso_inv _) ?_
  refine @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ ?_ (CategoryTheory.Iso.isIso_hom _)
  refine @CategoryTheory.Functor.map_isIso _ _ _ _ _ _ _ _ ?_
  exact hev

/-- The pairing `contract : L ⊗ pr₂^*O_X(1) ⟶ pr₁^*A` is an isomorphism (`M ⊗ Q^∨ ⊗ Q ≅ M`):
`tensorIsoTensorObj.hom ▷ _`, the associator, `_ ◁ eval` (`isIso_eval`) and the right unitor are all
isomorphisms. -/
theorem conePuncturedLineBundle.isIso_contract {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] :
    CategoryTheory.IsIso (conePuncturedLineBundle.contract e A) := by
  have hev : CategoryTheory.IsIso (conePuncturedLineBundle.eval C e) := conePuncturedLineBundle.isIso_eval C e
  unfold conePuncturedLineBundle.contract
  exact @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _
    (@CategoryTheory.MonoidalCategory.whiskerRight_isIso _ _ _ _ _ _ _ (CategoryTheory.Iso.isIso_hom _))
    (@CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ (CategoryTheory.Iso.isIso_hom _)
      (@CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _
        (@CategoryTheory.MonoidalCategory.whiskerLeft_isIso _ _ _ _ _ _ _ hev)
        (CategoryTheory.Iso.isIso_hom _)))

end
