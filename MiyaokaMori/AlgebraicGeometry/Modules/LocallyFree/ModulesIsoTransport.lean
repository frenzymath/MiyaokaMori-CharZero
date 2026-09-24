import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # Transport of properties of sheaves of modules along isomorphisms

Users of the determinant and rank additivity of short exact sequences have three vector bundles
`F G H` and isomorphisms `eF : F.toModules ≅ S.X₁` etc., while
`AlgebraicGeometry.Scheme.Modules.rankAtStalk_add_of_shortExact` assumes
`[S.X₁.IsLocallyFree] [S.X₁.IsFiniteType]`. This file states the three transports along isomorphisms
as named lemmas.

References: Stacks 01BZ / 01CC (locally free and finite type are local properties, hence preserved
under isomorphisms); the rank at a stalk is `rankAtStalk` (`VectorBundleRank`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Auxiliary lemma: push a family of generating sections `σ` of `M|_U` along the restriction
`e.hom|_U` of an isomorphism `e : M ≅ N` (`SheafOfModules.GeneratingSections.ofEpi`); if
`σ.π : free σ.I ⟶ M|_U` is an isomorphism, so is the `π` of the new family: by `ofEpi_π` it equals
`σ.π ≫ e.hom|_U`, a composite of isomorphisms.

(Stated separately because, written inside the structure fields of `isLocallyFree_of_iso`, the defeq
check between `(q'.generators i).π` and `((q.generators i).ofEpi _).π` exhausts the heartbeats.) -/
theorem AlgebraicGeometry.Scheme.Modules.isIso_ofEpi_π_over {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (σ : (M.over U).GeneratingSections)
    [IsIso σ.π] :
    haveI : IsIso (e.hom.over U) := Iso.isIso_hom ((SheafOfModules.overFunctor _ U).mapIso e)
    IsIso (σ.ofEpi (e.hom.over U)).π := by
  have : IsIso (e.hom.over U) := Iso.isIso_hom ((SheafOfModules.overFunctor _ U).mapIso e)
  have h : (σ.ofEpi (e.hom.over U)).π = σ.π ≫ e.hom.over U :=
    SheafOfModules.GeneratingSections.ofEpi_π σ (e.hom.over U)
  have h2 : IsIso (σ.π ≫ e.hom.over U) := inferInstance
  exact h ▸ h2

/-- Local freeness is preserved under isomorphisms of sheaves of modules.

Proof: `SheafOfModules.IsLocallyFree M` unfolds to "there is local generators data
`q : M.LocalGeneratorsData` with `q.IsLocallyFreeData`", where local generators data consists of
opens `Uᵢ`, index types and morphisms `free Iᵢ ⟶ M|_{Uᵢ}`, and `IsLocallyFreeData` says these are
isomorphisms. Given `e : M ≅ N`, composing each `free Iᵢ ⟶ M|_{Uᵢ}` with the restriction `e.hom|_{Uᵢ}`
gives local generators data for `N`; composites of isomorphisms are isomorphisms
(`IsIso.comp_isIso`), so it satisfies `IsLocallyFreeData`. -/
theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_iso {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) (hM : M.IsLocallyFree) : N.IsLocallyFree := by
  obtain ⟨q, hq⟩ := hM.exists_isLocallyFreeData
  -- `e.hom.over U = (overFunctor _ U).map e.hom` is an isomorphism, hence an epimorphism
  have hiso : ∀ i, IsIso (e.hom.over (q.X i)) := fun i =>
    Iso.isIso_hom ((SheafOfModules.overFunctor _ (q.X i)).mapIso e)
  -- local generators of `N`: those of `M`, pushed forward along `e.hom|_{Uᵢ}`
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i => (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have hq' : q'.IsLocallyFreeData :=
    { isIso := fun i =>
        haveI : IsIso (q.generators i).π := hq.isIso i
        AlgebraicGeometry.Scheme.Modules.isIso_ofEpi_π_over e (q.X i) (q.generators i) }
  -- (the anonymous constructor `⟨⟨q', hq'⟩⟩` mis-elaborates the universes here; spell out the field)
  exact { exists_isLocallyFreeData := ⟨q', hq'⟩ }

/-- Finite type is preserved under isomorphisms of sheaves of modules.

Proof: `SheafOfModules.IsFiniteType N` says there is local generators data `σ : N.LocalGeneratorsData`
(opens `Uᵢ` and generating sections of `N|_{Uᵢ}`) with finite index types (`σ.IsFiniteType`). Given
`e : M ≅ N`, push each family of generating sections of `M` along `e.hom|_{Uᵢ}`
(`GeneratingSections.ofEpi`; an isomorphism is an epimorphism): generation means the induced
`free Iᵢ ⟶ N|_{Uᵢ}` is an epimorphism, and it equals `(free Iᵢ ⟶ M|_{Uᵢ}) ≫ e.hom|_{Uᵢ}`, a composite
of epimorphisms; the index types are unchanged, so finiteness is unchanged. -/
theorem AlgebraicGeometry.Scheme.Modules.isFiniteType_of_iso {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) (hM : M.IsFiniteType) : N.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := hM.exists_localGeneratorsData
  have hiso : ∀ i, IsIso (e.hom.over (σ.X i)) := fun i =>
    Iso.isIso_hom ((SheafOfModules.overFunctor _ (σ.X i)).mapIso e)
  -- local generators of `N`: those of `M`, pushed forward along `e.hom|_{Uᵢ}`; same index types
  let σ' : N.LocalGeneratorsData :=
    { I := σ.I
      X := σ.X
      coversTop := σ.coversTop
      generators := fun i => (σ.generators i).ofEpi (e.hom.over (σ.X i)) }
  have hσ' : σ'.IsFiniteType :=
    { isFiniteType := fun i => by
        have : (σ.generators i).IsFiniteType := hσ.isFiniteType i
        show ((σ.generators i).ofEpi (e.hom.over (σ.X i))).IsFiniteType
        infer_instance }
  -- (the anonymous constructor `⟨⟨σ', hσ'⟩⟩` mis-elaborates the universes here; spell out the field)
  exact { exists_localGeneratorsData := ⟨σ', hσ'⟩ }

/-- The rank at a stalk is preserved under isomorphisms of sheaves of modules.

Proof: `rankAtStalk E x = finrank κ(x) (κ(x) ⊗_{O_{X,x}} E_x)`. An isomorphism `e : M ≅ N` gives,
through the stalk functor `AlgebraicGeometry.Scheme.Modules.stalkFunctor x`, an `O_{X,x}`-linear
isomorphism `M_x ≅ N_x`; tensoring with `κ(x)` gives a `κ(x)`-linear isomorphism
`κ(x) ⊗ M_x ≅ κ(x) ⊗ N_x` (`TensorProduct.congr` with the identity on the left), and
`Module.finrank` is invariant under linear isomorphisms (`LinearEquiv.finrank_eq`). -/
theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_iso {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk M x =
      AlgebraicGeometry.Scheme.Modules.rankAtStalk N x := by
  unfold AlgebraicGeometry.Scheme.Modules.rankAtStalk
  let _ := (X.residue x).hom.toAlgebra
  -- the stalk functor sends `e` to an `O_{X,x}`-linear isomorphism `M_x ≃ N_x`
  let φ : M.stalk x ≃ₗ[X.presheaf.stalk x] N.stalk x :=
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).mapIso e).toLinearEquiv
  -- base change to `κ(x)` and compare dimensions
  exact LinearEquiv.finrank_eq (φ.baseChange (X.presheaf.stalk x) (X.residueField x) _ _)

end
