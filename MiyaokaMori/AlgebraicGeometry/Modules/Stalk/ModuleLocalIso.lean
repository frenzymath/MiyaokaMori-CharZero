import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso

/-!
# Invertibility of a module-sheaf morphism is local

A morphism of module sheaves whose restriction to each member of an open cover is invertible
is invertible. Restriction along an open immersion commutes with stalks by Mathlib's natural
isomorphism `Scheme.Modules.restrictStalkNatIso`; its naturality transports invertibility of
the restricted morphism to bijectivity of the original stalk map, and
`moduleHom_isIso_iff_stalk_bijective` concludes.

Sources: Stacks Project, `sheaves.tex`, `lemma-points-exactness` (isomorphisms are detected on
stalks) and `modules.tex`, open restriction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X : Scheme.{u}} {M N : X.Modules}

/-- If the restriction of `φ` along an open immersion `f` is invertible, the stalk map of `φ`
at every point in the image of `f` is bijective. -/
theorem moduleStalkMap_bijective_of_restrict_isIso {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (φ : M ⟶ N) [IsIso ((Scheme.Modules.restrictFunctor f).map φ)] (y : Y) :
    Function.Bijective (moduleStalkMap X (f y) φ) := by
  have nat := (Scheme.Modules.restrictStalkNatIso f y).hom.naturality φ
  have hiso : IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).map φ) := by
    have h : (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).map φ =
        (Scheme.Modules.restrictStalkNatIso f y).inv.app M ≫
          (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf Y ⋙
            TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ ≫
          (Scheme.Modules.restrictStalkNatIso f y).hom.app N := by
      rw [nat, Iso.inv_hom_id_app_assoc]
    rw [h]
    have : IsIso ((Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ) := by
      rw [Functor.comp_map]
      infer_instance
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).map φ)

/-- Invertibility of a morphism of module sheaves can be checked on an open cover. -/
theorem moduleHom_isIso_of_locally_isIso (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) : IsIso φ := by
  rw [moduleHom_isIso_iff_stalk_bijective]
  intro x
  obtain ⟨U, hxU, hU⟩ := h x
  exact moduleStalkMap_bijective_of_restrict_isIso U.ι φ ⟨x, hxU⟩

end AlgebraicGeometry.Scheme.Modules
