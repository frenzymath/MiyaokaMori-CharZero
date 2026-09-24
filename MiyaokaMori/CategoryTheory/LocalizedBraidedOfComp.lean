import MiyaokaMori.Prelude

/-! # A functor out of a monoidal localization is braided if its lift is

The braided version of `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`.

Mathlib (`CategoryTheory/Localization/Monoidal/Functor.lean`) shows: if `L : C ⥤ D` is a monoidal
localization functor and `F : D ⥤ E` lifts along `L` to a monoidal functor `G : C ⥤ E`
(`Lifting L W G F`), then `F` is monoidal (`functorMonoidalOfComp`). It does not contain the braided
version: if `G` is braided, so is `F`. This file provides `functorBraidedOfComp`, together with two
independently usable lemmas:

| declaration | content |
| --- | --- |
| `braided_of_iso` | the braiding compatibility `μ ≫ F(β) = β ≫ μ` transported along isomorphisms of objects in both variables |
| `comp_braided_aux` | `L ⋙ F ≅ G` (monoidal natural isomorphism) and `G` braided ⟹ `L ⋙ F` braided |
| `functorBraidedOfComp_braided` | the braiding compatibility of `F` (checked on the image of `L`, then transported to all objects using that `L` is essentially surjective) |
| `functorBraidedOfComp` | `F.Braided` |

Proof outline (two short steps):

1. **On the image of `L`.** Since `Lifting.iso L W G F : L ⋙ F ≅ G` is a monoidal natural isomorphism
   (`lifting_isMonoidal`) and `G` is braided, `L ⋙ F` is braided by `Functor.LaxBraided.ofNatIso`.
   Substitute `μ (L ⋙ F) = μ F ∘ F(μ L)` (`comp_μ`), replace `μ L ≫ L(β)` using the braiding
   compatibility of `L` itself, and cancel the isomorphism `F (μ L)` (`L` is strong monoidal, so `μ L`
   is invertible).
2. **All objects.** `L.IsLocalization W ⟹ L.EssSurj`, so every `X : D` is isomorphic to
   `L (L.objPreimage X)`; the braiding compatibility transports along isomorphisms of objects
   (`braided_of_iso`, using only the naturality of `μ` and of the braiding).

Implementation remark: the `toLaxMonoidal` inside the `(L ⋙ F).LaxBraided` produced by
`Functor.LaxBraided.ofNatIso` and `Functor.LaxMonoidal.comp` are definitionally equal but
**syntactically different** instance paths, so a direct `rw [comp_μ]` fails. Hence the braiding
compatibility of `L ⋙ F` is stated separately as `comp_braided_aux`, whose **statement** is elaborated
without the local `LaxBraided` instance (so it uses the composite instance), and the proof term is
connected by definitional unfolding.

Also, `[L.Monoidal]` and `[L.Braided]` cannot both be instance arguments (`Braided extends Monoidal`
gives two conflicting `LaxMonoidal` paths, flagged by the `overlappingInstances` linter); only
`[L.Braided]` is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

noncomputable section

namespace CategoryTheory.Localization.Monoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]

/-- The braiding compatibility transported along isomorphisms in both variables. -/
theorem braided_of_iso (F : D ⥤ E) [F.LaxMonoidal] {X Y X' Y' : D} (a : X ≅ X') (b : Y ≅ Y')
    (h : LaxMonoidal.μ F X' Y' ≫ F.map (β_ X' Y').hom =
      (β_ (F.obj X') (F.obj Y')).hom ≫ LaxMonoidal.μ F Y' X') :
    LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ LaxMonoidal.μ F Y X := by
  have hβ : (β_ X Y).hom = (a.hom ⊗ₘ b.hom) ≫ (β_ X' Y').hom ≫ (b.inv ⊗ₘ a.inv) := by
    rw [BraidedCategory.braiding_naturality_assoc]
    simp
  rw [hβ, F.map_comp, F.map_comp]
  rw [← LaxMonoidal.μ_natural_assoc, reassoc_of% h,
    BraidedCategory.braiding_naturality_assoc, LaxMonoidal.μ_natural_assoc, ← F.map_comp]
  simp

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Braided]
  (F : D ⥤ E) (G : C ⥤ E) [G.Braided] [W.ContainsIdentities] [Lifting L W G F]

/-- If `L ⋙ F ≅ G` is a monoidal natural isomorphism and `G` is braided, then `L ⋙ F` is braided. The
statement is phrased with the **composite** `LaxMonoidal` instance, so that `comp_μ` applies downstream
without instance-path mismatches. -/
theorem comp_braided_aux (X₀ Y₀ : C) :
    letI := functorMonoidalOfComp L W F G
    LaxMonoidal.μ (L ⋙ F) X₀ Y₀ ≫ (L ⋙ F).map (β_ X₀ Y₀).hom =
      (β_ ((L ⋙ F).obj X₀) ((L ⋙ F).obj Y₀)).hom ≫ LaxMonoidal.μ (L ⋙ F) Y₀ X₀ := by
  let := functorMonoidalOfComp L W F G
  have : NatTrans.IsMonoidal (Lifting.iso L W G F).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (Lifting.iso L W G F).inv)
  exact (Functor.LaxBraided.ofNatIso (Lifting.iso L W G F).symm).braided X₀ Y₀

/-- The braiding compatibility for `functorMonoidalOfComp`. -/
theorem functorBraidedOfComp_braided (X Y : D) :
    letI := functorMonoidalOfComp L W F G
    LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ LaxMonoidal.μ F Y X := by
  let := functorMonoidalOfComp L W F G
  have := Localization.essSurj L W
  refine braided_of_iso F (L.objObjPreimageIso X).symm (L.objObjPreimageIso Y).symm ?_
  have hb := comp_braided_aux L W F G (L.objPreimage X) (L.objPreimage Y)
  rw [LaxMonoidal.comp_μ, LaxMonoidal.comp_μ] at hb
  have hL := Functor.LaxBraided.braided (F := L) (L.objPreimage X) (L.objPreimage Y)
  rw [Category.assoc, show (L ⋙ F).map (β_ (L.objPreimage X) (L.objPreimage Y)).hom
      = F.map (L.map (β_ (L.objPreimage X) (L.objPreimage Y)).hom) from rfl,
    ← F.map_comp, hL, F.map_comp, ← Category.assoc, ← Category.assoc] at hb
  have : IsIso (F.map (LaxMonoidal.μ L (L.objPreimage Y) (L.objPreimage X))) := by
    have : IsIso (LaxMonoidal.μ L (L.objPreimage Y) (L.objPreimage X)) := inferInstance
    infer_instance
  exact (cancel_mono (F.map (LaxMonoidal.μ L (L.objPreimage Y) (L.objPreimage X)))).mp hb

/-- If `F` lifts along the monoidal localization functor `L` to a braided functor `G`, then `F` itself
(with the monoidal structure `functorMonoidalOfComp`) is braided. -/
@[instance_reducible]
noncomputable def functorBraidedOfComp :
    letI := functorMonoidalOfComp L W F G
    F.Braided :=
  letI := functorMonoidalOfComp L W F G
  { toMonoidal := functorMonoidalOfComp L W F G
    braided := functorBraidedOfComp_braided L W F G }

end CategoryTheory.Localization.Monoidal

end
