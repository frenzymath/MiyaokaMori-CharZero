import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials

/-! # Sections of the inverse image presheaf `f⁻¹O_S`

Let `f : X → S` be a morphism of schemes, `f⁻¹O_S` the inverse image presheaf of rings
(`Scheme.inverseImagePresheaf`, a left Kan extension) and `φ : f⁻¹O_S → O_X` the map
`Scheme.inverseImageStructureMap`. For an open `W ⊆ X`:
1. every element of `(f⁻¹O_S)(W)` is the image of a section `r ∈ O_S(V)` for some `V ⊇ f(W)`,
   under the adjunction unit `O_S(V) → (f⁻¹O_S)(f⁻¹V)` followed by restriction to `W`;
2. `φ_W` sends such an element to `f.appLE V W r`; hence the image of `φ_W` is the union of the
   images of the maps `f.appLE V W`;
3. consequently every `f⁻¹O_S`-derivation `D : O_X → F` satisfies `D(f.appLE V U r) = 0`, and the
   `d_app` condition of a derivation need only be checked on the elements `f.appLE V W r`.

Proof sketch. The left Kan extension is computed pointwise by colimits
(`Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit`): `(f⁻¹O_S)(W) = colim_{(V, W ≤ f⁻¹V)} O_S(V)`,
with cocone components "unit ≫ restriction". The index category
`CostructuredArrow (Opens.map f).op (op W)` is thin, nonempty (`V = ⊤`) and any two objects have
the upper bound `V₁ ⊓ V₂`, so it is filtered; the forgetful functor of `CommRingCat` preserves
filtered colimits, so every element of the colimit comes from a component
(`Concrete.isColimit_exists_rep`). The formula `unit_V ≫ φ_{f⁻¹V} = f.app V` is the `homEquiv_unit`
of the adjunction; naturality of `φ` and `f.appLE = f.app ≫ res` give (2), and (3) follows from
`d_map` and `d_app`.

Reference: Stacks 008C (the colimit description of the inverse image presheaf).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- The index category `{V ⊆ S open | W ⊆ f⁻¹V}ᵒᵖ` is filtered. -/
instance Scheme.isFiltered_costructuredArrow_opensMap {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens) :
    IsFiltered (CostructuredArrow (Opens.map f.base).op (op W)) := by
  have : ∀ (a b : CostructuredArrow (Opens.map f.base).op (op W)), Subsingleton (a ⟶ b) :=
    fun a b => ⟨fun p q => by ext; exact Subsingleton.elim _ _⟩
  have : Nonempty (CostructuredArrow (Opens.map f.base).op (op W)) :=
    ⟨CostructuredArrow.mk (Y := op ⊤) (homOfLE (by exact le_top)).op⟩
  refine { cocone_objs := fun a b => ?_, cocone_maps := fun a b p q => ⟨b, 𝟙 _, Subsingleton.elim _ _⟩ }
  have ha : W ≤ f ⁻¹ᵁ a.left.unop := a.hom.unop.le
  have hb : W ≤ f ⁻¹ᵁ b.left.unop := b.hom.unop.le
  refine ⟨CostructuredArrow.mk (Y := op (a.left.unop ⊓ b.left.unop))
    (homOfLE (by exact le_inf ha hb)).op, ?_, ?_, trivial⟩
  · exact CostructuredArrow.homMk (homOfLE inf_le_left).op (Subsingleton.elim _ _)
  · exact CostructuredArrow.homMk (homOfLE inf_le_right).op (Subsingleton.elim _ _)

/-- Every element of `(f⁻¹O_S)(W)` comes from some `O_S(V)` with `W ⊆ f⁻¹V`. -/
theorem Scheme.inverseImagePresheaf_exists_rep {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens)
    (s : (Scheme.inverseImagePresheaf f).obj (op W)) :
    ∃ (V : S.Opens) (e : W ≤ f ⁻¹ᵁ V) (r : Γ(S, V)),
      s = ((Scheme.inverseImagePresheaf f).map (homOfLE e).op).hom
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
          S.presheaf).app (op V)).hom r) := by
  have hc := (Opens.map f.base).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit S.presheaf (op W)
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _ hc s
  refine ⟨j.left.unop, j.hom.unop.le, y, ?_⟩
  rw [← hy]
  rfl

/-- The adjunction unit followed by `f⁻¹O_S ⟶ O_X` is `f.app`:
`O_S(V) → (f⁻¹O_S)(f⁻¹V) → O_X(f⁻¹V)`. -/
theorem Scheme.inverseImageStructureMap_unit {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app S.presheaf).app (op V) ≫
      (Scheme.inverseImageStructureMap f).app (op (f ⁻¹ᵁ V)) = f.app V := by
  have := (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv_unit
    (X := S.presheaf) (Y := X.presheaf) (f := Scheme.inverseImageStructureMap f)
  have h2 : ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _)
      (Scheme.inverseImageStructureMap f) = f.c := by
    simp [Scheme.inverseImageStructureMap]
  rw [h2] at this
  exact (congrArg (fun t => t.app (op V)) this).symm

/-- `f.appLE` factors through `f⁻¹O_S`. -/
theorem Scheme.appLE_eq_inverseImageStructureMap {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    (f.appLE V U e).hom r =
      ((Scheme.inverseImageStructureMap f).app (op U)).hom
        (((Scheme.inverseImagePresheaf f).map (homOfLE e).op).hom
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
            S.presheaf).app (op V)).hom r)) := by
  have h := (Scheme.inverseImageStructureMap f).naturality (homOfLE e).op
  rw [Scheme.Hom.appLE, ← Scheme.inverseImageStructureMap_unit]
  exact (congrArg (fun t => t.hom
    ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
      S.presheaf).app (op V)).hom r)) h).symm

/-- The image of `φ_W` consists of the images of the maps `f.appLE`. -/
theorem Scheme.inverseImageStructureMap_app_eq_appLE {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens)
    (s : (Scheme.inverseImagePresheaf f).obj (op W)) :
    ∃ (V : S.Opens) (e : W ≤ f ⁻¹ᵁ V) (r : Γ(S, V)),
      ((Scheme.inverseImageStructureMap f).app (op W)).hom s = (f.appLE V W e).hom r := by
  obtain ⟨V, e, r, rfl⟩ := Scheme.inverseImagePresheaf_exists_rep f W s
  exact ⟨V, e, r, (Scheme.appLE_eq_inverseImageStructureMap f V W e r).symm⟩

/-- An `f⁻¹O_S`-derivation kills the image of `f.appLE`: for `U ⊆ f⁻¹V`, `D(f^♯ r) = 0`. -/
theorem Omega.derivation_appLE {X S : Scheme.{u}} (f : X ⟶ S)
    {F : X.Modules} (D : (F.val).Derivation' (Scheme.inverseImageStructureMap f))
    (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    D.d (X := op U) ((f.appLE V U e).hom r) = 0 := by
  rw [Scheme.appLE_eq_inverseImageStructureMap]
  exact PresheafOfModules.Derivation'.d_app D _

end AlgebraicGeometry
