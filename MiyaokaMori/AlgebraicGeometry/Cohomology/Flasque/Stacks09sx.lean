import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule

/-! # Injective sheaves are flasque (Stacks 09SX)

Stacks 09SX: injective sheaves are flasque (for abelian sheaves; and the underlying abelian sheaf of an
injective `O_X`-module on a scheme is flasque).

Proof (abelian sheaves, valid on any site `C`): let `ℤ[h_U]^#` be the sheafification of the free abelian
presheaf on the representable presheaf `h_U`.
1. Three adjunctions (sheafification, whiskered free abelian group adjunction, Yoneda) give a natural
   bijection `Hom(ℤ[h_U]^#, F) ≃ F(U)`, with
   `sectionsEquiv V F (freeSheafMap (J := J) m ≫ φ) = F(m)(sectionsEquiv U F φ)` for `m : V ⟶ U`.
2. `m` mono ⇒ `ℤ[h_V]^# → ℤ[h_U]^#` mono: `h_V(W) → h_U(W)` is injective on each object (`cancel_mono`),
   the free abelian group functor preserves monomorphisms (Mathlib
   `AddCommGrpCat.free.PreservesMonomorphisms`), a pointwise mono of presheaves is a mono, and
   sheafification preserves finite limits, hence monos.
3. `F` injective: `s ∈ F(V)` corresponds to `φ : ℤ[h_V]^# → F`, which extends along the monomorphism above
   to `ψ : ℤ[h_U]^# → F`, whose section restricts back to `s`. On the site of opens of a topological space
   every `V ≤ U` is a monomorphism (thin category), so `F(U) → F(V)` is surjective, i.e. `F` is flasque.

The module version (`AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective`) is the same construction
with `ℤ[h_U]^#` replaced by `j_!(O_U)` := the sheafification of the presheaf of modules
`(free O_X).obj (h_U)` (Mathlib `PresheafOfModules.free` + `PresheafOfModules.sheafification`):
`Hom(j_!(O_U), M) ≃ Γ(M, U)` from the sheafification adjunction for modules and Mathlib's
`PresheafOfModules.freeYonedaEquiv` (naturality `freeYonedaEquiv_map` proved here); the monomorphism
`j_!(O_V) ↪ j_!(O_U)` comes from `Finsupp.mapDomain` along an injection being injective
(`Finsupp.mapDomain_injective`), `PresheafOfModules.mono_of_injective`, and sheafification of modules
preserving finite limits.

Source: Stacks 09SX (cohomology-lemma-injective-flasque) = a reformulation of 01EA; Hartshorne III.2.4.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks09sxAux

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}]

/-- `ℤ[h_U]^#`: the sheafification of the free abelian presheaf on a representable presheaf. -/
abbrev freeSheaf (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}] (U : C) :
    Sheaf J AddCommGrpCat.{u} :=
  (presheafToSheaf J AddCommGrpCat.{u}).obj
    (((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free).obj (yoneda.obj U))

/-- `m : V ⟶ U` induces `ℤ[h_V]^# ⟶ ℤ[h_U]^#`. -/
def freeSheafMap {V U : C} (m : V ⟶ U) : freeSheaf J V ⟶ freeSheaf J U :=
  (presheafToSheaf J AddCommGrpCat.{u}).map
    (((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free).map (yoneda.map m))

/-- `Hom(ℤ[h_U]^#, F) ≃ F(U)` (composite of three adjunctions). -/
def sectionsEquiv (U : C) (F : Sheaf J AddCommGrpCat.{u}) :
    (freeSheaf J U ⟶ F) ≃ ((F.obj ⋙ forget AddCommGrpCat.{u}).obj (op U)) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _).trans
    (((AddCommGrpCat.adj.{u}.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj).trans yonedaEquiv)

/-- (Contravariant) naturality of the bijection in `U`. -/
theorem sectionsEquiv_map {V U : C} (m : V ⟶ U) (F : Sheaf J AddCommGrpCat.{u})
    (φ : freeSheaf J U ⟶ F) :
    sectionsEquiv V F (freeSheafMap (J := J) m ≫ φ) =
      (F.obj ⋙ forget AddCommGrpCat.{u}).map m.op (sectionsEquiv U F φ) := by
  show yonedaEquiv ((AddCommGrpCat.adj.{u}.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) F.obj
      ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _ (freeSheafMap (J := J) m ≫ φ))) = _
  rw [freeSheafMap, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    ← yonedaEquiv_naturality]
  rfl

/-- `m` mono ⇒ `ℤ[h_V]^# ⟶ ℤ[h_U]^#` mono. -/
instance freeSheafMap_mono {V U : C} (m : V ⟶ U) [Mono m] : Mono (freeSheafMap (J := J) m) := by
  have h0 : ∀ W : Cᵒᵖ, Mono ((yoneda.map m).app W) := by
    intro W
    rw [CategoryTheory.mono_iff_injective]
    intro a b hab
    exact (cancel_mono m).1 hab
  have h1 : Mono (((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free).map
      (yoneda.map m)) := by
    have h2 : ∀ W : Cᵒᵖ, Mono (AddCommGrpCat.free.map ((yoneda.map m).app W)) :=
      fun W => have := h0 W; AddCommGrpCat.free.map_mono ((yoneda.map m).app W)
    exact NatTrans.mono_of_mono_app _
  exact (presheafToSheaf J AddCommGrpCat.{u}).map_mono _

/-- The restriction maps on sections of an injective sheaf along monomorphisms are surjective. -/
theorem surjective_of_injective (F : Sheaf J AddCommGrpCat.{u}) [Injective F] {V U : C}
    (m : V ⟶ U) [Mono m] :
    Function.Surjective ((F.obj ⋙ forget AddCommGrpCat.{u}).map m.op) := by
  intro s
  obtain ⟨ψ, hψ⟩ := Injective.factors ((sectionsEquiv V F).symm s) (freeSheafMap m)
  refine ⟨sectionsEquiv U F ψ, ?_⟩
  rw [← sectionsEquiv_map m F ψ, hψ, Equiv.apply_symm_apply]

end Stacks09sxAux

namespace Stacks09sxModAux

open AlgebraicGeometry PresheafOfModules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The `O_X`-module version `j_!(O_U)`: the sheafification of the free presheaf of modules `R ⊗ ℤ[h_U]`. -/
abbrev freeModSheaf (U : X.Opens) : SheafOfModules.{u} X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))

/-- `V ≤ U` induces `j_!(O_V) ⟶ j_!(O_U)`. -/
def freeModSheafMap {V U : X.Opens} (h : V ⟶ U) : freeModSheaf V ⟶ freeModSheaf U :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map h))

/-- Naturality of `freeYonedaEquiv` in the second variable (the object of the site). -/
theorem freeYonedaEquiv_map {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M : PresheafOfModules.{u} R} {V U : C} (m : V ⟶ U)
    (ψ : (PresheafOfModules.free R).obj (yoneda.obj U) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv ((PresheafOfModules.free R).map (yoneda.map m) ≫ ψ) =
      M.map m.op (PresheafOfModules.freeYonedaEquiv ψ) := by
  show ((PresheafOfModules.free R).map (yoneda.map m) ≫ ψ).app (op V) (ModuleCat.freeMk (𝟙 V)) =
    M.map m.op (ψ.app (op U) (ModuleCat.freeMk (𝟙 U)))
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply ψ m.op (ModuleCat.freeMk (𝟙 U)))
  simp
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) (congrArg _ ?_)
  refine Eq.trans (ModuleCat.free_map_apply _ _) ?_
  show _ = (PresheafOfModules.freeObj (R := R) (yoneda.obj U)).map m.op (ModuleCat.freeMk (𝟙 U))
  rw [PresheafOfModules.freeObj_map]
  refine Eq.trans ?_ (ModuleCat.freeDesc_apply _ (𝟙 U)).symm
  simp
  show ModuleCat.freeMk m = ModuleCat.freeMk (m ≫ 𝟙 U)
  rw [Category.comp_id]

/-- `Hom(j_!(O_U), M) ≃ Γ(M, U)`. -/
def sectionsEquivMod (U : X.Opens) (M : SheafOfModules.{u} X.ringCatSheaf) :
    (freeModSheaf U ⟶ M) ≃
      (((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj M).obj (op U)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).trans
    PresheafOfModules.freeYonedaEquiv

/-- (Contravariant) naturality of the above bijection in `U`. -/
theorem sectionsEquivMod_map {V U : X.Opens} (h : V ⟶ U) (M : SheafOfModules.{u} X.ringCatSheaf)
    (φ : freeModSheaf U ⟶ M) :
    sectionsEquivMod V M (freeModSheafMap h ≫ φ) =
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj M).map h.op
        (sectionsEquivMod U M φ) := by
  show PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _
      (freeModSheafMap h ≫ φ)) = _
  rw [freeModSheafMap, Adjunction.homEquiv_naturality_left, freeYonedaEquiv_map]
  rfl

/-- `V ≤ U` ⇒ `j_!(O_V) ⟶ j_!(O_U)` is a monomorphism. -/
instance freeModSheafMap_mono {V U : X.Opens} (h : V ⟶ U) : Mono (freeModSheafMap h) := by
  have h1 : Mono ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map h)) := by
    apply PresheafOfModules.mono_of_injective
    intro W a b hab
    have hinj : Function.Injective ((yoneda.map h).app W) := fun x y _ =>
      Subsingleton.elim (α := (W.unop ⟶ V)) x y
    exact Finsupp.mapDomain_injective hinj hab
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_mono _

/-- The restriction maps on sections of an injective `O_X`-module are surjective. -/
theorem sections_surjective_of_injective (I : SheafOfModules.{u} X.ringCatSheaf)
    [CategoryTheory.Injective I] {V U : X.Opens} (h : V ⟶ U) :
    Function.Surjective
      (((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj I).map h.op) := by
  intro s
  obtain ⟨ψ, hψ⟩ := CategoryTheory.Injective.factors ((sectionsEquivMod V I).symm s)
    (freeModSheafMap h)
  refine ⟨sectionsEquivMod U I ψ, ?_⟩
  rw [← sectionsEquivMod_map h I ψ, hψ]
  exact (sectionsEquivMod V I).apply_symm_apply s

end Stacks09sxModAux

/-- Stacks 09SX: injective sheaves are flasque. The abelian sheaf version (the ringed space with
`O_X = ℤ`); the `O_X`-module version on a scheme follows below. -/

theorem TopCat.Sheaf.isFlasque_of_injective {X : TopCat.{u}}
    (I : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [CategoryTheory.Injective I] : TopCat.Sheaf.IsFlasque I where
  epi {U V} i := by
    have hmono : Mono i.unop := ⟨fun {W} g h _ => Subsingleton.elim g h⟩
    rw [AddCommGrpCat.epi_iff_surjective]
    have hsurj := Stacks09sxAux.surjective_of_injective I i.unop
    intro s
    obtain ⟨t, ht⟩ := hsurj s
    exact ⟨t, ht⟩

theorem AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.Modules) [CategoryTheory.Injective I] :
    TopCat.Sheaf.IsFlasque I.toAddCommGrpSheaf where
  epi {U V} i := by
    have hinj : CategoryTheory.Injective (C := SheafOfModules.{u} X.ringCatSheaf) I := ‹_›
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    obtain ⟨t, ht⟩ := Stacks09sxModAux.sections_surjective_of_injective
      (X := X) (I := I) i.unop s
    exact ⟨t, ht⟩

end
