import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Quasi-coherent algebras on the small affine Zariski site and their relative Spec

A **quasi-coherent `O_X`-algebra** on `X`, encoded as a presheaf of commutative rings `ring` on the small
affine Zariski site `X.AffineZariskiSite` (objects: affine opens; arrows: principal opens `D(f) ⊆ U`)
together with a structure map `unit : O_X ⟶ ring`; **quasi-coherence is a field**
`coequifibered : unit.Coequifibered` (⇔ for every affine open `U` and `f ∈ Γ(X,U)`,
`ring(D(f)) = ring(U)[1/f]`; Mathlib `coequifibered_iff_forall_isLocalizationAway`). The relative Spec
`A.relativeSpec : Over X` is the gluing of Mathlib's `Scheme.AffineZariskiSite.relativeGluingData` (the same
machinery as Mathlib's `Scheme.Hom.normalization`); the charts `A.chart U : Spec A(U) ⟶ Spec_X A` are open
immersions, `π⁻¹U = range (chart U)`, the chart squares are pullbacks, and the structure morphism is affine.
Algebra homomorphisms `AffineAlgebra.Hom` give `relativeSpec.map` contravariantly.

Design: the quasi-coherent algebras used in the paper (jet algebras `J_r(B_U, ε_U)`, `⊕ L^{-q}`, `Sym E^∨`) are
all given by "rings on affine opens compatible with localization", and sections over non-affine opens are
never needed. The encoding on the affine site makes the data fully constructive, and quasi-coherence is a
propositional field proved case by case, with no fallback branch. This agrees with Mathlib's direction:
`SmallAffineZariski.lean` describes `Coequifibered` as "quasi-coherent `𝒪ₓ`-algebras".

References: Stacks 01LL–01LQ (relative Spec); Mathlib `AlgebraicGeometry/Sites/SmallAffineZariski.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A quasi-coherent `O_X`-algebra on `X`: a presheaf of rings on the affine site + structure map +
compatibility with localization. -/
structure AffineAlgebra (X : Scheme.{u}) where
  /-- Affine open `U ↦` ring `A(U)`; principal open `D(f) ⊆ U ↦` restriction map. -/
  ring : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}
  /-- The structure map `O_X(U) → A(U)`. -/
  unit : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ ring
  /-- Quasi-coherence: `A(D(f)) = A(U)[1/f]`. -/
  coequifibered : unit.Coequifibered

namespace AffineAlgebra

variable {X : Scheme.{u}} (A : X.AffineAlgebra)

/-- The section ring on an affine open `U`. -/
abbrev sections (U : X.AffineZariskiSite) : CommRingCat.{u} := A.ring.obj (op U)

/-- The restriction map `A(V) → A(U)` (`U ≤ V`, i.e. `U` is a principal open of `V`). -/
def restrict {U V : X.AffineZariskiSite} (h : U ≤ V) : A.sections V →+* A.sections U :=
  (A.ring.map (homOfLE h).op).hom

/-- The structure map `Γ(X, U) → A(U)`. -/
def unitHom (U : X.AffineZariskiSite) : Γ(X, U.toOpens) →+* A.sections U :=
  (A.unit.app (op U)).hom

@[simp] theorem restrict_refl (U : X.AffineZariskiSite) (a : A.sections U) :
    A.restrict (le_refl U) a = a := by
  show (A.ring.map (𝟙 (op U))).hom a = a
  rw [A.ring.map_id]; rfl

theorem restrict_restrict {U V W : X.AffineZariskiSite} (hUV : U ≤ V) (hVW : V ≤ W)
    (a : A.sections W) : A.restrict hUV (A.restrict hVW a) = A.restrict (hUV.trans hVW) a := by
  show ((A.ring.map (homOfLE hVW).op) ≫ (A.ring.map (homOfLE hUV).op)).hom a = _
  rw [← A.ring.map_comp]; rfl

/-- The structure map commutes with restriction. -/
theorem restrict_unitHom {U V : X.AffineZariskiSite} (h : U ≤ V) (r : Γ(X, V.toOpens)) :
    A.restrict h (A.unitHom V r) =
      A.unitHom U ((X.presheaf.map (homOfLE (AffineZariskiSite.toOpens_mono h)).op).hom r) :=
  (congrArg (fun φ => φ.hom r) (A.unit.naturality (homOfLE h).op)).symm

/-- **Usable form of quasi-coherence**: `A(D(f))` is the localization of `A(U)` at the image of `f`. -/
theorem isLocalization_basicOpen (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) :
    letI := (A.restrict (U.basicOpen_le f)).toAlgebra
    IsLocalization.Away (A.unitHom U f) (A.sections (U.basicOpen f)) :=
  AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp A.coequifibered U f

/-- The gluing data: the `Spec A(U)` over the `U`. -/
def gluingData : (AffineZariskiSite.directedCover X).RelativeGluingData :=
  AffineZariskiSite.relativeGluingData A.coequifibered

instance gluingData_isLocallyDirected :
    (A.gluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- **The relative Spec** `Spec_X A → X`. -/
def relativeSpec : Over X := Over.mk A.gluingData.toBase

/-- The chart `Spec A(U) → Spec_X A`. -/
def chart (U : X.AffineZariskiSite) : Spec (A.sections U) ⟶ A.relativeSpec.left :=
  colimit.ι A.gluingData.functor U

instance chart_isOpenImmersion (U : X.AffineZariskiSite) : IsOpenImmersion (A.chart U) := by
  change IsOpenImmersion (colimit.ι A.gluingData.functor U)
  infer_instance

/-- The morphism from the chart to `U`: `Spec(unit)` followed by the inverse of `U ≅ Spec Γ(X,U)`. -/
def chartToOpen (U : X.AffineZariskiSite) : Spec (A.sections U) ⟶ U.toOpens.toScheme :=
  Spec.map (A.unit.app (op U)) ≫ U.2.isoSpec.inv

theorem gluingData_natTrans_app (U : X.AffineZariskiSite) :
    A.gluingData.natTrans.app U = A.chartToOpen U := rfl

@[reassoc (attr := simp)]
theorem chart_hom (U : X.AffineZariskiSite) :
    A.chart U ≫ A.relativeSpec.hom = A.chartToOpen U ≫ U.toOpens.ι := by
  change colimit.ι A.gluingData.functor U ≫ A.gluingData.toBase = _
  rw [A.gluingData.ι_toBase U]
  rfl

/-- The charts are compatible with restriction. -/
@[reassoc]
theorem map_chart {U V : X.AffineZariskiSite} (h : U ≤ V) :
    Spec.map (A.ring.map (homOfLE h).op) ≫ A.chart V = A.chart U :=
  colimit.w A.gluingData.functor (homOfLE h)

/-- `π⁻¹(U)` is the image of the chart. -/
theorem preimage_eq_opensRange (U : X.AffineZariskiSite) :
    A.relativeSpec.hom ⁻¹ᵁ U.toOpens = (A.chart U).opensRange := by
  have h := A.gluingData.toBase_preimage_eq_opensRange_ι U
  rw [← show A.gluingData.toBase ⁻¹ᵁ ((AffineZariskiSite.directedCover X).f U).opensRange =
    A.relativeSpec.hom ⁻¹ᵁ U.toOpens from by
      congr 1
      exact Scheme.Opens.opensRange_ι U.toOpens]
  exact h

/-- The chart square is a pullback (`Spec_X A` restricted to `U` is `Spec A(U)`). -/
theorem chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (A.chartToOpen U) (A.chart U) U.toOpens.ι A.relativeSpec.hom :=
  A.gluingData.isPullback_natTrans_ι_toBase U

/-- The charts are jointly surjective. -/
theorem exists_chart_mem (x : A.relativeSpec.left) :
    ∃ (U : X.AffineZariskiSite) (y : Spec (A.sections U)), A.chart U y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective A.gluingData.functor x

/-- The structure morphism of the relative Spec is affine (half of Stacks 01LQ). -/
instance relativeSpec_isAffineHom : IsAffineHom A.relativeSpec.hom := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  let V : X.AffineZariskiSite := ⟨U.1, U.2⟩
  refine ⟨V.toOpens, hU, V.2, ?_⟩
  rw [A.preimage_eq_opensRange V]
  exact isAffineOpen_opensRange (A.chart V)

/-! ## Algebra homomorphisms and functoriality -/

/-- A homomorphism of quasi-coherent algebras: a natural transformation of presheaves of rings compatible with
the structure maps. -/
@[ext] structure Hom (A B : X.AffineAlgebra) where
  app : A.ring ⟶ B.ring
  unit_app : A.unit ≫ app = B.unit

namespace Hom

variable {A} {B C : X.AffineAlgebra}

/-- The identity homomorphism. -/
@[simps] def id (A : X.AffineAlgebra) : Hom A A := ⟨𝟙 _, Category.comp_id _⟩

/-- Composition of homomorphisms. -/
@[simps] def comp (φ : Hom A B) (ψ : Hom B C) : Hom A C :=
  ⟨φ.app ≫ ψ.app, by rw [← Category.assoc, φ.unit_app, ψ.unit_app]⟩

/-- The component ring homomorphism `A(U) → B(U)`. -/
def appHom (φ : Hom A B) (U : X.AffineZariskiSite) : A.sections U →+* B.sections U :=
  (φ.app.app (op U)).hom

theorem appHom_unitHom (φ : Hom A B) (U : X.AffineZariskiSite) (r : Γ(X, U.toOpens)) :
    φ.appHom U (A.unitHom U r) = B.unitHom U r :=
  congrArg (fun α => (α.app (op U)).hom r) φ.unit_app

end Hom

instance : Category X.AffineAlgebra where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

/-- The natural transformation between charts `Spec B(U) → Spec A(U)` induced by an algebra homomorphism. -/
def specNatTrans {A B : X.AffineAlgebra} (φ : Hom A B) :
    B.gluingData.functor ⟶ A.gluingData.functor :=
  Functor.whiskerRight (NatTrans.rightOp φ.app) Scheme.Spec

theorem specNatTrans_app {A B : X.AffineAlgebra} (φ : Hom A B) (U : X.AffineZariskiSite) :
    (specNatTrans φ).app U = Spec.map (φ.app.app (op U)) := rfl

/-- Functoriality (contravariant): an algebra homomorphism `A → B` gives a morphism `Spec_X B → Spec_X A` over
`X`. -/
def relativeSpec.map {A B : X.AffineAlgebra} (φ : Hom A B) :
    B.relativeSpec.left ⟶ A.relativeSpec.left :=
  colimMap (specNatTrans φ)

@[reassoc (attr := simp)]
theorem relativeSpec.chart_map {A B : X.AffineAlgebra} (φ : Hom A B) (U : X.AffineZariskiSite) :
    B.chart U ≫ relativeSpec.map φ = Spec.map (φ.app.app (op U)) ≫ A.chart U := by
  change colimit.ι B.gluingData.functor U ≫ colimMap (specNatTrans φ) =
    (specNatTrans φ).app U ≫ colimit.ι A.gluingData.functor U
  exact ι_colimMap _ _

theorem spec_map_unit {A B : X.AffineAlgebra} (φ : Hom A B) (U : X.AffineZariskiSite) :
    Spec.map (φ.app.app (op U)) ≫ Spec.map (A.unit.app (op U)) = Spec.map (B.unit.app (op U)) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun α => α.app (op U)) φ.unit_app)

theorem specMap_chartToOpen {A B : X.AffineAlgebra} (φ : Hom A B) (U : X.AffineZariskiSite) :
    Spec.map (φ.app.app (op U)) ≫ A.chartToOpen U = B.chartToOpen U := by
  unfold chartToOpen
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun g => g ≫ U.2.isoSpec.inv) (spec_map_unit φ U))

/-- `relativeSpec.map` is a morphism over `X`. -/
@[reassoc (attr := simp)]
theorem relativeSpec.map_hom {A B : X.AffineAlgebra} (φ : Hom A B) :
    relativeSpec.map φ ≫ A.relativeSpec.hom = B.relativeSpec.hom := by
  refine colimit.hom_ext fun (U : X.AffineZariskiSite) => ?_
  change B.chart U ≫ relativeSpec.map φ ≫ A.relativeSpec.hom = B.chart U ≫ B.relativeSpec.hom
  rw [relativeSpec.chart_map_assoc, chart_hom, chart_hom, ← Category.assoc,
    specMap_chartToOpen]

/-! ## The structure sheaf itself -/

/-- `O_X` as a quasi-coherent algebra; its `relativeSpec` is `X` (Mathlib `AffineZariskiSite.isColimitCocone`). -/
@[simps] def structureSheaf (X : Scheme.{u}) : X.AffineAlgebra where
  ring := (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf
  unit := 𝟙 _
  coequifibered := .of_isIso _

/-- Every quasi-coherent algebra lies under `O_X`. -/
@[simps] def unitHomAlg : Hom (structureSheaf X) A := ⟨A.unit, Category.id_comp _⟩

end AffineAlgebra

end AlgebraicGeometry.Scheme

end
