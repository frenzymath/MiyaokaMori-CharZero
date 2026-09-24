import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AffineAlgebra
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Pushforward algebras of affine morphisms and pullback of affine algebras

Two constructions.

1. **The pushforward algebra of an affine morphism**
   `AffineAlgebra.ofAffineHom (p : W ⟶ T) [IsAffineHom p] : T.AffineAlgebra`: on an affine open
   `U ↦ Γ(W, p⁻¹U)`, structure map `p.app U`, quasi-coherence because `p⁻¹U` is affine and
   `p⁻¹(D_U(f)) = D_{p⁻¹U}(p^♯f)` (Mathlib `IsAffineOpen.isLocalization_of_eq_basicOpen`).
   This is the algebraic side of Stacks 01S5 ("affine morphisms = relative Specs"), entirely
   constructive.

2. **The pullback of a quasi-coherent algebra along an arbitrary morphism**
   `AffineAlgebra.pullback (A : X.AffineAlgebra) (g : T ⟶ X) : T.AffineAlgebra :=
   ofAffineHom (pullback.snd A.relativeSpec.hom g)`: `A.relativeSpec.hom` is an affine morphism
   (`relativeSpec_isAffineHom`), `IsAffineHom` is stable under base change (Mathlib
   `isAffineHom_isStableUnderBaseChange`), so the base change `T ×_X Spec_X A ⟶ T` is affine and we
   take its pushforward algebra. Defined for arbitrary `g`.

Why not define the pullback by tensor products on affine opens: algebras are encoded as presheaves of
rings on the **small affine Zariski site**, and `T.AffineZariskiSite` contains **all** affine opens of `T`.
The natural formula `(g^*A)(V) = A(U) ⊗_{Γ(X,U)} Γ(T,V)` (`V ⊆ g⁻¹U`) only makes sense when `V` lies in some
`g⁻¹U`; for general `g` (e.g. `π : A¹_X → X` with `X` non-separated) there are affine opens `V ⊆ T` whose
image is contained in no affine open `U ⊆ X`, so the open-by-open formula is undefined, and a choice
`V ↦ U(V)` has no monotonicity (no restriction maps). The geometric side has no such problem: the base
change always exists, affineness is preserved by base change, `Γ(W, p⁻¹V)` is defined for **every** affine
open `V`, and quasi-coherence is exactly "`p` affine".

The geometric side of 01S5, `ofAffineHom_relativeSpec_iso` (`Spec_T (p_*O_W) ≅ W`), and the base-change
compatibility `pullback_relativeSpec_iso` derived from it are proved at the end of this file.

References: Stacks 01S5 (affine morphisms and relative Specs), 01SD (base change).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.AffineAlgebra

variable {T W : Scheme.{u}}

/-- **The pushforward algebra** `p_*O_W` **of an affine morphism.** -/
def ofAffineHom (p : W ⟶ T) [IsAffineHom p] : T.AffineAlgebra where
  ring := (AffineZariskiSite.toOpensFunctor T).op ⋙ (p.base _* W.presheaf)
  unit := Functor.whiskerLeft (AffineZariskiSite.toOpensFunctor T).op p.c
  coequifibered := by
    rw [AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
    intro U f
    exact (U.2.preimage p).isLocalization_of_eq_basicOpen (p.app U.toOpens f)
      ((Opens.map p.base).map (homOfLE (AffineZariskiSite.toOpens_mono (U.basicOpen_le f))))
      (Scheme.preimage_basicOpen p f)

@[simp] theorem ofAffineHom_sections (p : W ⟶ T) [IsAffineHom p] (U : T.AffineZariskiSite) :
    (ofAffineHom p).sections U = Γ(W, p ⁻¹ᵁ U.toOpens) := rfl

@[simp] theorem ofAffineHom_unitHom (p : W ⟶ T) [IsAffineHom p] (U : T.AffineZariskiSite)
    (r : Γ(T, U.toOpens)) : (ofAffineHom p).unitHom U r = (p.app U.toOpens) r := rfl

theorem ofAffineHom_restrict (p : W ⟶ T) [IsAffineHom p] {U V : T.AffineZariskiSite} (h : U ≤ V)
    (a : Γ(W, p ⁻¹ᵁ V.toOpens)) :
    (ofAffineHom p).restrict h a =
      (W.presheaf.map ((Opens.map p.base).map
        (homOfLE (AffineZariskiSite.toOpens_mono h))).op).hom a := rfl

/-- The pushforward along the identity is the structure sheaf algebra. -/
theorem ofAffineHom_id : ofAffineHom (𝟙 T) = structureSheaf T := rfl

variable {X : Scheme.{u}}

instance pullback_isAffineHom (A : X.AffineAlgebra) (g : T ⟶ X) :
    IsAffineHom (Limits.pullback.snd A.relativeSpec.hom g) :=
  AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback _ _) inferInstance

/-- **The pullback of a quasi-coherent algebra along an arbitrary morphism `g : T ⟶ X`**: the pushforward
algebra of the base change `T ×_X Spec_X A ⟶ T`. -/
def pullback (A : X.AffineAlgebra) (g : T ⟶ X) : T.AffineAlgebra :=
  ofAffineHom (Limits.pullback.snd A.relativeSpec.hom g)

@[simp] theorem pullback_sections (A : X.AffineAlgebra) (g : T ⟶ X) (V : T.AffineZariskiSite) :
    (A.pullback g).sections V =
      Γ(Limits.pullback A.relativeSpec.hom g,
        Limits.pullback.snd A.relativeSpec.hom g ⁻¹ᵁ V.toOpens) := rfl


/-! ## Geometric half of Stacks 01S5: the comparison morphism `Spec_T (p_*O_W) ⟶ W`

Source: Stacks 01S5 (morphisms-lemma-affine-equivalence-algebras), 01SA. The argument (the data form
`ofAffineHom.relativeSpecIso` lives in `OfAffineHomRelativeSpecIso.lean`, which imports this file):
the charts `Spec Γ(W, p⁻¹U)` of `Spec_T(p_*O_W)` map to `W` by `IsAffineOpen.fromSpec`
(`p⁻¹U` is affine since `p` is), compatibly with restriction (`IsAffineOpen.map_fromSpec`);
gluing gives `c : Spec_T(p_*O_W) ⟶ W` over `T` (`SpecMap_appLE_fromSpec`). Over each affine
`U ⊆ T`, the chart square is a pullback (`AffineAlgebra.chart_isPullback`), the square
`p⁻¹U → U` is a pullback (`isPullback_morphismRestrict`), so by pasting `c` is, over `p⁻¹U`,
the isomorphism `isoSpec.inv`. Isomorphisms are local on the target, so `c` is an isomorphism.
-/

section RelativeSpecIso

set_option backward.isDefEq.respectTransparency false

variable (p : W ⟶ T) [IsAffineHom p]

namespace ofAffineHom

/-- The chart `Spec Γ(W, p⁻¹U)` maps to `W` via `fromSpec` of the affine open `p⁻¹U`. -/
def toSource (U : T.AffineZariskiSite) : Spec ((ofAffineHom p).sections U) ⟶ W :=
  (U.2.preimage p).fromSpec

theorem map_toSource {U V : T.AffineZariskiSite} (h : U ≤ V) :
    Spec.map ((ofAffineHom p).ring.map (homOfLE h).op) ≫ toSource p V = toSource p U :=
  IsAffineOpen.map_fromSpec (V.2.preimage p) (U.2.preimage p)
    ((Opens.map p.base).map (homOfLE (AffineZariskiSite.toOpens_mono h))).op

/-- The cocone on the gluing diagram of `Spec_T(p_*O_W)` with vertex `W`. -/
def toSourceCocone : Cocone (ofAffineHom p).gluingData.functor where
  pt := W
  ι :=
    { app := toSource p
      naturality := fun U V g => by
        change Spec.map ((ofAffineHom p).ring.map g.op) ≫ toSource p V = toSource p U ≫ 𝟙 W
        rw [Category.comp_id]
        exact map_toSource p (leOfHom g) }

/-- The canonical morphism `Spec_T(p_*O_W) ⟶ W`. -/
def toSourceHom : (ofAffineHom p).relativeSpec.left ⟶ W :=
  colimit.desc _ (toSourceCocone p)

@[reassoc (attr := simp)]
theorem chart_toSourceHom (U : T.AffineZariskiSite) :
    (ofAffineHom p).chart U ≫ toSourceHom p = (U.2.preimage p).fromSpec :=
  colimit.ι_desc (toSourceCocone p) U

/-- `Spec.map (p.app U) ≫ fromSpec_U = fromSpec_{p⁻¹U} ≫ p`. -/
theorem specMap_app_fromSpec (U : T.AffineZariskiSite) :
    Spec.map (p.app U.toOpens) ≫ U.2.fromSpec = (U.2.preimage p).fromSpec ≫ p := by
  rw [Scheme.Hom.app_eq_appLE]
  exact IsAffineOpen.SpecMap_appLE_fromSpec p U.2 (U.2.preimage p) le_rfl

/-- `chartToOpen U` factors through the restriction `p ∣_ U`. -/
theorem chartToOpen_eq (U : T.AffineZariskiSite) :
    (ofAffineHom p).chartToOpen U = (U.2.preimage p).isoSpec.inv ≫ (p ∣_ U.toOpens) := by
  rw [← cancel_mono U.toOpens.ι]
  change Spec.map (p.app U.toOpens) ≫ U.2.isoSpec.inv ≫ U.toOpens.ι = _
  rw [IsAffineOpen.isoSpec_inv_ι, Category.assoc, morphismRestrict_ι,
    IsAffineOpen.isoSpec_inv_ι_assoc]
  exact specMap_app_fromSpec p U

/-- `toSourceHom` is a morphism over `T`. -/
@[reassoc (attr := simp)]
theorem toSourceHom_comp : toSourceHom p ≫ p = (ofAffineHom p).relativeSpec.hom := by
  refine colimit.hom_ext fun (U : T.AffineZariskiSite) => ?_
  change (ofAffineHom p).chart U ≫ toSourceHom p ≫ p = (ofAffineHom p).chart U ≫ _
  rw [chart_toSourceHom_assoc, chart_hom, chartToOpen_eq, Category.assoc, morphismRestrict_ι,
    IsAffineOpen.isoSpec_inv_ι_assoc]

/-- Over the affine open `p⁻¹U ⊆ W`, `toSourceHom` restricts to the chart square. -/
theorem isPullback_chart (U : T.AffineZariskiSite) :
    IsPullback (U.2.preimage p).isoSpec.inv ((ofAffineHom p).chart U) (p ⁻¹ᵁ U.toOpens).ι
      (toSourceHom p) := by
  have s := (ofAffineHom p).chart_isPullback U
  rw [chartToOpen_eq, ← toSourceHom_comp] at s
  exact IsPullback.of_right s
    (by rw [IsAffineOpen.isoSpec_inv_ι, chart_toSourceHom])
    (isPullback_morphismRestrict p U.toOpens)

/-- The affine opens `p⁻¹U` (`U ⊆ T` affine) cover `W`. -/
def preimageCover : W.OpenCover :=
  Cover.mkOfCovers T.AffineZariskiSite (fun U => (p ⁻¹ᵁ U.toOpens).toScheme)
    (fun U => (p ⁻¹ᵁ U.toOpens).ι) fun x => by
      obtain ⟨U, hU⟩ := Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top T).ge (Set.mem_univ (p.base x)))
      exact ⟨⟨U.1, U.2⟩, ⟨x, hU⟩, rfl⟩

/-- `toSourceHom` is an isomorphism: isomorphisms are Zariski-local on the target, and over each
`p⁻¹U` the base change of `toSourceHom` is `isoSpec.inv` (`isPullback_chart`). Stated as a theorem
(not a global instance): use `have := toSourceHom_isIso p` where needed. -/
theorem toSourceHom_isIso : IsIso (toSourceHom p) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover (preimageCover p) fun U => ?_
  rw [MorphismProperty.isomorphisms.iff]
  have h := (isPullback_chart p U).flip.isoIsPullback_inv_snd _ _
    (IsPullback.of_hasPullback (toSourceHom p) (p ⁻¹ᵁ U.toOpens).ι)
  change IsIso (pullback.snd (toSourceHom p) (p ⁻¹ᵁ U.toOpens).ι)
  rw [← h]
  infer_instance

end ofAffineHom

end RelativeSpecIso

/-- The relative Spec of the pushforward algebra is the source (geometric form). This is the content of
**Stacks 01S5**: an affine morphism `p` and its pushforward algebra are relative Specs of each other.
Proof: `ofAffineHom.toSourceHom p : Spec_T(p_*O_W) ⟶ W` is a morphism over `T` (`toSourceHom_comp`) and an
isomorphism (`toSourceHom_isIso`: chart by chart via `chart_isPullback` and `IsAffineOpen.isoSpec`;
being an isomorphism is Zariski-local on the target). The data form `ofAffineHom.relativeSpecIso` is in
`OfAffineHomRelativeSpecIso.lean`. -/
theorem ofAffineHom_relativeSpec_iso (p : W ⟶ T) [IsAffineHom p] :
    Nonempty ((ofAffineHom p).relativeSpec ≅ Over.mk p) :=
  have := ofAffineHom.toSourceHom_isIso p
  ⟨Over.isoMk (asIso (ofAffineHom.toSourceHom p)) (ofAffineHom.toSourceHom_comp p)⟩

/-- Base-change compatibility, from the previous result: `Spec_T (g^*A) ≅ T ×_X Spec_X A` (the pullback
square over `X`). -/
theorem pullback_relativeSpec_iso (A : X.AffineAlgebra) (g : T ⟶ X) :
    Nonempty ((A.pullback g).relativeSpec ≅
      Over.mk (Limits.pullback.snd A.relativeSpec.hom g)) :=
  ofAffineHom_relativeSpec_iso _

end AlgebraicGeometry.Scheme.AffineAlgebra

end
