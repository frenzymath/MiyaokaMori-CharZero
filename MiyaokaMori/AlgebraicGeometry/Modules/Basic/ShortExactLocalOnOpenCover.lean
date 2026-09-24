import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleLocalIso

/-! # Short exactness of sheaves of modules is local on an open cover

Short exactness of a short complex of `O_X`-modules can be checked on an open cover: if the restricted
short complex is short exact on each member of an open cover, then the original short complex is short
exact (mono, epi and exactness in the middle are each checked locally; exactness of sheaves can be checked
on stalks).

References: Stacks 01AI (mono, epi and iso of sheaf morphisms are checked on stalks); Stacks 01AH / 006X
(restriction along an open immersion is exact).

## Route

Instead of "the stalk functor is exact" we use "a jointly conservative family of exact functors reflects
short exactness":

1. Abstract lemma (any abelian category): let `F_i : C ⥤ D_i` preserve finite limits and finite colimits
   (hence homology, `ShortComplex.mapHomologyIso`) and jointly reflect isomorphisms
   (`IsIso (F_i φ) ∀ i ⇒ IsIso φ`). Then
   * they jointly reflect zero objects: `Z` is zero ⟺ `0 : Z ⟶ Z` is an isomorphism, and `F_i 0 = 0` is an
     isomorphism on the zero object `F_i Z`;
   * they reflect exactness: `S` is exact ⟺ `S.homology` is zero (`exact_iff_isZero_homology`), and
     `F_i (S.homology) ≅ (S.map F_i).homology` is zero;
   * they reflect mono/epi: `Mono f` ⟺ the short complex `0 → M → N` is exact (`exact_iff_mono`), and
     similarly for epi;
   * combining, they reflect short exactness.
2. Pullback `Scheme.Modules.pullback f` along an open immersion `f` is exact: it is a left adjoint (preserves
   colimits) and is `≅ restrictFunctor f` (`restrictFunctorIsoPullback`), which is a
   `SheafOfModules.pushforward`, a right adjoint (preserves limits).
3. Joint conservativity: `φ` an isomorphism after each `pullback (𝒰.f i)` ⇒ after each
   `restrictFunctor (𝒰.f i)` ⇒ (naturality of `restrictStalkNatIso`,
   `moduleStalkMap_bijective_of_restrict_isIso`) `φ` is bijective on the stalk at every point `x = 𝒰.f i y`
   ⇒ `IsIso φ` (`moduleHom_isIso_iff_stalk_bijective`, essentially
   `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ZeroObject
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] {ι : Type w} {D : ι → Type u'} [∀ i, Category.{v'} (D i)]

/-- A family of functors preserving zero morphisms that jointly reflects isomorphisms
reflects zero objects. -/
theorem _root_.CategoryTheory.Limits.isZero_of_family [HasZeroMorphisms C]
    [∀ i, HasZeroMorphisms (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).PreservesZeroMorphisms]
    (hF : ∀ {M N : C} (φ : M ⟶ N), (∀ i, IsIso ((F i).map φ)) → IsIso φ)
    (Z : C) (hZ : ∀ i, IsZero ((F i).obj Z)) : IsZero Z := by
  have : IsIso (0 : Z ⟶ Z) := by
    apply hF
    intro i
    rw [Functor.map_zero, (hZ i).eq_of_src (0 : (F i).obj Z ⟶ (F i).obj Z) (𝟙 _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 Z = 0 ≫ inv (0 : Z ⟶ Z) := (IsIso.hom_inv_id (0 : Z ⟶ Z)).symm
    _ = 0 := zero_comp

variable [Abelian C] [∀ i, Abelian (D i)]
  (F : ∀ i, C ⥤ D i) [∀ i, (F i).PreservesZeroMorphisms]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
  (hF : ∀ {M N : C} (φ : M ⟶ N), (∀ i, IsIso ((F i).map φ)) → IsIso φ)

include hF

/-- A jointly conservative family of exact functors between abelian categories reflects
exactness of short complexes. -/
theorem exact_of_family (S : ShortComplex C) (h : ∀ i, (S.map (F i)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  apply isZero_of_family F hF
  intro i
  have hi := h i
  rw [exact_iff_isZero_homology] at hi
  exact hi.of_iso (S.mapHomologyIso (F i)).symm

/-- A jointly conservative family of exact functors between abelian categories reflects
monomorphisms. -/
theorem _root_.CategoryTheory.mono_of_family {M N : C} (f : M ⟶ N)
    (h : ∀ i, Mono ((F i).map f)) : Mono f := by
  let S : ShortComplex C := ShortComplex.mk (0 : 0 ⟶ M) f zero_comp
  have hS : S.Exact := by
    apply exact_of_family F hF
    intro i
    rw [(S.map (F i)).exact_iff_mono]
    · exact h i
    · exact Functor.map_zero _ _ _
  exact (S.exact_iff_mono rfl).1 hS

/-- A jointly conservative family of exact functors between abelian categories reflects
epimorphisms. -/
theorem _root_.CategoryTheory.epi_of_family {M N : C} (f : M ⟶ N)
    (h : ∀ i, Epi ((F i).map f)) : Epi f := by
  let S : ShortComplex C := ShortComplex.mk f (0 : N ⟶ 0) comp_zero
  have hS : S.Exact := by
    apply exact_of_family F hF
    intro i
    rw [(S.map (F i)).exact_iff_epi]
    · exact h i
    · exact Functor.map_zero _ _ _
  exact (S.exact_iff_epi rfl).1 hS

/-- A jointly conservative family of exact functors between abelian categories reflects
short exactness. -/
theorem shortExact_of_family (S : ShortComplex C) (h : ∀ i, (S.map (F i)).ShortExact) :
    S.ShortExact :=
  ShortExact.mk' (exact_of_family F hF S fun i => (h i).exact)
    (mono_of_family F hF S.f fun i => (h i).mono_f)
    (epi_of_family F hF S.g fun i => (h i).epi_g)

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction along an open immersion is a right adjoint: it is a `SheafOfModules.pushforward`
(composition with `f.opensFunctor`), whose left adjoint is extension by zero. -/
theorem restrictFunctor_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).IsRightAdjoint := by
  -- `restrictFunctor f` is by definition `SheafOfModules.pushforward` along `f.opensFunctor`.
  -- Mathlib's instance is stated for `SheafOfModules R ⥤ SheafOfModules S`; since
  -- `Scheme.Modules` is a non-reducible `def`, instance search does not see through it, so we
  -- state the instance in `SheafOfModules` form and transport it by `exact`.
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  have h : (SheafOfModules.pushforward.{u} (F := f.opensFunctor)
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (S := X.ringCatSheaf) (R := Y.ringCatSheaf)
      ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩).IsRightAdjoint := inferInstance
  exact h

/-- Restriction along an open immersion is a right adjoint, hence preserves finite limits. -/
theorem restrictFunctor_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (restrictFunctor f) :=
  have := restrictFunctor_isRightAdjoint f
  inferInstance

/-- Pullback along an open immersion preserves finite limits. -/
theorem pullback_preservesFiniteLimits_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (pullback f) :=
  have := restrictFunctor_preservesFiniteLimits f
  preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback f)

/-- Pullback of sheaves of modules is a left adjoint, hence preserves finite colimits. -/
theorem pullback_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback f) :=
  have := (pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  inferInstance

/-- Invertibility of a morphism of `𝒪_X`-modules can be checked after pullback to the members
of an open cover (Stacks 01AI: isomorphisms are detected on stalks, and pullback along an open
immersion commutes with stalks). -/
theorem isIso_of_openCover {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (𝒰 : X.OpenCover)
    (h : ∀ i, IsIso ((pullback (𝒰.f i)).map φ)) : IsIso φ := by
  rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have : IsIso ((restrictFunctor (𝒰.f (𝒰.idx x))).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback (𝒰.f (𝒰.idx x))) φ).2 (h _)
  rw [← hy]
  exact AlgebraicGeometry.Scheme.Modules.moduleStalkMap_bijective_of_restrict_isIso (𝒰.f (𝒰.idx x)) φ y

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Scheme.Modules in
/-- Short exactness of a short complex of `𝒪_X`-modules can be checked on an open cover:
apply `ShortComplex.shortExact_of_family` to the exact (`pullback_preservesFiniteLimits_of_isOpenImmersion`,
`pullback_preservesFiniteColimits`) and jointly conservative (`isIso_of_openCover`) family
`pullback (𝒰.f i)`. -/
theorem AlgebraicGeometry.Scheme.Modules.shortExact_of_openCover {X : AlgebraicGeometry.Scheme.{u}}
    (S : CategoryTheory.ShortComplex X.Modules) (𝒰 : X.OpenCover)
    (h : ∀ i, (S.map (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i))).ShortExact) :
    S.ShortExact := by
  have : ∀ i, PreservesFiniteLimits (pullback (𝒰.f i)) := fun i =>
    pullback_preservesFiniteLimits_of_isOpenImmersion (𝒰.f i)
  have : ∀ i, PreservesFiniteColimits (pullback (𝒰.f i)) := fun i =>
    pullback_preservesFiniteColimits (𝒰.f i)
  exact ShortComplex.shortExact_of_family (fun i => pullback (𝒰.f i))
    (fun φ hφ => isIso_of_openCover φ 𝒰 hφ) S h

end
