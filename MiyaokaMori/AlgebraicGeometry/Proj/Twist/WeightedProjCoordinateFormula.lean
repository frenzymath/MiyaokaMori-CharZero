import MiyaokaMori.AlgebraicGeometry.Proj.Twist.WeightedProjTwisting
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Coordinate frames for the actual weighted Proj twist

A homogeneous element `g` of degree `d` trivializes the existing twist on any
open on which `g` does not vanish. The inverse frame sends `r` to `r * g`.
The forward frame divides the localization-valued section by `g`: locally a
shifted fraction `a / c` becomes the same-degree fraction `a / (c * g)`.

The construction uses `ProjTwisting.sheaf`, the existing Proj structure sheaf,
and the actual scalar restriction along the open immersion. Empty opens and zero
coefficient rings require no exception or nontriviality assumption.

Sources: Stacks Project, `constructions.tex`, `lemma-proj-sheaves`,
`definition-twist`, and `lemma-when-invertible`; §2 of the paper (the Veronese polarization,
Lemma 2.2). Global gluing, the Veronese
comparison, and relative very ampleness remain separate obligations.

## Structure

The only mathematical input is `isFrame_homogeneousSection`: `g` is a frame of `O(d)` on `U` (`Scheme.Modules.IsFrame`).
The isomorphism `homogeneousCoordinateFrameIso` and all its formulas are produced by the general `IsFrame.restrictIso`
API. Two rules are observed throughout this file (both dictated by measured kernel times):

1. Carrier conversions of the kind "sections of the restricted sheaf ↔ sections on the image open" are done only in
   the general lemmas about a **variable** `M`. For the concrete `sheaf 𝒜 d`, every such conversion with both sides of
   the form `ModuleCat.carrier (…)` costs the kernel 5–6 s.
2. When a statement at the concrete level uses a section of the twisting sheaf as a section of the restricted sheaf,
   write `show sectionsSubmodule … from …` (going through the normal form, under 0.1 s); the weighted level only
   instantiates the abstract lemmas, without new reasoning.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open SetLike.GradedMonoid

universe u v t w

namespace MiyaokaMori.WeightedJets

namespace ProjTwisting

-- The division and multiplication lemmas rely on this option to recognize `↑(ProjectiveSpectrum.top 𝒜)` as
-- `ProjectiveSpectrum 𝒜` when synthesizing the `IsPrime` instance (removing it produces an error). It only affects the
-- elaborator, not kernel time.
set_option backward.isDefEq.respectTransparency false

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Dividing a shifted homogeneous fraction by a nonvanishing homogeneous element
gives an actual same-degree homogeneous fraction. -/
theorem isFraction_divide_lift (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    {s : ∀ x : U, Fiber 𝒜 x.1} (hs : IsFraction 𝒜 (d : ℤ) s) :
    ∃ r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal,
      ProjectiveSpectrum.StructureSheaf.IsFraction r ∧
        ∀ x : U, (r x).val = s x * Localization.mk 1 ⟨g, hU x⟩ := by
  rcases hs with rfl | ⟨p, q, a, c, hpq, hc, hs⟩
  · refine ⟨0, ⟨0, ⟨0, zero_mem _⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩,
      fun x ↦ x.1.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, fun _ ↦ rfl⟩, ?_⟩
    intro x
    simp only [Pi.zero_apply, HomogeneousLocalization.val_zero, zero_mul]
  · have he : q + d = p := by omega
    let den : 𝒜 p := ⟨c.1 * g, he ▸ SetLike.mul_mem_graded c.2 hg⟩
    have hden (x : U) : den.1 ∉ x.1.asHomogeneousIdeal :=
      x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hc x) (hU x)
    refine ⟨fun x ↦ HomogeneousLocalization.mk ⟨p, a, den, hden x⟩,
      ⟨p, a, den, hden, fun _ ↦ rfl⟩, ?_⟩
    intro x
    change (HomogeneousLocalization.mk ⟨p, a, den, hden x⟩).val = _
    simp only [HomogeneousLocalization.val_mk, hs, Localization.mk_mul, mul_one]
    congr 1

/-- Each value of a locally shifted fraction, after division, lies in the same
homogeneous localization used by the structure sheaf. -/
theorem exists_divideValue (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (s : sectionsSubmodule 𝒜 (d : ℤ) U) (x : U) :
    ∃ r : HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal,
      r.val = s.1 x * Localization.mk 1 ⟨g, hU x⟩ := by
  obtain ⟨V, hx, i, hs⟩ := s.2 x
  obtain ⟨r, _, hr⟩ := isFraction_divide_lift 𝒜 d g hg (fun y ↦ hU (i y)) hs
  exact ⟨r ⟨x.1, hx⟩, hr ⟨x.1, hx⟩⟩

/-- The degree-zero localization value of the quotient by the specified homogeneous element. -/
def divideValue (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (s : sectionsSubmodule 𝒜 (d : ℤ) U) (x : U) :
    HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal :=
  (exists_divideValue 𝒜 d g hg hU s x).choose

/-- The chosen homogeneous-localization representative is the actual quotient
in the ordinary localization. -/
theorem divideValue_val (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (s : sectionsSubmodule 𝒜 (d : ℤ) U) (x : U) :
    (divideValue 𝒜 d g hg hU s x).val = s.1 x * Localization.mk 1 ⟨g, hU x⟩ :=
  (exists_divideValue 𝒜 d g hg hU s x).choose_spec

/-- Division gives a section of the existing structure sheaf, with its local fraction witnesses. -/
def divideSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (s : sectionsSubmodule 𝒜 (d : ℤ) U) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U) := by
  refine ⟨divideValue 𝒜 d g hg hU s, ?_⟩
  intro x
  obtain ⟨V, hx, i, hs⟩ := s.2 x
  obtain ⟨r, hr, hval⟩ := isFraction_divide_lift 𝒜 d g hg (fun y ↦ hU (i y)) hs
  refine ⟨V, hx, i, ?_⟩
  have he : (fun y : V ↦ divideValue 𝒜 d g hg hU s (i y)) = r := by
    funext y
    apply HomogeneousLocalization.val_injective
    exact (divideValue_val 𝒜 d g hg hU s (i y)).trans (hval y).symm
  change ProjectiveSpectrum.StructureSheaf.IsFraction
    (fun y : V ↦ divideValue 𝒜 d g hg hU s (i y))
  rw [he]
  exact hr

/-- Evaluation of the actual structure-sheaf quotient section. -/
theorem divideSection_val (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (s : sectionsSubmodule 𝒜 (d : ℤ) U) (x : U) :
    ((divideSection 𝒜 d g hg hU s).1 x).val =
      s.1 x * Localization.mk 1 ⟨g, hU x⟩ :=
  divideValue_val 𝒜 d g hg hU s x

/-- Multiplication by the specified homogeneous section is linear over the actual section ring. -/
def multiplySection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U) →ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)]
        sectionsSubmodule 𝒜 (d : ℤ) U :=
  LinearMap.toSpanSingleton _ _ (homogeneousSection 𝒜 d g hg U)

/-- The inverse frame multiplies localization values by the actual homogeneous element. -/
theorem multiplySection_val (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) (x : U) :
    (multiplySection 𝒜 d g hg U r).1 x = (r.1 x).val * Localization.mk g 1 := rfl

/-- A nonvanishing homogeneous element and its displayed fraction inverse multiply to one. -/
theorem fiber_coordinate_mul_inverse (g : A) (x : ProjectiveSpectrum 𝒜)
    (hx : g ∉ x.asHomogeneousIdeal) :
    (Localization.mk g 1 : Fiber 𝒜 x) * Localization.mk 1 ⟨g, hx⟩ = 1 := by
  rw [Localization.mk_mul, mul_one, one_mul]
  exact Localization.mk_self ⟨g, hx⟩

/-- Multiplying the quotient by the coordinate recovers the original twist section. -/
theorem multiplySection_divideSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (s : sectionsSubmodule 𝒜 (d : ℤ) U) :
    multiplySection 𝒜 d g hg U (divideSection 𝒜 d g hg hU s) = s := by
  apply Subtype.ext
  funext x
  rw [multiplySection_val, divideSection_val, mul_assoc,
    mul_comm (Localization.mk 1 _), fiber_coordinate_mul_inverse, mul_one]

/-- Dividing a multiple of the coordinate recovers the original structure-sheaf section. -/
theorem divideSection_multiplySection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    divideSection 𝒜 d g hg hU (multiplySection 𝒜 d g hg U r) = r := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rw [divideSection_val, multiplySection_val, mul_assoc,
    fiber_coordinate_mul_inverse, mul_one]

/-- The actual section-ring linear equivalence given by multiplication and division. -/
def homogeneousFrameSectionEquiv (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U) ≃ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)]
        sectionsSubmodule 𝒜 (d : ℤ) U :=
  { multiplySection 𝒜 d g hg U with
    invFun := divideSection 𝒜 d g hg hU
    left_inv := divideSection_multiplySection 𝒜 d g hg hU
    right_inv := multiplySection_divideSection 𝒜 d g hg hU }

/-- The frame identifies the unit section with the specified homogeneous section. -/
theorem homogeneousFrameSectionEquiv_one (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    homogeneousFrameSectionEquiv 𝒜 d g hg hU 1 = homogeneousSection 𝒜 d g hg U :=
  LinearMap.toSpanSingleton_apply_one _ _ _

/-- Division sends the specified homogeneous section to the actual unit of the section ring. -/
theorem homogeneousFrameSectionEquiv_symm_section (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    (homogeneousFrameSectionEquiv 𝒜 d g hg hU).symm
      (homogeneousSection 𝒜 d g hg U) = 1 := by
  rw [← homogeneousFrameSectionEquiv_one 𝒜 d g hg hU]
  exact (homogeneousFrameSectionEquiv 𝒜 d g hg hU).symm_apply_apply 1

/-- The component frame is compatible with actual restriction of sections. -/
theorem multiplySection_restrict (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U V : Opens (ProjectiveSpectrum.top 𝒜)} (i : V ⟶ U)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    (presheaf 𝒜 (d : ℤ)).map i.op (multiplySection 𝒜 d g hg U r) =
      multiplySection 𝒜 d g hg V
        ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.map i.op r) := rfl

/-- Restricting the quotient gives the quotient of the restricted twist section. -/
theorem divideSection_restrict (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U V : Opens (ProjectiveSpectrum.top 𝒜)} (i : V ⟶ U)
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (hV : ∀ x : V, g ∉ x.1.asHomogeneousIdeal)
    (s : sectionsSubmodule 𝒜 (d : ℤ) U) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.map i.op
        (divideSection 𝒜 d g hg hU s) =
      divideSection 𝒜 d g hg hV ((presheaf 𝒜 (d : ℤ)).map i.op s) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  exact (divideSection_val 𝒜 d g hg hU s (i x)).trans
    (divideSection_val 𝒜 d g hg hV ((presheaf 𝒜 (d : ℤ)).map i.op s) x).symm

open AlgebraicGeometry.Scheme.Modules in
/-- A homogeneous element `g` is a frame of `O(d)` on an open `U` where it vanishes nowhere: `r ↦ r • g` is bijective on
every open subset of `U` (the inverse is `divideSection`). This is the only "mathematical input" of this file; the
isomorphism and the formulas below are all produced by the general `IsFrame` API (`ModuleSheafFrame`). -/
theorem isFrame_homogeneousSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    IsFrame (sheaf 𝒜 (d : ℤ)) U (homogeneousSection 𝒜 d g hg U) := by
  intro W' h
  exact (homogeneousFrameSectionEquiv 𝒜 d g hg
    (fun x : W' ↦ hU ⟨x.1, h x.2⟩)).bijective

open AlgebraicGeometry.Scheme.Modules in
/-- Taking coordinates with respect to this frame is division by `g`. -/
theorem coord_homogeneousSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    {W' : (Proj 𝒜).Opens} (h : W' ≤ U) (s : sectionsSubmodule 𝒜 (d : ℤ) W') :
    (isFrame_homogeneousSection 𝒜 d g hg U hU).coord h s =
      divideSection 𝒜 d g hg (fun x : W' ↦ hU ⟨x.1, h x.2⟩) s := by
  apply IsFrame.coord_unique
  exact multiplySection_divideSection 𝒜 d g hg _ s

/-- Division by the specified homogeneous element trivializes the same twist on the open.

The body is the general `IsFrame.restrictIso`. Downstream uses this isomorphism only through the characterizing lemmas
`_hom_app` / `_inv_app` below; its inverse comes from `asIso` and **cannot** be seen through with `rfl` / `change`. -/
def homogeneousCoordinateFrameIso (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    (sheaf 𝒜 (d : ℤ)).restrict U.ι ≅
      SheafOfModules.unit (R := U.toScheme.ringCatSheaf) :=
  (isFrame_homogeneousSection 𝒜 d g hg U hU).restrictIso

/-- On each subopen, the forward map is division followed by the actual structure-ring appIso. -/
theorem homogeneousCoordinateFrameIso_hom_app (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (V : U.toScheme.Opens) (s : ((sheaf 𝒜 (d : ℤ)).restrict U.ι).val.obj (op V)) :
    (homogeneousCoordinateFrameIso 𝒜 d g hg U hU).hom.val.app (op V) s =
      (U.ι.appIso V).hom (divideSection 𝒜 d g hg
        (fun x : U.ι ''ᵁ V ↦ hU ⟨x.1, U.ι_image_le V x.2⟩) s) :=
  ((isFrame_homogeneousSection 𝒜 d g hg U hU).restrictIso_hom_app V s).trans
    (congrArg (U.ι.appIso V).hom
      (coord_homogeneousSection 𝒜 d g hg U hU (Scheme.Modules.image_ι_le U V) s))

/-- The same formula in the `Hom.app` / `restrictAppIso` spelling that consumers' goals carry
(`HomogeneousTupleTwistPullback`): the forward frame of a restricted section is its quotient by `g`. -/
theorem homogeneousCoordinateFrameIso_hom_app_restrictAppIso_inv (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (V : U.toScheme.Opens) (t : sectionsSubmodule 𝒜 (d : ℤ) (U.ι ''ᵁ V)) :
    (homogeneousCoordinateFrameIso 𝒜 d g hg U hU).hom.app V
        (((sheaf 𝒜 (d : ℤ)).restrictAppIso U.ι V).inv t) =
      (U.ι.appIso V).hom (divideSection 𝒜 d g hg
        (fun x : U.ι ''ᵁ V ↦ hU ⟨x.1, U.ι_image_le V x.2⟩) t) :=
  ((isFrame_homogeneousSection 𝒜 d g hg U hU).restrictIso_hom_app_restrictAppIso_inv V t).trans
    (congrArg (U.ι.appIso V).hom
      (coord_homogeneousSection 𝒜 d g hg U hU (Scheme.Modules.image_ι_le U V) t))

/-- The forward frame of a **global** homogeneous section, restricted to the chart: divide on any
open `V'` containing the chart where `g` is invertible, then restrict. -/
theorem homogeneousCoordinateFrameIso_hom_app_top_homogeneousSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (a : A) (ha : a ∈ 𝒜 d) {V' : (Proj 𝒜).Opens}
    (hV' : ∀ x : V', g ∉ x.1.asHomogeneousIdeal) (hUV : U.ι ''ᵁ ⊤ ≤ V') :
    (homogeneousCoordinateFrameIso 𝒜 d g hg U hU).hom.app ⊤
        (((sheaf 𝒜 (d : ℤ)).restrictAppIso U.ι ⊤).inv
          ((sheaf 𝒜 (d : ℤ)).presheaf.map
            (homOfLE (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top)).op
            (homogeneousSection 𝒜 d a ha ⊤))) =
      (U.ι.appIso ⊤).hom ((Proj 𝒜).presheaf.map (homOfLE hUV).op
        (divideSection 𝒜 d g hg hV' (homogeneousSection 𝒜 d a ha V'))) := by
  refine (homogeneousCoordinateFrameIso_hom_app_restrictAppIso_inv 𝒜 d g hg U hU ⊤
    (homogeneousSection 𝒜 d a ha (U.ι ''ᵁ ⊤))).trans ?_
  exact congrArg (U.ι.appIso ⊤).hom
    (divideSection_restrict 𝒜 d g hg (homOfLE hUV) hV' _ (homogeneousSection 𝒜 d a ha V')).symm

/-- Bridge form of the previous lemma for instantiation at a **concrete** graded ring: the
consumer's named constants (its copy `P` of the twist, its frame `e`, its restricted section `x`,
its quotient `r`) enter as variables tied by equations that are discharged by top-level `rfl`, so the
instance is syntactically the consumer's statement. -/
theorem homogeneousCoordinateFrameIso_hom_app_top_of_eq (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (a : A) (ha : a ∈ 𝒜 d) {V' : (Proj 𝒜).Opens}
    (hV' : ∀ x : V', g ∉ x.1.asHomogeneousIdeal) (hUV : U.ι ''ᵁ ⊤ ≤ V')
    {P : (Proj 𝒜).Modules} (hP : sheaf 𝒜 (d : ℤ) = P)
    (e : P.restrict U.ι ≅ SheafOfModules.unit (R := U.toScheme.ringCatSheaf))
    (he : e = hP ▸ homogeneousCoordinateFrameIso 𝒜 d g hg U hU)
    (x : Γ(P.restrict U.ι, ⊤))
    (hx : x = (P.restrictAppIso U.ι ⊤).inv
      (P.presheaf.map (homOfLE (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top)).op
        (hP ▸ homogeneousSection 𝒜 d a ha ⊤)))
    (r : Γ(Proj 𝒜, V')) (hr : divideSection 𝒜 d g hg hV' (homogeneousSection 𝒜 d a ha V') = r) :
    e.hom.app ⊤ x = (U.ι.appIso ⊤).hom ((Proj 𝒜).presheaf.map (homOfLE hUV).op r) := by
  subst hP
  have he' : e = homogeneousCoordinateFrameIso 𝒜 d g hg U hU := he
  subst he'; subst hx; subst hr
  exact homogeneousCoordinateFrameIso_hom_app_top_homogeneousSection 𝒜 d g hg U hU a ha hV' hUV

/-- The inverse frame transports the scalar through appIso and multiplies by the same section. -/
theorem homogeneousCoordinateFrameIso_inv_app (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (V : U.toScheme.Opens) (r : Γ(U.toScheme, V)) :
    (homogeneousCoordinateFrameIso 𝒜 d g hg U hU).inv.val.app (op V) r =
      multiplySection 𝒜 d g hg (U.ι ''ᵁ V) ((U.ι.appIso V).inv r) :=
  (isFrame_homogeneousSection 𝒜 d g hg U hU).restrictIso_inv_app V r

/-- The forward frame sends the distinguished homogeneous section to one.

The section is written `show sectionsSubmodule … from …`: using it directly as a section of the restricted sheaf makes
the kernel pay one carrier conversion of about 5 s under a common head; going through the normal form is almost free.
If the downstream goal is spelled without the `show`, `exact` with this lemma still closes it (one β/ζ step). -/
theorem homogeneousCoordinateFrameIso_hom_section (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (V : U.toScheme.Opens) :
    (homogeneousCoordinateFrameIso 𝒜 d g hg U hU).hom.val.app (op V)
      (show sectionsSubmodule 𝒜 (d : ℤ) (U.ι ''ᵁ V) from
        homogeneousSection 𝒜 d g hg (U.ι ''ᵁ V)) = (1 : Γ(U.toScheme, V)) :=
  (isFrame_homogeneousSection 𝒜 d g hg U hU).restrictIso_hom_app_frame V

/-- Pointwise value of the forward frame: the fraction `s` divided by `g`. -/
theorem homogeneousCoordinateFrameIso_hom_val (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (V : U.toScheme.Opens) (s : ((sheaf 𝒜 (d : ℤ)).restrict U.ι).val.obj (op V))
    (x : U.ι ''ᵁ V) :
    (((U.ι.appIso V).inv
      ((homogeneousCoordinateFrameIso 𝒜 d g hg U hU).hom.val.app (op V) s)).1 x).val =
      s.1 x * Localization.mk 1 ⟨g, hU ⟨x.1, U.ι_image_le V x.2⟩⟩ := by
  have happ := homogeneousCoordinateFrameIso_hom_app 𝒜 d g hg U hU V s
  have hi := (U.ι.appIso V).hom_inv_id_apply (divideSection 𝒜 d g hg
    (fun y : U.ι ''ᵁ V ↦ hU ⟨y.1, U.ι_image_le V y.2⟩) s)
  have h1 := (congrArg (U.ι.appIso V).inv happ).trans hi
  exact (congrArg (fun z => (z.1 x).val) h1).trans
    (divideSection_val 𝒜 d g hg (fun y : U.ι ''ᵁ V ↦ hU ⟨y.1, U.ι_image_le V y.2⟩) s x)

/-- Pointwise value of the inverse frame: the transported scalar times `g`. -/
theorem homogeneousCoordinateFrameIso_inv_val (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (V : U.toScheme.Opens) (r : Γ(U.toScheme, V)) (x : U.ι ''ᵁ V) :
    ((homogeneousCoordinateFrameIso 𝒜 d g hg U hU).inv.val.app (op V) r).1 x =
      (((U.ι.appIso V).inv r).1 x).val * Localization.mk g 1 :=
  congrArg (fun z : sectionsSubmodule 𝒜 (d : ℤ) (U.ι ''ᵁ V) => z.1 x)
    (homogeneousCoordinateFrameIso_inv_app 𝒜 d g hg U hU V r)

end ProjTwisting

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable (R : Type u) [CommRing R] {ι : Type t} (w : ι → ℕ+)

/-- The specified common-degree coordinate power is nonvanishing on its actual coordinate chart. -/
theorem weightedCoordinatePower_not_mem (b : ℕ) (hb : 0 < b) (i : ι)
    (hi : (w i : ℕ) ∣ b) (x : weightedCoordinateOpen R w i) :
    weightedCoordinatePower R w b i ∉ x.1.asHomogeneousIdeal := by
  have hx : x.1 ∈ Proj.basicOpen (weightedPolynomialGrading R w)
      (weightedCoordinatePower R w b i) := by
    rw [weightedCoordinatePower_basicOpen R w b hb i hi]
    exact x.2
  exact hx

/-!
The weighted concrete level: every statement is a **pure instantiation** of an abstract lemma. Here the graded ring and
the `GradedRing` instance are concrete, so a kernel comparison under a common head can unfold all the way in; do not
carry out any new reasoning at this level.
-/

/-- The coordinate power `X_i^(b/w_i)` is a frame of `O(b)` on the coordinate chart `D₊(X_i)`. -/
theorem isFrame_weightedCoordinateTwistingSection (b : ℕ) (hb : 0 < b)
    (hw : ∀ i, (w i : ℕ) ∣ b) (i : ι) :
    Scheme.Modules.IsFrame (weightedProjTwisting R w (b : ℤ)) (weightedCoordinateOpen R w i)
      (weightedCoordinateTwistingSection R w b i (hw i) (weightedCoordinateOpen R w i)) :=
  ProjTwisting.isFrame_homogeneousSection (weightedPolynomialGrading R w) b
    (weightedCoordinatePower R w b i) (weightedCoordinatePower_mem R w b i (hw i))
    (weightedCoordinateOpen R w i) (weightedCoordinatePower_not_mem R w b hb i (hw i))

/-- The actual coordinate frame on O(b), sending the specified coordinate power to one. -/
def weightedProjCoordinateFrameIso (b : ℕ) (hb : 0 < b)
    (hw : ∀ i, (w i : ℕ) ∣ b) (i : ι) :
    (weightedProjTwisting R w (b : ℤ)).restrict (weightedCoordinateOpen R w i).ι ≅
      SheafOfModules.unit (R := (weightedCoordinateOpen R w i).toScheme.ringCatSheaf) :=
  ProjTwisting.homogeneousCoordinateFrameIso (weightedPolynomialGrading R w) b
    (weightedCoordinatePower R w b i) (weightedCoordinatePower_mem R w b i (hw i))
    (weightedCoordinateOpen R w i) (weightedCoordinatePower_not_mem R w b hb i (hw i))

/-- A common positive multiple of the coordinate weights gives a twist trivial on every standard
coordinate chart (Stacks, `lemma-when-invertible`). This is the proved form of the local
triviality of `O(b)`. -/
theorem weightedProjTwisting_coordinate_trivial (b : ℕ) (hb : 0 < b)
    (hw : ∀ i, (w i : ℕ) ∣ b) (i : ι) :
    Nonempty ((weightedProjTwisting R w (b : ℤ)).restrict
      (weightedCoordinateOpen R w i).ι ≅
        SheafOfModules.unit (R := (weightedCoordinateOpen R w i).toScheme.ringCatSheaf)) :=
  ⟨weightedProjCoordinateFrameIso R w b hb hw i⟩

/-- The coordinate frame's forward map is the fraction s divided by X_i^(b/w_i). -/
theorem weightedProjCoordinateFrameIso_hom_val (b : ℕ) (hb : 0 < b)
    (hw : ∀ i, (w i : ℕ) ∣ b) (i : ι)
    (V : (weightedCoordinateOpen R w i).toScheme.Opens)
    (s : ((weightedProjTwisting R w (b : ℤ)).restrict
      (weightedCoordinateOpen R w i).ι).val.obj (op V))
    (x : (weightedCoordinateOpen R w i).ι ''ᵁ V) :
    ((((weightedCoordinateOpen R w i).ι.appIso V).inv
      ((weightedProjCoordinateFrameIso R w b hb hw i).hom.val.app (op V) s)).1 x).val =
        s.1 x * Localization.mk 1
          ⟨weightedCoordinatePower R w b i,
            weightedCoordinatePower_not_mem R w b hb i (hw i)
              ⟨x.1, (weightedCoordinateOpen R w i).ι_image_le V x.2⟩⟩ :=
  ProjTwisting.homogeneousCoordinateFrameIso_hom_val (weightedPolynomialGrading R w) b
    (weightedCoordinatePower R w b i) (weightedCoordinatePower_mem R w b i (hw i))
    (weightedCoordinateOpen R w i) (weightedCoordinatePower_not_mem R w b hb i (hw i)) V s x

/-- The inverse coordinate frame multiplies the transported scalar by X_i^(b/w_i). -/
theorem weightedProjCoordinateFrameIso_inv_val (b : ℕ) (hb : 0 < b)
    (hw : ∀ i, (w i : ℕ) ∣ b) (i : ι)
    (V : (weightedCoordinateOpen R w i).toScheme.Opens)
    (r : Γ((weightedCoordinateOpen R w i).toScheme, V))
    (x : (weightedCoordinateOpen R w i).ι ''ᵁ V) :
    ((weightedProjCoordinateFrameIso R w b hb hw i).inv.val.app (op V) r).1 x =
      ((((weightedCoordinateOpen R w i).ι.appIso V).inv r).1 x).val *
        Localization.mk (weightedCoordinatePower R w b i) 1 :=
  ProjTwisting.homogeneousCoordinateFrameIso_inv_val (weightedPolynomialGrading R w) b
    (weightedCoordinatePower R w b i) (weightedCoordinatePower_mem R w b i (hw i))
    (weightedCoordinateOpen R w i) (weightedCoordinatePower_not_mem R w b hb i (hw i)) V r x

/-- The forward frame sends the existing named coordinate section to the actual scalar one.
(The section goes through `sectionsSubmodule`; see `homogeneousCoordinateFrameIso_hom_section` for the reason.) -/
theorem weightedProjCoordinateFrameIso_section (b : ℕ) (hb : 0 < b)
    (hw : ∀ i, (w i : ℕ) ∣ b) (i : ι)
    (V : (weightedCoordinateOpen R w i).toScheme.Opens) :
    (weightedProjCoordinateFrameIso R w b hb hw i).hom.val.app (op V)
      (show ProjTwisting.sectionsSubmodule (weightedPolynomialGrading R w) (b : ℤ)
          ((weightedCoordinateOpen R w i).ι ''ᵁ V) from
        weightedCoordinateTwistingSection R w b i (hw i)
          ((weightedCoordinateOpen R w i).ι ''ᵁ V)) =
      (1 : Γ((weightedCoordinateOpen R w i).toScheme, V)) :=
  ProjTwisting.homogeneousCoordinateFrameIso_hom_section (weightedPolynomialGrading R w) b
    (weightedCoordinatePower R w b i) (weightedCoordinatePower_mem R w b i (hw i))
    (weightedCoordinateOpen R w i) (weightedCoordinatePower_not_mem R w b hb i (hw i)) V

/-
The two naturality statements (`…_hom_naturality` / `…_inv_naturality`) are deliberately absent: they are one-line
special cases of `PresheafOfModules.naturality_apply (weightedProjCoordinateFrameIso …).hom.val j.op s`, and, being
stated at the weighted concrete level, each would cost 6–12 s of kernel time. Use the Mathlib lemma directly when needed.
-/

/-- Multiplication and division are inverse on each actual restricted twist module. -/
theorem weightedProjCoordinateFrameIso_inv_hom (b : ℕ) (hb : 0 < b)
    (hw : ∀ i, (w i : ℕ) ∣ b) (i : ι)
    (V : (weightedCoordinateOpen R w i).toScheme.Opens)
    (s : ((weightedProjTwisting R w (b : ℤ)).restrict
      (weightedCoordinateOpen R w i).ι).val.obj (op V)) :
    (weightedProjCoordinateFrameIso R w b hb hw i).inv.val.app (op V)
      ((weightedProjCoordinateFrameIso R w b hb hw i).hom.val.app (op V) s) = s :=
  congrArg (fun φ : End ((weightedProjTwisting R w (b : ℤ)).restrict
      (weightedCoordinateOpen R w i).ι) ↦ φ.val.app (op V) s)
    (weightedProjCoordinateFrameIso R w b hb hw i).hom_inv_id

/-- Division and multiplication are inverse on each actual structure-sheaf section ring. -/
theorem weightedProjCoordinateFrameIso_hom_inv (b : ℕ) (hb : 0 < b)
    (hw : ∀ i, (w i : ℕ) ∣ b) (i : ι)
    (V : (weightedCoordinateOpen R w i).toScheme.Opens)
    (r : Γ((weightedCoordinateOpen R w i).toScheme, V)) :
    (weightedProjCoordinateFrameIso R w b hb hw i).hom.val.app (op V)
      ((weightedProjCoordinateFrameIso R w b hb hw i).inv.val.app (op V) r) = r :=
  congrArg (fun φ : End (SheafOfModules.unit
      (R := (weightedCoordinateOpen R w i).toScheme.ringCatSheaf)) ↦ φ.val.app (op V) r)
    (weightedProjCoordinateFrameIso R w b hb hw i).inv_hom_id

end MiyaokaMori.WeightedJets
