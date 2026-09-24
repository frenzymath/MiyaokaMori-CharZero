import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mw

/-! # The unit `O_{Proj 𝒜} → O(0)` is an isomorphism

On the absolute Proj, the canonical map `O_{Proj 𝒜} → O(0)` (`r ↦ (x ↦ (r x).val)`, i.e. `1 ↦ 1/1`) is an
isomorphism.

Source: Stacks 01MN / 01MS (`O_{Proj A}(0) = O_{Proj A}`). Here the sections of `ProjTwisting.sheaf 𝒜 0` are
computed directly: a section of `O(0)` over `U` is a function `x ↦ A_x` (`Localization.AtPrime`) which is locally a
homogeneous fraction `a/b` of degree `0` (`deg a = deg b`); a section of the structure sheaf is a function
`x ↦ A_(x)` (`HomogeneousLocalization.AtPrime`) which is locally a fraction of equal degrees; `val : A_(x) → A_x` is
injective, and the two "locally a fraction of equal degrees" conditions correspond exactly, so the map is a bijection
on every open set.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory
open MiyaokaMori.WeightedJets.ProjTwisting

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The homogeneous localization `A_(x)` at the point `x` (the local notation of Mathlib's `StructureSheaf.lean`). -/
local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal (x : ProjectiveSpectrum 𝒜)))

/-- Applying `val` to a section `r` of the structure sheaf gives a function with values in `A_x` which is locally a
homogeneous fraction of degree `0` (the `val` of a fraction `a/b` of equal degrees is `mk a b`). -/
theorem locallyFraction_zero_val (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    (locallyFraction 𝒜 0).pred (fun x : U => (r.1 x).val) := by
  intro x
  obtain ⟨V, hxV, i, j, a, b, hb, hr⟩ := r.2 x
  refine ⟨V, hxV, i, Or.inr ⟨j, j, a, b, by simp, hb, fun y => ?_⟩⟩
  exact (congrArg HomogeneousLocalization.val (hr y)).trans (HomogeneousLocalization.val_mk _)

/-- The section map of `κ` on an open set `U`, as a concrete function: `r ↦ (x ↦ (r x).val)`. -/
def unitToTwistZeroFun (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) : sectionsSubmodule 𝒜 0 U :=
  ⟨fun x => (r.1 x).val, locallyFraction_zero_val 𝒜 U r⟩

/-- The canonical map `O_{Proj 𝒜} → O(0)`: `r ↦ (x ↦ (r x).val)`. -/
def unitToTwistZero : (𝟙_ (AlgebraicGeometry.Proj 𝒜).Modules) ⟶ AlgebraicGeometry.Proj.twist 𝒜 0 :=
  ⟨{ app := fun U => ModuleCat.ofHom
        (X := (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒜).ringCatSheaf).val.obj U)
        (Y := (presheaf 𝒜 0).obj U)
        { toFun := unitToTwistZeroFun 𝒜 U.unop
          map_add' := fun r s => Subtype.ext (funext fun x => HomogeneousLocalization.val_add _ _)
          map_smul' := fun c r => Subtype.ext (funext fun x => HomogeneousLocalization.val_mul _ _) },
     naturality := fun {U V} i => by
       ext
       rfl }⟩

theorem unitToTwistZero_app (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    (unitToTwistZero 𝒜).app U r = unitToTwistZeroFun 𝒜 U r := rfl

/-- Every section of `O(0)` is pointwise the `val` of some element of `A_(x)`. -/
theorem exists_val_eq (U : Opens (ProjectiveSpectrum.top 𝒜)) (s : sectionsSubmodule 𝒜 0 U) (x : U) :
    ∃ y : at x.1, y.val = s.1 x := by
  obtain ⟨V, hxV, i, hV⟩ := s.2 x
  have hx : (i ⟨x.1, hxV⟩ : U) = x := Subtype.ext rfl
  rcases hV with h0 | ⟨p, q, a, b, hpq, hb, hs⟩
  · refine ⟨0, ?_⟩
    have h1 : s.1 (i ⟨x.1, hxV⟩) = 0 := congrFun h0 ⟨x.1, hxV⟩
    rw [hx] at h1
    exact HomogeneousLocalization.val_zero.trans h1.symm
  · have hp : p = q := by omega
    subst hp
    refine ⟨HomogeneousLocalization.mk
      (⟨p, a, b, hb ⟨x.1, hxV⟩⟩ : HomogeneousLocalization.NumDenSameDeg 𝒜
        (HomogeneousIdeal.toIdeal
          (ProjectiveSpectrum.asHomogeneousIdeal (x.1 : ProjectiveSpectrum 𝒜))).primeCompl), ?_⟩
    have h1 : s.1 (i ⟨x.1, hxV⟩) = Localization.mk a.1 ⟨b.1, hb ⟨x.1, hxV⟩⟩ := hs ⟨x.1, hxV⟩
    exact (HomogeneousLocalization.val_mk _).trans h1.symm

/-- Pointwise choice of elements of `A_(x)` from a section `s` of `O(0)`. -/
def liftFun (U : Opens (ProjectiveSpectrum.top 𝒜)) (s : sectionsSubmodule 𝒜 0 U) :
    ∀ x : U, at x.1 :=
  fun x => Classical.choose (exists_val_eq 𝒜 U s x)

theorem liftFun_val (U : Opens (ProjectiveSpectrum.top 𝒜)) (s : sectionsSubmodule 𝒜 0 U) (x : U) :
    (liftFun 𝒜 U s x).val = s.1 x :=
  Classical.choose_spec (exists_val_eq 𝒜 U s x)

/-- The chosen function is locally a fraction of equal degrees (the section condition of the structure sheaf). -/
theorem liftFun_isLocallyFraction (U : Opens (ProjectiveSpectrum.top 𝒜)) (s : sectionsSubmodule 𝒜 0 U) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred (liftFun 𝒜 U s) := by
  intro x
  obtain ⟨V, hxV, i, hV⟩ := s.2 x
  refine ⟨V, hxV, i, ?_⟩
  rcases hV with h0 | ⟨p, q, a, b, hpq, hb, hs⟩
  · refine ⟨0, ⟨0, zero_mem _⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩,
      fun y => (HomogeneousIdeal.toIdeal
        (ProjectiveSpectrum.asHomogeneousIdeal (y.1 : ProjectiveSpectrum 𝒜))).primeCompl.one_mem,
      fun y => ?_⟩
    apply HomogeneousLocalization.val_injective
    have h1 : s.1 (i y) = 0 := congrFun h0 y
    refine (liftFun_val 𝒜 U s (i y)).trans (h1.trans ?_)
    exact ((HomogeneousLocalization.val_mk _).trans (Localization.mk_zero _)).symm
  · have hp : p = q := by omega
    subst hp
    refine ⟨p, a, b, hb, fun y => ?_⟩
    apply HomogeneousLocalization.val_injective
    exact (liftFun_val 𝒜 U s (i y)).trans
      ((hs y).trans (HomogeneousLocalization.val_mk ⟨p, a, b, hb y⟩).symm)

/-- The section map is bijective: `val` is injective; every degree-`0` locally-fractional function is pointwise in the
image of `val` (`liftFun`), and the chosen function satisfies the local fraction condition of the structure sheaf. -/
theorem unitToTwistZeroFun_bijective (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Function.Bijective (unitToTwistZeroFun 𝒜 U) := by
  refine ⟨fun r r' h => ?_, fun s => ?_⟩
  · apply Subtype.ext
    funext x
    apply HomogeneousLocalization.val_injective
    exact congrFun (congrArg Subtype.val h) x
  · refine ⟨⟨liftFun 𝒜 U s, liftFun_isLocallyFraction 𝒜 U s⟩, ?_⟩
    apply Subtype.ext
    funext x
    exact liftFun_val 𝒜 U s x

/-- **`O_{Proj 𝒜} → O(0)` is an isomorphism**: it is a bijection on every open set (`unitToTwistZeroFun_bijective`). -/
theorem isIso_unitToTwistZero : IsIso (unitToTwistZero 𝒜) := by
  rw [AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact unitToTwistZeroFun_bijective 𝒜 U

end AlgebraicGeometry.Proj

end
