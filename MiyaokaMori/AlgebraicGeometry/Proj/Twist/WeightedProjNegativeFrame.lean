import MiyaokaMori.AlgebraicGeometry.Proj.Twist.WeightedProjCoordinateFormula

/-!
# Negative-degree coordinate frames for the Proj twist

`WeightedProjCoordinateFormula` frames `O(d)` for `d : ℕ` by a homogeneous element `g` of
degree `d`: the frame is `g` itself and the coordinate map divides by `g`. This file is the
mirror image for **negative** degrees: on an open `U` where `g` does not vanish, the section
`1/g` is a frame of `O(-d)`, and the coordinate map multiplies by `g`.

The only new mathematical input is `isFraction_multiply_lift`: a degree-`(-d)` homogeneous
fraction times the degree-`d` element `g` is an honest degree-zero homogeneous fraction, i.e.
a section of the structure sheaf. Everything above it is the same four-step ladder as in
`WeightedProjCoordinateFormula` (`exists_…Value` / `…Value` / `…Section` / `…_val`), and the
isomorphism itself is produced by the generic `Scheme.Modules.IsFrame` API in
`ModuleSheafFrame`.

Combining the two halves, `exists_isFrame_sheaf_basicOpen` frames `O(m)` for **every** `m : ℤ`
on the standard open `D₊(g)` of a degree-one homogeneous `g`: `g ^ m` for `m ≥ 0`,
`1 / g ^ (-m)` for `m < 0`. That is what makes `O(m)` a line bundle on `P^N`
(`SerreTwistIsLineBundle`).

Sources: Stacks Project, `constructions.tex`, `lemma-proj-sheaves`, `definition-twist`,
`lemma-when-invertible`; Hartshorne II.5.12(a).

## Performance rules

This file is written **entirely at the level of variables** (a general graded ring `𝒜`, a general homogeneous element
`g`): no statement mentions a concrete graded ring. Carrier conversions of the kind "sections of the restricted sheaf ↔
sections on the image open" are never performed here (they all live in the variable-level lemmas of
`ModuleSheafFrame`); the concrete level (`P^N`) only instantiates once.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open SetLike.GradedMonoid

universe u v t w

namespace MiyaokaMori.WeightedJets

namespace ProjTwisting

-- For the same reason as in `WeightedProjCoordinateFormula`: the fraction lemmas rely on this option to recognize
-- `↑(ProjectiveSpectrum.top 𝒜)` as `ProjectiveSpectrum 𝒜` when synthesizing the `IsPrime` instance.
set_option backward.isDefEq.respectTransparency false

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- `1/g`: on an open `U` where `g` vanishes nowhere, this is a section of `O(-d)` (data).
Degree bookkeeping: numerator `1 ∈ 𝒜 0`, denominator `g ∈ 𝒜 d`, `(0 : ℤ) = d + (-d)`. -/
def inverseSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    sectionsSubmodule 𝒜 (-(d : ℤ)) U :=
  ⟨fun x ↦ Localization.mk 1 ⟨g, hU x⟩,
    PrelocalPredicate.sheafifyOf (P := fractionPrelocal 𝒜 (-(d : ℤ)))
      (Or.inr ⟨0, d, ⟨1, SetLike.one_mem_graded 𝒜⟩, ⟨g, hg⟩, by omega, hU, fun _ ↦ rfl⟩)⟩

/-- The only mathematical input of this file: a homogeneous fraction of degree `-d` multiplied by the homogeneous
element `g` of degree `d` is a genuine homogeneous fraction of degree `0`, i.e. a local section of the structure sheaf.
This is the multiplicative mirror of `isFraction_divide_lift`. -/
theorem isFraction_multiply_lift (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {s : ∀ x : U, Fiber 𝒜 x.1} (hs : IsFraction 𝒜 (-(d : ℤ)) s) :
    ∃ r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal,
      ProjectiveSpectrum.StructureSheaf.IsFraction r ∧
        ∀ x : U, (r x).val = s x * Localization.mk g 1 := by
  rcases hs with rfl | ⟨p, q, a, c, hpq, hc, hs⟩
  · refine ⟨0, ⟨0, ⟨0, zero_mem _⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩,
      fun x ↦ x.1.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, fun _ ↦ rfl⟩, ?_⟩
    intro x
    simp only [Pi.zero_apply, HomogeneousLocalization.val_zero, zero_mul]
  · have he : p + d = q := by omega
    refine ⟨fun x ↦ HomogeneousLocalization.mk
        ⟨q, ⟨a.1 * g, he ▸ SetLike.mul_mem_graded a.2 hg⟩, c, hc x⟩,
      ⟨q, ⟨a.1 * g, he ▸ SetLike.mul_mem_graded a.2 hg⟩, c, hc, fun _ ↦ rfl⟩, ?_⟩
    intro x
    rw [hs, Localization.mk_mul, mul_one]
    exact HomogeneousLocalization.val_mk _

/-- At every point, the value after multiplying by `g` lies in the homogeneous localization used by the structure sheaf. -/
theorem exists_multiplyValue (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (s : sectionsSubmodule 𝒜 (-(d : ℤ)) U) (x : U) :
    ∃ r : HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal,
      r.val = s.1 x * Localization.mk g 1 := by
  obtain ⟨V, hx, i, hs⟩ := s.2 x
  obtain ⟨r, _, hr⟩ := isFraction_multiply_lift 𝒜 d g hg hs
  exact ⟨r ⟨x.1, hx⟩, hr ⟨x.1, hx⟩⟩

/-- The representative in the degree-`0` homogeneous localization after multiplying by `g`. -/
def multiplyValue (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (s : sectionsSubmodule 𝒜 (-(d : ℤ)) U) (x : U) :
    HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal :=
  (exists_multiplyValue 𝒜 d g hg s x).choose

theorem multiplyValue_val (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (s : sectionsSubmodule 𝒜 (-(d : ℤ)) U) (x : U) :
    (multiplyValue 𝒜 d g hg s x).val = s.1 x * Localization.mk g 1 :=
  (exists_multiplyValue 𝒜 d g hg s x).choose_spec

/-- The coordinate map for the frame `1/g`: multiplying a section of `O(-d)` by `g` gives a section of the structure
sheaf. -/
def inverseFrameCoord (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (s : sectionsSubmodule 𝒜 (-(d : ℤ)) U) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U) := by
  refine ⟨multiplyValue 𝒜 d g hg s, ?_⟩
  intro x
  obtain ⟨V, hx, i, hs⟩ := s.2 x
  obtain ⟨r, hr, hval⟩ := isFraction_multiply_lift 𝒜 d g hg hs
  refine ⟨V, hx, i, ?_⟩
  have he : (fun y : V ↦ multiplyValue 𝒜 d g hg s (i y)) = r := by
    funext y
    apply HomogeneousLocalization.val_injective
    exact (multiplyValue_val 𝒜 d g hg s (i y)).trans (hval y).symm
  change ProjectiveSpectrum.StructureSheaf.IsFraction
    (fun y : V ↦ multiplyValue 𝒜 d g hg s (i y))
  rw [he]
  exact hr

theorem inverseFrameCoord_val (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (s : sectionsSubmodule 𝒜 (-(d : ℤ)) U) (x : U) :
    ((inverseFrameCoord 𝒜 d g hg s).1 x).val = s.1 x * Localization.mk g 1 :=
  multiplyValue_val 𝒜 d g hg s x

/-- The frame direction: `r ↦ r • (1/g)`, linear over sections of the structure sheaf. -/
def smulInverseSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U) →ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)]
        sectionsSubmodule 𝒜 (-(d : ℤ)) U :=
  LinearMap.toSpanSingleton _ _ (inverseSection 𝒜 d g hg hU)

theorem smulInverseSection_val (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) (x : U) :
    (smulInverseSection 𝒜 d g hg hU r).1 x = (r.1 x).val * Localization.mk 1 ⟨g, hU x⟩ := rfl

/-- The commuted form of `fiber_coordinate_mul_inverse`. -/
theorem fiber_inverse_mul_coordinate (g : A) (x : ProjectiveSpectrum 𝒜)
    (hx : g ∉ x.asHomogeneousIdeal) :
    (Localization.mk 1 ⟨g, hx⟩ : Fiber 𝒜 x) * Localization.mk g 1 = 1 :=
  (mul_comm _ _).trans (fiber_coordinate_mul_inverse 𝒜 g x hx)

theorem inverseFrameCoord_smulInverseSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    inverseFrameCoord 𝒜 d g hg (smulInverseSection 𝒜 d g hg hU r) = r := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rw [inverseFrameCoord_val, smulInverseSection_val, mul_assoc,
    fiber_inverse_mul_coordinate, mul_one]

theorem smulInverseSection_inverseFrameCoord (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal)
    (s : sectionsSubmodule 𝒜 (-(d : ℤ)) U) :
    smulInverseSection 𝒜 d g hg hU (inverseFrameCoord 𝒜 d g hg s) = s := by
  apply Subtype.ext
  funext x
  rw [smulInverseSection_val, inverseFrameCoord_val, mul_assoc,
    fiber_coordinate_mul_inverse, mul_one]

/-- Multiplication by `1/g` and by `g` are mutually inverse: the module of sections of `O(-d)` is isomorphic to the
section ring of the structure sheaf. -/
def inverseFrameSectionEquiv (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U) ≃ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)]
        sectionsSubmodule 𝒜 (-(d : ℤ)) U :=
  { smulInverseSection 𝒜 d g hg hU with
    invFun := inverseFrameCoord 𝒜 d g hg
    left_inv := inverseFrameCoord_smulInverseSection 𝒜 d g hg hU
    right_inv := smulInverseSection_inverseFrameCoord 𝒜 d g hg hU }

open AlgebraicGeometry.Scheme.Modules in
/-- `1/g` is a frame of `O(-d)` on `U` (the negative-degree mirror of `isFrame_homogeneousSection`). -/
theorem isFrame_inverseSection (d : ℕ) (g : A) (hg : g ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : ∀ x : U, g ∉ x.1.asHomogeneousIdeal) :
    IsFrame (sheaf 𝒜 (-(d : ℤ))) U (inverseSection 𝒜 d g hg hU) := by
  intro W' h
  exact (inverseFrameSectionEquiv 𝒜 d g hg (fun x : W' ↦ hU ⟨x.1, h x.2⟩)).bijective

open AlgebraicGeometry.Scheme.Modules in
/-- **Both signs at once**: for a homogeneous `g` of degree `1` and **every** `m : ℤ`, the twisting sheaf `O(m)` has a
frame on the standard open `D₊(g)`: `g ^ m` (of degree `m`) for `m ≥ 0`, and `1 / g ^ (-m)` for `m < 0`. -/
theorem exists_isFrame_sheaf_basicOpen (m : ℤ) (g : A) (hg : g ∈ 𝒜 1) :
    ∃ e : Γ(sheaf 𝒜 m, Proj.basicOpen 𝒜 g),
      IsFrame (sheaf 𝒜 m) (Proj.basicOpen 𝒜 g) e := by
  have hpow : ∀ n : ℕ, g ^ n ∈ 𝒜 n := fun n ↦ by
    simpa using SetLike.pow_mem_graded n hg
  by_cases hm : 0 ≤ m
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, by omega⟩
    exact ⟨_, isFrame_homogeneousSection 𝒜 n (g ^ n) (hpow n) (Proj.basicOpen 𝒜 g)
      (fun x ↦ x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.2 n)⟩
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    exact ⟨_, isFrame_inverseSection 𝒜 n (g ^ n) (hpow n) (Proj.basicOpen 𝒜 g)
      (fun x ↦ x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.2 n)⟩

end ProjTwisting

end MiyaokaMori.WeightedJets
