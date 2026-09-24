import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProj
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The genuine twisting module on weighted polynomial Proj

For any integer `d`, the sections of `O(d)` are functions into the ordinary localizations
at homogeneous prime ideals which locally have the form `a / b`, where `a` and `b` are
homogeneous and `degree(a) = degree(b) + d`. This is the sheaf associated to the shifted
graded module `S(d)`. The zero section is included explicitly, also for negative degrees. The construction
is universe-polymorphic and makes no field or characteristic assumption.
The local predicate is sheafified, and scalar multiplication uses the actual structure
sheaf of the same Proj. Restrictions are restrictions of these localization-valued functions.

Sources: Stacks Project, `constructions.tex`, `lemma-proj-sheaves`, `definition-twist`,
and `lemma-when-invertible`. The integer shift convention is `S(d)_n = S_(n+d)`.

For the weighted intersection formula (Proposition 2.4 of the paper), this supplies the actual local sheaf
underlying `B_k = O(m)` (Lemma 2.2). The local triviality of `O(b)` on the coordinate charts
(`b` a common positive multiple of the weights) is proved in
`WeightedProjCoordinateFormula` (`weightedProjCoordinateFrameIso`,
`weightedProjTwisting_coordinate_trivial`), which builds on the frame API of
`ModuleSheafFrame`; it is not stated here, because this module
sits below that API in the import order. Relative gluing, the comparison
with the Proj of the Veronese algebra, and relative very ampleness are separate
construction/proof tasks; they are not assumed in the definition of the twist.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open SetLike.GradedMonoid

namespace MiyaokaMori.WeightedJets
universe u v t

namespace ProjTwisting

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The ordinary localization in which shifted homogeneous fractions are compared. -/
abbrev Fiber (x : ProjectiveSpectrum 𝒜) :=
  Localization x.asHomogeneousIdeal.toIdeal.primeCompl

/-- One homogeneous fraction of degree `d`, with zero allowed in every graded component. -/
def IsFraction (d : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (s : ∀ x : U, Fiber 𝒜 x.1) : Prop :=
  s = 0 ∨ ∃ (i j : ℕ) (a : 𝒜 i) (b : 𝒜 j), (i : ℤ) = j + d ∧
    ∃ hb : ∀ x : U, b.1 ∉ x.1.asHomogeneousIdeal,
      ∀ x : U, s x = Localization.mk a.1 ⟨b.1, hb x⟩

/-- Representability by a fixed shifted fraction is stable under open restriction. -/
def fractionPrelocal (d : ℤ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ Fiber 𝒜 x where
  pred s := IsFraction 𝒜 d s
  res i s hs := by
    rcases hs with rfl | ⟨p, q, a, b, hpq, hb, hs⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨p, q, a, b, hpq, fun x ↦ hb (i x), fun x ↦ hs (i x)⟩

/-- Sections of the twist are locally represented by shifted homogeneous fractions. -/
def locallyFraction (d : ℤ) :
    LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ Fiber 𝒜 x :=
  (fractionPrelocal 𝒜 d).sheafify

/-- Adding shifted fractions uses a common homogeneous denominator. -/
theorem isFraction_add (d : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {s t : ∀ x : U, Fiber 𝒜 x.1}
    (hs : IsFraction 𝒜 d s) (ht : IsFraction 𝒜 d t) :
    IsFraction 𝒜 d (s + t) := by
  rcases hs with rfl | ⟨i, j, a, b, hij, hb, hs⟩
  · simpa only [zero_add] using ht
  rcases ht with rfl | ⟨k, l, c, e, hkl, he, ht⟩
  · exact Or.inr ⟨i, j, a, b, hij, hb, by simpa only [add_zero] using hs⟩
  have hdegrees : j + k = i + l := by omega
  refine Or.inr ⟨i + l, j + l,
    ⟨a.1 * e.1 + b.1 * c.1, add_mem (SetLike.mul_mem_graded a.2 e.2)
      (hdegrees ▸ SetLike.mul_mem_graded b.2 c.2)⟩,
    ⟨b.1 * e.1, SetLike.mul_mem_graded b.2 e.2⟩, by omega,
    fun x ↦ x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb x) (he x), ?_⟩
  intro x
  simp only [Pi.add_apply, hs, ht, Localization.add_mk, mul_comm, add_comm]
  rfl

/-- A degree-zero homogeneous fraction multiplies a degree-`d` fraction to degree `d`. -/
theorem structureFraction_mul (d : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal}
    {s : ∀ x : U, Fiber 𝒜 x.1}
    (hr : ProjectiveSpectrum.StructureSheaf.IsFraction r)
    (hs : IsFraction 𝒜 d s) :
    IsFraction 𝒜 d (fun x ↦ (r x).val * s x) := by
  rcases hs with rfl | ⟨i, j, a, b, hij, hb, hs⟩
  · exact Or.inl (by ext; exact mul_zero _)
  rcases hr with ⟨k, c, e, he, hr⟩
  refine Or.inr ⟨k + i, k + j, ⟨c.1 * a.1, SetLike.mul_mem_graded c.2 a.2⟩,
    ⟨e.1 * b.1, SetLike.mul_mem_graded e.2 b.2⟩, by omega,
    fun x ↦ x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (he x) (hb x), ?_⟩
  intro x
  simp only [hr, hs, HomogeneousLocalization.val_mk, Localization.mk_mul]
  rfl

/-- The locally representable sections are closed under addition. -/
theorem locallyFraction_add (d : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {s t : ∀ x : U, Fiber 𝒜 x.1}
    (hs : (locallyFraction 𝒜 d).pred s) (ht : (locallyFraction 𝒜 d).pred t) :
    (locallyFraction 𝒜 d).pred (s + t) := by
  apply PrelocalPredicate.sheafify_inductionOn₂' (fractionPrelocal 𝒜 d)
    (fractionPrelocal 𝒜 d) (fractionPrelocal 𝒜 d) (fun s t ↦ s + t) ?_ hs ht
  intro V W a b ha hb
  exact isFraction_add 𝒜 d
    ((fractionPrelocal 𝒜 d).res (Opens.infLELeft V W) a ha)
    ((fractionPrelocal 𝒜 d).res (Opens.infLERight V W) b hb)

/-- Multiplication by an actual structure-sheaf section preserves locally shifted fractions. -/
theorem locallyFraction_smul (d : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U))
    {s : ∀ x : U, Fiber 𝒜 x.1} (hs : (locallyFraction 𝒜 d).pred s) :
    (locallyFraction 𝒜 d).pred (fun x ↦ (r.1 x).val * s x) := by
  apply PrelocalPredicate.sheafify_inductionOn₂'
    (ProjectiveSpectrum.StructureSheaf.isFractionPrelocal 𝒜)
    (fractionPrelocal 𝒜 d) (fractionPrelocal 𝒜 d) (fun r s ↦ r.val * s) ?_ r.2 hs
  intro V W a b ha hb
  exact structureFraction_mul 𝒜 d
    ((ProjectiveSpectrum.StructureSheaf.isFractionPrelocal 𝒜).res
      (Opens.infLELeft V W) a ha)
    ((fractionPrelocal 𝒜 d).res (Opens.infLERight V W) b hb)

/-- The structure sheaf acts through its actual degree-zero fractions in each localization. -/
def sectionCoefficientMap (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U) →+* (∀ x : U, Fiber 𝒜 x.1) where
  toFun r x := (r.1 x).val
  map_zero' := by ext x; exact HomogeneousLocalization.val_zero
  map_one' := by ext x; exact HomogeneousLocalization.val_one
  map_add' r s := by ext x; exact HomogeneousLocalization.val_add _ _
  map_mul' r s := by ext x; exact HomogeneousLocalization.val_mul _ _

/-- Scalar multiplication on localization-valued functions comes from the structure sheaf. -/
instance sectionFunctionModule (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) (∀ x : U, Fiber 𝒜 x.1) :=
  Module.compHom _ (sectionCoefficientMap 𝒜 U)

/-- The degree-`d` sections form a module over the same Proj's structure-sheaf sections. -/
def sectionsSubmodule (d : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Submodule ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) (∀ x : U, Fiber 𝒜 x.1) where
  carrier := {s | (locallyFraction 𝒜 d).pred s}
  zero_mem' := PrelocalPredicate.sheafifyOf (Or.inl rfl)
  add_mem' := locallyFraction_add 𝒜 d
  smul_mem' r _ hs := locallyFraction_smul 𝒜 d r hs

/-- The twisting presheaf with restriction maps given by restricting the represented functions. -/
def presheaf (d : ℤ) : (Proj 𝒜).PresheafOfModules where
  obj U := ModuleCat.of _ (sectionsSubmodule 𝒜 d U.unop)
  map {U V} i := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((Proj 𝒜).ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of _ (sectionsSubmodule 𝒜 d V.unop)))
    { toFun s := ⟨fun x ↦ s.1 (i.unop x), (locallyFraction 𝒜 d).res i.unop s.1 s.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Forgetting addition identifies the presheaf with the local-predicate sheaf of functions. -/
def presheafForgetIso (d : ℤ) :
    (presheaf 𝒜 d).presheaf ⋙ forget Ab ≅ (subsheafToTypes (locallyFraction 𝒜 d)).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro U V i; ext s; rfl)

/-- The actual sheaf associated to the shifted graded ring `S(d)`. -/
def sheaf (d : ℤ) : (Proj 𝒜).Modules where
  val := presheaf 𝒜 d
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (presheafForgetIso 𝒜 d).symm
      (subsheafToTypes (locallyFraction 𝒜 d)).property)

/-- Restriction in the twist is the actual restriction of localization-valued functions. -/
@[simp]
theorem presheaf_map_apply (d : ℤ) {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (i : U ⟶ V) (s : (presheaf 𝒜 d).obj U) (x : V.unop) :
    ((presheaf 𝒜 d).map i s).1 x = s.1 (i.unop x) := rfl

/-- Every homogeneous polynomial gives its canonical section of the corresponding twist. -/
def homogeneousSection (d : ℕ) (a : A) (ha : a ∈ 𝒜 d)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) : (presheaf 𝒜 (d : ℤ)).obj (op U) := by
  refine ⟨fun _ ↦ Localization.mk a 1, ?_⟩
  exact PrelocalPredicate.sheafifyOf (P := fractionPrelocal 𝒜 (d : ℤ))
    (Or.inr ⟨d, 0, ⟨a, ha⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩,
      by omega, fun x ↦ x.1.asHomogeneousIdeal.toIdeal.primeCompl.one_mem,
      fun _ ↦ rfl⟩)

/-- The canonical homogeneous sections commute with restriction to smaller opens. -/
@[simp]
theorem homogeneousSection_restrict (d : ℕ) (a : A) (ha : a ∈ 𝒜 d)
    {U V : Opens (ProjectiveSpectrum.top 𝒜)} (i : V ⟶ U) :
    (presheaf 𝒜 (d : ℤ)).map i.op (homogeneousSection 𝒜 d a ha U) =
      homogeneousSection 𝒜 d a ha V := rfl

end ProjTwisting

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The twist `O(d)` on the actual positive-weight polynomial Proj. -/
def weightedProjTwisting (R : Type u) [CommRing R] {ι : Type t} (w : ι → ℕ+) (d : ℤ) :
    (weightedProj R w).Modules := ProjTwisting.sheaf (weightedPolynomialGrading R w) d

/-- The actual common-degree coordinate section, retaining its coordinate multiplicity. -/
def weightedCoordinateTwistingSection (R : Type u) [CommRing R] {ι : Type t}
    (w : ι → ℕ+) (b : ℕ) (i : ι) (hi : (w i : ℕ) ∣ b)
    (U : (weightedProj R w).Opens) :
    (weightedProjTwisting R w (b : ℤ)).val.obj (op U) :=
  ProjTwisting.homogeneousSection (weightedPolynomialGrading R w) b
    (weightedCoordinatePower R w b i) (weightedCoordinatePower_mem R w b i hi) U

/-- The coordinate section restricts by the restriction map of the same twist. -/
@[simp]
theorem weightedCoordinateTwistingSection_restrict
    (R : Type u) [CommRing R] {ι : Type t} (w : ι → ℕ+)
    (b : ℕ) (i : ι) (hi : (w i : ℕ) ∣ b)
    {U V : (weightedProj R w).Opens} (j : V ⟶ U) :
    (weightedProjTwisting R w (b : ℤ)).val.map j.op
      (weightedCoordinateTwistingSection R w b i hi U) =
        weightedCoordinateTwistingSection R w b i hi V := rfl

/-
The local triviality of `O(b)` on `D₊(X_i)` is `weightedProjTwisting_coordinate_trivial` in
`WeightedProjCoordinateFormula` (via `weightedProjCoordinateFrameIso`); this module deliberately does not restate it.
-/

end MiyaokaMori.WeightedJets
