import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrameCover
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineRationalSectionCartier
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldSections

/-!
# Cartier presentations from a specified finite cover by line frames

Two frames of the same module sheaf give a unit ratio of the coordinates of a nonzero generic
section in every stalk of their overlap. The existing function-field gluing theorem produces
a unit of the section ring on that entire overlap, with the same coordinate ratio.

A specified finite cover by nonempty framed opens then gives an actual
`LineCartierPresentation`: its equations are exactly these generic coordinates, and its
whole-overlap units come from the preceding construction. The existence of the finite frame
cover and the presentation existence theorem remain separate interfaces.

Sources: Theorem 1.1 of the paper and the proof of Proposition 2.4; Stacks Project
`divisors.tex`,
`definition-order-vanishing-meromorphic`, and `chow.tex`, `definition-divisor-invertible-sheaf`
and `definition-cap-c1`. Function-field gluing uses `morphisms.tex`,
`lemma-integral-scheme-rational-functions`, and `sheaves.tex`, `lemma-condition-star-sections`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Divisors.LineGenericCoordinates

namespace AlgebraicGeometry.Divisors.LineCartierFinitePresentation

universe u

/-- The ratio of a nonzero generic section's two frame coordinates is the image of a unit
section on the entire nonempty overlap of the two frames. -/
theorem exists_unit_genericCoordinate_ratio (X : Scheme.{u}) [IsIntegral X] (M : X.Modules)
    (U V : X.Opens) (hU : Nonempty U) (hV : Nonempty V)
    (eU : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (eV : M.restrict V.ι ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    [Nonempty ↑(U ⊓ V)] (s : M.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    ∃ a : Γ(X, U ⊓ V)ˣ,
      X.germToFunctionField (U ⊓ V) (a : Γ(X, U ⊓ V)) =
        genericCoordinate X M U hU eU s / genericCoordinate X M V hV eV s := by
  apply AlgebraicGeometry.Scheme.exists_unit_section_of_stalkwise_unit X (U ⊓ V)
  intro x
  exact genericCoordinate_ratio_is_local_unit X M U V x.1 x.2.1 x.2.2 eU eV s hs

/-- A specified finite cover by nonempty frames presents the same nonzero generic section
using its actual frame coordinates and units on whole overlaps. -/
def ofFiniteFrames {k : Type u} [Field k] (X : AlgebraicGeometry.Proj.SchemeOver k)
    [IsIntegral X.scheme] [IsLocallyNoetherian X.scheme] (M : X.scheme.Modules)
    {ι : Type u} [Finite ι] (U : ι → X.scheme.Opens) (hU : ∀ i, Nonempty (U i))
    (hcover : ⋃ i, (U i : Set X.scheme) = Set.univ)
    (e : ∀ i, M.restrict (U i).ι ≅
      SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (s : M.presheaf.stalk (genericPoint X.scheme)) (hs : s ≠ 0) :
    LineCartierPresentation X M s where
  section_ne_zero := hs
  cartier :=
    { index := ι
      opens := U
      cover := hcover
      locallyFinite := locallyFinite_of_finite _
      equation := fun i ↦ genericCoordinate X.scheme M (U i) (hU i) (e i) s
      equation_ne_zero := fun i ↦
        genericCoordinate_ne_zero X.scheme M (U i) (hU i) (e i) s hs
      ratio_unit := by
        intro i j hW
        letI : Nonempty ↑(U i ⊓ U j) := hW
        obtain ⟨a, ha⟩ := exists_unit_genericCoordinate_ratio X.scheme M
          (U i) (U j) (hU i) (hU j) (e i) (e j) s hs
        exact ⟨a, a.isUnit, ha⟩ }
  frame := e
  equation_eq := fun _ _ ↦ rfl

end AlgebraicGeometry.Divisors.LineCartierFinitePresentation

namespace AlgebraicGeometry.Divisors
open AlgebraicGeometry.Proj AlgebraicGeometry.Scheme.Modules

universe v

/-- Every nonzero rational section of the same rank-one module on a Noetherian
integral scheme has a Cartier presentation by actual local frames and their units.

Declared here rather than in `LineRationalSectionCartier`, where the statement was first
registered, because its proof needs the finite frame cover and the whole-overlap unit
construction of this module. -/
theorem exists_lineCartierPresentation {k : Type v} [Field k] (X : SchemeOver k)
    [IsIntegral X.scheme] [IsNoetherian X.scheme] (M : X.scheme.Modules)
    (hM : IsLocallyFreeRank X M 1)
    (s : M.presheaf.stalk (genericPoint X.scheme)) (hs : s ≠ 0) :
    Nonempty (LineCartierPresentation X M s) := by
  classical
  obtain ⟨S, U, hU, hframe, hcover⟩ := hM.exists_finite_frame_cover
  exact ⟨LineCartierFinitePresentation.ofFiniteFrames X M U
    (fun i ↦ ⟨⟨i.val, hU i⟩⟩) hcover (fun i ↦ Classical.choice (hframe i)) s hs⟩

end AlgebraicGeometry.Divisors
