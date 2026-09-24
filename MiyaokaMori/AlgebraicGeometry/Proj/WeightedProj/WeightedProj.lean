import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.RingTheory.WeightedJetValuation

/-!
# Local weighted polynomial Proj and its coordinate charts

The grading is Mathlib's actual `weightedHomogeneousSubmodule`, also used by the
Veronese generation statement. The scheme is its `Proj`; each coordinate chart is
the spectrum of the degree-zero homogeneous localization. The jet specialization
uses the shared `WeightedJets.JetCoordinate` and `WeightedJets.jetCoordinateWeight`.

The structure morphism and the field-valued wrapper work over any coefficient
field, without algebraic closedness or characteristic hypotheses. Coordinate
powers at a common divisible degree are actual homogeneous polynomials, and each
homogeneous piece is finite over the coefficient ring for finitely many variables.

These are the local models required by the weighted intersection formula and the positive line
bundle (Sections 2 and 3 of the paper). This file does not construct the global based-jet sheaf,
prove normality or a dimension formula, or construct a relatively very ample twist.
Its coordinate powers are not asserted to be global sections of such a twist.

Sources: Stacks Project, `constructions.tex`, Section `section-proj`, in particular
`lemma-standard-open`, `lemma-proj-sheaves` and `lemma-proj-scheme`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MiyaokaMori.WeightedJets

universe u v

variable (R : Type u) [CommRing R] {ι : Type v} (w : ι → ℕ+)

/-- The actual degree-`m` submodule for the positive coordinate weights. -/
abbrev weightedPolynomialGrading : ℕ → Submodule R (MvPolynomial ι R) :=
  MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (w i : ℕ))

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The scheme Proj of the weighted polynomial algebra over `R`. -/
def weightedProj : Scheme := Proj (weightedPolynomialGrading R w)

/-- The structural morphism to the coefficient ring, through the degree-zero part.

The coefficient universe contains the coordinate universe, so both schemes have
the same universe. In particular, finite jet coordinates work over any `Type u` field.
-/
def weightedProjToSpec (S : Type (max u v)) [CommRing S] {σ : Type v} (w : σ → ℕ+) :
    weightedProj S w ⟶ Spec (.of S) :=
  Proj.toSpecZero (weightedPolynomialGrading S w) ≫
    Spec.map (CommRingCat.ofHom (algebraMap S (weightedPolynomialGrading S w 0)))

/-- The standard coordinate open `D₊(Xᵢ)` in the weighted Proj. -/
def weightedCoordinateOpen (i : ι) : (weightedProj R w).Opens :=
  Proj.basicOpen (weightedPolynomialGrading R w) (MvPolynomial.X i)

/-- The coordinate-chart ring consists of homogeneous fractions of degree zero. -/
abbrev weightedCoordinateRing (i : ι) :=
  HomogeneousLocalization.Away (weightedPolynomialGrading R w) (MvPolynomial.X i)

/-- The standard affine chart is the spectrum of the degree-zero localization. -/
def weightedCoordinateChartIso (i : ι) :
    (weightedCoordinateOpen R w i).toScheme ≅ Spec (.of (weightedCoordinateRing R w i)) :=
  Proj.basicOpenIsoSpec (weightedPolynomialGrading R w) (MvPolynomial.X i)
    ((MvPolynomial.mem_weightedHomogeneousSubmodule R _ _ _).mpr
      (MvPolynomial.isWeightedHomogeneous_X R (fun j ↦ (w j : ℕ)) i)) (w i).pos

/-- The canonical inclusion of the coordinate localization chart into weighted Proj. -/
def weightedCoordinateChartMap (i : ι) :
    Spec (.of (weightedCoordinateRing R w i)) ⟶ weightedProj R w :=
  (weightedCoordinateChartIso R w i).inv ≫ (weightedCoordinateOpen R w i).ι

/-- Each coordinate chart maps to weighted Proj by an actual open immersion. -/
instance weightedCoordinateChartMap_isOpenImmersion (i : ι) :
    IsOpenImmersion (weightedCoordinateChartMap R w i) := by
  unfold weightedCoordinateChartMap
  infer_instance

/-- A coordinate to the power `b / weight(i)`, retaining its multiplicity. -/
def weightedCoordinatePower (b : ℕ) (i : ι) : MvPolynomial ι R :=
  MvPolynomial.X i ^ (b / (w i : ℕ))

/-- Divisibility puts each coordinate power in the same actual graded piece. -/
theorem weightedCoordinatePower_mem (b : ℕ) (i : ι) (hi : (w i : ℕ) ∣ b) :
    weightedCoordinatePower R w b i ∈ weightedPolynomialGrading R w b := by
  have h := (MvPolynomial.isWeightedHomogeneous_X (R := R) (fun j ↦ (w j : ℕ)) i).pow
    (b / (w i : ℕ))
  simpa only [weightedCoordinatePower, weightedPolynomialGrading,
    MvPolynomial.mem_weightedHomogeneousSubmodule, smul_eq_mul, Nat.div_mul_cancel hi] using h

/-- At a positive divisible degree, the coordinate power has the same Proj open. -/
theorem weightedCoordinatePower_basicOpen (b : ℕ) (hb : 0 < b) (i : ι)
    (hi : (w i : ℕ) ∣ b) :
    Proj.basicOpen (weightedPolynomialGrading R w) (weightedCoordinatePower R w b i) =
      weightedCoordinateOpen R w i := by
  exact Proj.basicOpen_pow (weightedPolynomialGrading R w) (MvPolynomial.X i)
    (b / (w i : ℕ)) (Nat.div_pos (Nat.le_of_dvd hb hi) (w i).pos)

/-- Each weighted homogeneous piece is finite over the coefficient ring. -/
theorem weightedPolynomialGrading_finite [Finite ι] (m : ℕ) :
    Module.Finite R (weightedPolynomialGrading R w m) := by
  apply Module.Finite.iff_fg.mpr
  exact MvPolynomial.weightedHomogeneousSubmodule_fg R (fun i ↦ (w i : ℕ))
    (fun i ↦ (w i).ne_zero) m

end MiyaokaMori.WeightedJets
