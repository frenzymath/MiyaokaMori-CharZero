import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineCartierFinitePresentation
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineRationalSectionCartier
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineCartierPresentationIso
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierFiniteSupport
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PrincipalCartierDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.PrincipalDivisorDegreeZero

/-!
# Degree of the same line module on an integral proper curve

`HasCurveModuleDegree X M d` uses a nonzero element of the actual generic stalk of
`M`, the coordinates of that element in actual local frames, and the resulting
Cartier divisor zero cycle. Its integer is the existing residue-weighted degree
over the specified structure morphism of `X`.

Integrality, Noetherianity, properness and dimension at most one are quantified
inside the relation. Thus a caller may use an original smooth connected curve
without choosing an integrality instance from an admitted theorem. The relation
asserts the existence of actual geometric witnesses, not a universal property of
an empty witness type. Its existence and numerical uniqueness are separate
theorem obligations; no integer or presentation is chosen globally from them.

Sources: Stacks Project `divisors.tex`, `definition-divisor-invertible-sheaf` and
`lemma-divisor-meromorphic-well-defined`; `chow.tex`,
`definition-degree-zero-cycle`, `lemma-spell-out-degree-zero-cycle`,
`lemma-curve-principal-divisor`, and `lemma-degree-vector-bundle`.
This is the source-degree prerequisite for the degree comparison in the proof of
Theorem 1.1 of the paper and for the degrees used in its §2.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Intersection

universe u

variable {k : Type u} [Field k]

/-- The degree of an actual line module, computed from its own rational section divisor.

The Cartier presentation itself supplies the rank-one local frames of this same module.
No arbitrary coefficient function, independently chosen cycle, or degree evaluator is an input.
-/
def HasCurveModuleDegree (X : AlgebraicGeometry.Proj.SchemeOver k) (M : X.scheme.Modules) (d : ℤ) : Prop :=
  ∃ hIntegral : IsIntegral X.scheme,
    ∃ hNoetherian : IsNoetherian X.scheme,
      ∃ hProper : IsProper X.toBase,
        ∃ hdim : topologicalKrullDim X.scheme ≤ 1,
          letI : IsIntegral X.scheme := hIntegral
          letI : IsNoetherian X.scheme := hNoetherian
          letI : IsProper X.toBase := hProper
          ∃ s : M.presheaf.stalk (genericPoint X.scheme),
            ∃ P : AlgebraicGeometry.Divisors.LineCartierPresentation X M s,
              rawZeroCycleDegree X.toBase (P.cartier.zeroCycle hdim) = d

/-- Every specified presentation gives the degree computed by its own Cartier zero cycle. -/
theorem hasCurveModuleDegree_of_presentation (X : AlgebraicGeometry.Proj.SchemeOver k)
    [IsIntegral X.scheme] [IsNoetherian X.scheme] [IsProper X.toBase]
    (M : X.scheme.Modules) (hdim : topologicalKrullDim X.scheme ≤ 1)
    (s : M.presheaf.stalk (genericPoint X.scheme)) (P : AlgebraicGeometry.Divisors.LineCartierPresentation X M s) :
    HasCurveModuleDegree X M (rawZeroCycleDegree X.toBase (P.cartier.zeroCycle hdim)) := by
  exact ⟨inferInstance, inferInstance, inferInstance, hdim, s, P, rfl⟩

/-- A genuine line module on an integral proper curve has a degree from its section divisor.

The proof uses the separately registered existence of the actual Cartier presentation;
this theorem is not used to choose an object in any definition.
-/
theorem exists_curveModuleDegree (X : AlgebraicGeometry.Proj.SchemeOver k)
    [IsIntegral X.scheme] [IsNoetherian X.scheme] [IsProper X.toBase]
    (M : X.scheme.Modules) (hdim : topologicalKrullDim X.scheme ≤ 1)
    (hM : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X M 1) : ∃ d : ℤ, HasCurveModuleDegree X M d := by
  obtain ⟨s, hs⟩ := hM.exists_nonzero_genericSection
  obtain ⟨P⟩ := AlgebraicGeometry.Divisors.exists_lineCartierPresentation X M hM s hs
  exact ⟨rawZeroCycleDegree X.toBase (P.cartier.zeroCycle hdim),
    hasCurveModuleDegree_of_presentation X M hdim s P⟩

/-- Changing rational section, local frames and Cartier cover preserves the same module's degree.

The substantive input is that a principal divisor has degree zero on a proper integral curve.
-/
theorem curveModuleDegree_value_unique (X : AlgebraicGeometry.Proj.SchemeOver k) (M : X.scheme.Modules)
    {d e : ℤ} (hd : HasCurveModuleDegree X M d) (he : HasCurveModuleDegree X M e) :
    d = e := by
  rcases hd with ⟨hIntegral, hNoetherian, hProper, hdim, s, P, hP⟩
  letI : IsIntegral X.scheme := hIntegral
  letI : IsNoetherian X.scheme := hNoetherian
  letI : IsProper X.toBase := hProper
  rcases he with ⟨hIntegral', hNoetherian', hProper', hdim', t, Q, hQ⟩
  have hQ' : rawZeroCycleDegree X.toBase (Q.cartier.zeroCycle hdim) = e := by
    simpa only [Subsingleton.elim hdim' hdim] using hQ
  obtain ⟨a, _, ha⟩ := AlgebraicGeometry.Divisors.lineCartierPresentation_change_section P Q
  have hcycle : P.cartier.zeroCycle hdim =
      DimensionCycle.add (Q.cartier.zeroCycle hdim)
        ((principalCartierData a).zeroCycle hdim) := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    change P.cartier.coefficient x =
      (Q.cartier.zeroCycle hdim).1 x + ((principalCartierData a).zeroCycle hdim).1 x
    rw [CartierLocalData.zeroCycle_apply, principalCartierData_zeroCycle_apply, ha]
  calc
    d = rawZeroCycleDegree X.toBase (P.cartier.zeroCycle hdim) := hP.symm
    _ = rawZeroCycleDegree X.toBase
        (DimensionCycle.add (Q.cartier.zeroCycle hdim)
          ((principalCartierData a).zeroCycle hdim)) := by rw [← hcycle]
    _ = rawZeroCycleDegree X.toBase (Q.cartier.zeroCycle hdim) +
        rawZeroCycleDegree X.toBase ((principalCartierData a).zeroCycle hdim) :=
      rawZeroCycleDegree_add X.toBase _ _
    _ = rawZeroCycleDegree X.toBase (Q.cartier.zeroCycle hdim) := by
      rw [rawZeroCycleDegree_principal_eq_zero]
      simp
    _ = e := hQ'

/-- A genuine isomorphism of the same curve's module sheaves preserves their section-divisor degree.

This transports sections and frames through the isomorphism. It is not an identification
of two independently chosen numerical endpoints by definition.
-/
theorem curveModuleDegree_iso_iff (X : AlgebraicGeometry.Proj.SchemeOver k) (M N : X.scheme.Modules)
    (e : M ≅ N) (d : ℤ) : HasCurveModuleDegree X M d ↔ HasCurveModuleDegree X N d := by
  constructor
  · rintro ⟨hIntegral, hNoetherian, hProper, hdim, s, P, hdegree⟩
    letI : IsIntegral X.scheme := hIntegral
    letI : IsNoetherian X.scheme := hNoetherian
    letI : IsProper X.toBase := hProper
    let s' : N.presheaf.stalk (genericPoint X.scheme) :=
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X.scheme (genericPoint X.scheme) e.hom s
    let P' : AlgebraicGeometry.Divisors.LineCartierPresentation X N s' := P.mapIso e
    refine ⟨hIntegral, hNoetherian, hProper, hdim, s', P', ?_⟩
    change rawZeroCycleDegree X.toBase (P.cartier.zeroCycle hdim) = d
    exact hdegree
  · rintro ⟨hIntegral, hNoetherian, hProper, hdim, s, P, hdegree⟩
    letI : IsIntegral X.scheme := hIntegral
    letI : IsNoetherian X.scheme := hNoetherian
    letI : IsProper X.toBase := hProper
    let s' : M.presheaf.stalk (genericPoint X.scheme) :=
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X.scheme (genericPoint X.scheme) e.inv s
    let P' : AlgebraicGeometry.Divisors.LineCartierPresentation X M s' := P.mapIso e.symm
    refine ⟨hIntegral, hNoetherian, hProper, hdim, s', P', ?_⟩
    change rawZeroCycleDegree X.toBase (P.cartier.zeroCycle hdim) = d
    exact hdegree

end AlgebraicGeometry.Intersection
