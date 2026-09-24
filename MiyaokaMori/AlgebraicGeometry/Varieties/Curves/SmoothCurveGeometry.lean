import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothCurveDimension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Geometric consequences of the smooth projective curve input

This module contains no declarations. It is kept because `MiyaokaMori.Prelude` imports it, and
its Mathlib imports are kept so that nothing downstream of `Prelude` loses a transitive import.
The basic geometric properties of a smooth projective curve are `SmoothProjectiveCurve.isProper`
and `isIntegral` (`VarietySchemeAccessors`), `isLocallyNoetherian` (`CurveLocallyNoetherian`) and
`isIntegral_of_smooth_connected` (`SmoothProjectiveCurveIntegral`); the argument "connected and
locally irreducible implies irreducible" is in `Stacks033m`.
-/
