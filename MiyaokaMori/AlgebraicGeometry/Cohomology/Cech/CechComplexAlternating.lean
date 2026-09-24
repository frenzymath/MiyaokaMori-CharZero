import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingDefs

/-! # The alternating Čech complex

The alternating Čech complex `Č^•_alt(U, M)` of a module on a family of opens: the `p`-th term is
`∏_{i_0<⋯<i_p} M(U_{i_0} ∩ ⋯ ∩ U_{i_p})`, the differential is the alternating sum of restriction
maps; it is a cochain complex of `Γ(X, ⊤)`-modules.

The definitions (`sectionsOverTop`, `sectionsOverTopRestrict`, `cechTermAlt`, `cech_face_le`,
`cechDiffAlt`, `cechTermAltZ`, `cechDiffAltZ`) live in `CechComplexAlternatingDefs.lean`; this file
only contains `d ∘ d = 0` and the complex itself.

Source: Stacks 01FG (the alternating Čech complex).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `d ∘ d = 0` (the standard cancellation of alternating sums, Stacks 01FG): in nonnegative degrees
this is `cechDiffAlt_comp`; in negative degrees the first term is `0`. -/

theorem AlgebraicGeometry.Scheme.Modules.cechDiffAltZ_comp {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (M : X.Modules) (i : ℤ) :
    AlgebraicGeometry.Scheme.Modules.cechDiffAltZ U M i ≫ AlgebraicGeometry.Scheme.Modules.cechDiffAltZ U M (i + 1) = 0 := by
  cases i with
  | ofNat p =>
    exact AlgebraicGeometry.Scheme.Modules.cechDiffAlt_comp U M p
  | negSucc k =>
    exact CategoryTheory.Limits.zero_comp

/-- The alternating Čech complex `Č^•_alt(U, M)` (Stacks 01FG). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.cechComplexAlt {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (M : X.Modules) : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ :=
  CochainComplex.of (AlgebraicGeometry.Scheme.Modules.cechTermAltZ U M)
    (AlgebraicGeometry.Scheme.Modules.cechDiffAltZ U M) (AlgebraicGeometry.Scheme.Modules.cechDiffAltZ_comp U M)

end
