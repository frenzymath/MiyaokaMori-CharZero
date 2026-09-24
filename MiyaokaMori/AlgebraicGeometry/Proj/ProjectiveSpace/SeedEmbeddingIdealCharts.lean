import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOver
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Standard charts and local kernel ideals of a projective embedding

For a closed immersion `emb : X ⟶ P^N_k` (the project's `ProjectiveSpace N k`), this module records the
standard opens of the same projective Proj and the scheme-theoretic kernel ideal of `emb` on each affine
chart. The `Away` ideal is transported through Mathlib's canonical `Proj.basicOpenIsoAway`; no polynomial
homogeneous ideal or saturation claim is made here.

Sources: §2 of the paper; Stacks Project, `constructions.tex`,
the standard Proj opens and their homogeneous localizations.

Declarations that only concern `P^N` take `(k) (N : ℕ)` explicitly
(`standardAffineOpen k N i`, `chartScheme`, `chartRing`, `chartIso`), those about the embedding take
`{X : Scheme} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k)` (`chartKernelGamma emb i`, `chartKernelAway emb i`), with
`[IsClosedImmersion emb]` only where a proof uses it. The namespace `ProjectiveEmbedding` is a name only
(the structure `ProjectiveEmbedding k X N` lives in the root namespace).
`P^N` is spelled `ProjectiveSpace N k` (the abbrev of `ProjectiveSpaceOver N k`), so callers pass `e.emb` directly and
instance search finds `IsClosedImmersion e.emb` (`ProjectiveEmbedding.closed`).

The standard chart is `ProjectiveSpaceOver.chart N k i`;
`standardAffineOpen k N i` is its `affineOpens` packaging `⟨chart N k i, isAffineOpen_chart N k i⟩`, and `chartScheme`,
`chartRing`, `chartIso`, `chartKernelGamma`, `chartKernelAway` are definitions about it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The standard open `D₊(Xᵢ) = ProjectiveSpaceOver.chart N k i` packaged with its affine-open proof
`ProjectiveSpaceOver.isAffineOpen_chart` (a constructor of the one chart definition, not a second chart). -/
def ProjectiveEmbedding.standardAffineOpen (N : ℕ) (i : Fin (N + 1)) :
    (ProjectiveSpace N k).affineOpens :=
  ⟨ProjectiveSpaceOver.chart N k i, ProjectiveSpaceOver.isAffineOpen_chart N k i⟩

/-- The scheme of the affine standard chart. -/
abbrev ProjectiveEmbedding.chartScheme (N : ℕ) (i : Fin (N + 1)) : Scheme :=
  (ProjectiveEmbedding.standardAffineOpen k N i).1.toScheme

/-- The degree-zero homogeneous localization of the `i`th standard chart. -/
abbrev ProjectiveEmbedding.chartRing (N : ℕ) (i : Fin (N + 1)) : Type u :=
  HomogeneousLocalization.Away (projectiveGrading k N) (MvPolynomial.X i)

/-- The canonical chart isomorphism from the homogeneous localization to sections. -/
def ProjectiveEmbedding.chartIso (N : ℕ) (i : Fin (N + 1)) :
    CommRingCat.of (ProjectiveEmbedding.chartRing k N i) ≅
      Γ(ProjectiveSpace N k, ProjectiveEmbedding.standardAffineOpen k N i) :=
  by
    change CommRingCat.of
        (HomogeneousLocalization.Away (projectiveGrading k N) (MvPolynomial.X i)) ≅
      Γ(Proj (projectiveGrading k N),
        Proj.basicOpen (projectiveGrading k N) (MvPolynomial.X i))
    exact Proj.basicOpenIsoAway (projectiveGrading k N) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one

variable {k} {X : Scheme.{u}} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k)

/-- The actual scheme-theoretic kernel ideal of the embedding on the Gamma ring of the chart. -/
def ProjectiveEmbedding.chartKernelGamma (i : Fin (N + 1)) :
    Ideal Γ(ProjectiveSpace N k, ProjectiveEmbedding.standardAffineOpen k N i) :=
  emb.ker.ideal (ProjectiveEmbedding.standardAffineOpen k N i)

/-- The same kernel ideal transported to the homogeneous localization chart ring. -/
def ProjectiveEmbedding.chartKernelAway (i : Fin (N + 1)) :
    Ideal (ProjectiveEmbedding.chartRing k N i) :=
  (ProjectiveEmbedding.chartKernelGamma emb i).comap (ProjectiveEmbedding.chartIso k N i).hom.hom

end AlgebraicGeometry.Proj
