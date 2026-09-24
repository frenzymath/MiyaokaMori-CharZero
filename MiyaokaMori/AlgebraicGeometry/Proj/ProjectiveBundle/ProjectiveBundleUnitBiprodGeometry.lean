import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiprodLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLocallyPolynomialIntegral
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLocallyPolynomialKrullDim
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLocallyPolynomialSmooth
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraGeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraLocallyPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.SymGradedAlgebraPartOneFiniteType
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.UnitBiprodLineBundleRank

/-! # Geometry of the ruled surface `P(O_X ⊕ L)`

For a line bundle `L` on an integral, locally Noetherian scheme `X`, the projective bundle `P(O_X ⊕ L)`
is integral, smooth of relative dimension `1` over `X`, projective over `X`, and of dimension
`dim X + 1`. This is the ruled surface `W = P(O_{C̃} ⊕ L)` of the ruled-surface realization corollary
of the paper. References: Stacks 01OA, 01OD, 01O3.

Proof:
1. `O_X ⊕ L` is locally free of rank `2`, so the projective bundle is isomorphic to `P^1_U` on a
   trivializing open cover of `X`.
2. `P^1_U → U` is smooth of relative dimension `1` and projective; these properties are Zariski local
   on the target, so they glue to `P(O_X ⊕ L) → X`.
3. Each local product is covered by two integral affine charts; irreducibility of `X` and the
   pairwise intersection of the charts give that the total space is integral.
4. The Krull dimension formula for local products gives `dim P(O_X ⊕ L) = dim X + dim P^1 = dim X + 1`.

The hypothesis `[IsLocallyNoetherian X]` is necessary for the fourth conjunct: for a domain `R` one only
has `dim R + 1 ≤ dim R[x] ≤ 2 dim R + 1` (Mathlib `Polynomial.ringKrullDim_le`), and Seidenberg
(Pacific J. Math. 1953/54) constructs domains with `dim R = 1` and `dim R[x] = 3`; for `X = Spec R` and
`L = O_X`, `P(O ⊕ O) = P^1_R` is covered by two copies of `A^1_R = Spec R[x]`, so
`dim P(O ⊕ L) = 3 ≠ dim X + 1 = 2`. For Noetherian `R` Mathlib has `dim R[x] = dim R + 1`
(`Polynomial.ringKrullDim_of_isNoetherianRing`), which is what the proof needs. The application to a
smooth projective curve over a field is covered, since such a curve is locally Noetherian
(`LocallyOfFiniteType.isLocallyNoetherian`).

Assembly: `P(V) = Proj_X Sym(V^∨)` with `V = O ⊕ L`.
(a) `rank((O ⊕ L)^∨) = 2`;
(b) Sym of a rank-2 locally free sheaf is locally the standard-graded polynomial algebra in 2 variables;
(c) `Proj_X` of such an algebra over an integral base is integral;
(d) … is smooth of relative dimension `1`;
(e) … has dimension `dim X + 1` over a locally Noetherian base;
(f) `Proj_X Sym(V^∨) → X` is a projective morphism by definition (closed immersion = identity), since
    Sym is generated in degree one with finite type degree-one part.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The ruled surface `P(O_X ⊕ L)` over an integral locally Noetherian scheme `X` is integral, smooth of
relative dimension `1`, projective over `X`, and of dimension `dim X + 1`. -/
theorem projectiveBundle_unit_biprod_geometry
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X] [L.IsLineBundle] :
    let V := CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L
    AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.projBundle V).left ∧
      AlgebraicGeometry.SmoothOfRelativeDimension 1
        (AlgebraicGeometry.Scheme.projBundle V).hom ∧
      AlgebraicGeometry.IsProjectiveMorphism
        (AlgebraicGeometry.Scheme.projBundle V).hom ∧
      topologicalKrullDim (AlgebraicGeometry.Scheme.projBundle V).left =
        topologicalKrullDim X + 1 := by
  intro V
  have hlf : (AlgebraicGeometry.Scheme.Modules.dual V).IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' V
  have hqc : (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsLocallyFree.{u, u, u} (AlgebraicGeometry.Scheme.Modules.dual V)
  have hS := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_isLocallyWeightedPolynomial
    (AlgebraicGeometry.Scheme.Modules.dual V) 2
    (AlgebraicGeometry.Scheme.Modules.rankAtStalk_dual_unit_biprod_of_isLineBundle L)
  have hcard : Fintype.card (ULift.{u} (Fin 2)) = 1 + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact AlgebraicGeometry.Scheme.relativeProj_isIntegral_of_isLocallyWeightedPolynomial _ _ _ hS
  · exact AlgebraicGeometry.Scheme.relativeProj_smoothOfRelativeDimension_of_isLocallyWeightedPolynomial
      _ 1 hcard hS
  · change AlgebraicGeometry.IsProjectiveMorphism (AlgebraicGeometry.Scheme.relativeProj
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V))).hom
    exact ⟨AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V), 𝟙 _,
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_generatedInDegreeOne _,
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_part_one_isFiniteType _,
      inferInstance, CategoryTheory.Category.id_comp _⟩
  · have h := AlgebraicGeometry.Scheme.relativeProj_topologicalKrullDim_of_isLocallyWeightedPolynomial
      _ 1 hcard hS
    change topologicalKrullDim (AlgebraicGeometry.Scheme.relativeProj
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V))).left =
        topologicalKrullDim X + 1
    rw [h]
    norm_num

end
