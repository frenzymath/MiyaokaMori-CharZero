import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharLocallyConstant
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.InvertibleSheafFlatOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackLineBundlePow
import MiyaokaMori.AlgebraicGeometry.Cohomology.SnapperPolynomial
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.TopIntersectionFromEuler
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveFiberOfProjectiveMorphism

/-! # Deformation invariance of the top self-intersection

In a flat projective family the top self-intersection is the same on all fibers (constancy of `χ` +
the leading coefficient of the Snapper polynomial); ampleness of `O(m)` is not needed (proof of
Proposition 2.4 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Being a line bundle depends only on the isomorphism class (`restrict` is a functor). -/
private theorem isLineBundle_of_iso {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) [M.IsLineBundle] : N.IsLineBundle where
  locally_trivial x := by
    obtain ⟨U, hxU, ⟨i⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) x
    exact ⟨U, hxU, ⟨(AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ i⟩⟩

/-- The iterated tensor power `moduleTensorPower` of a line bundle is a line bundle. -/
private theorem isLineBundle_moduleTensorPower {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] (n : ℕ) : (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n).IsLineBundle :=
  isLineBundle_of_iso (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerIsoTensorPow L n).symm

/-- An integer power of a line bundle is a line bundle. -/
private theorem isLineBundle_zpow {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] (p : ℤ) : (L ^ p).IsLineBundle := by
  cases p with
  | ofNat n => exact isLineBundle_moduleTensorPower L n
  | negSucc n =>
    have : (AlgebraicGeometry.Scheme.Modules.moduleSheafDual L).IsLineBundle :=
      SheafOfModules.IsLineBundle.dual L
    exact isLineBundle_moduleTensorPower (AlgebraicGeometry.Scheme.Modules.moduleSheafDual L) (n + 1)

/-- **Deformation invariance of the top self-intersection**: for a flat projective morphism `f : Y → T`
over a connected locally Noetherian base and a line bundle `L` on `Y`, the top self-intersections of
`L` restricted to the fibers over `t₁` and `t₂` (schemes over `κ(t₁)`, `κ(t₂)`) agree. -/
theorem topSelfIntersection_constant_in_flat_family
    {Y T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian T]
    [ConnectedSpace T]
    (f : Y ⟶ T) [AlgebraicGeometry.IsProjectiveMorphism f] [AlgebraicGeometry.Flat f]
    (L : Y.Modules) [L.IsLineBundle] (t₁ t₂ : T)
    -- the fiber is viewed as a scheme over `κ(t)`, with the `Over` structure `f.fiberOverSpecResidueField t`
    (h₁ : letI := f.fiberOverSpecResidueField t₁; IsProperOver (T.residueField t₁) (f.fiber t₁))
    (h₂ : letI := f.fiberOverSpecResidueField t₂; IsProperOver (T.residueField t₂) (f.fiber t₂))
    [((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₁)).obj L).IsLineBundle]
    [((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₂)).obj L).IsLineBundle]
    (hdim : (f.fiber t₁).dimension = (f.fiber t₂).dimension) :
    letI := f.fiberOverSpecResidueField t₁
    letI := f.fiberOverSpecResidueField t₂
    AlgebraicGeometry.topSelfIntersection (k := T.residueField t₁) (f.fiber t₁) h₁
        ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₁)).obj L)
      = AlgebraicGeometry.topSelfIntersection (k := T.residueField t₂) (f.fiber t₂) h₂
        ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₂)).obj L) := by
  let := f.fiberOverSpecResidueField t₁
  let := f.fiberOverSpecResidueField t₂
  have : AlgebraicGeometry.IsProper f := AlgebraicGeometry.IsProjectiveMorphism.isProper f
  have : AlgebraicGeometry.IsLocallyNoetherian Y :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  -- steps 1–3: `χ(Y_{t₁}, L_{t₁}^p) = χ(Y_{t₂}, L_{t₂}^p)` for all `p`
  have hχ : ∀ p : ℤ,
      AlgebraicGeometry.sheafEulerCharacteristic (k := T.residueField t₁) (f.fiber t₁)
          (((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₁)).obj L) ^ p)
        = AlgebraicGeometry.sheafEulerCharacteristic (k := T.residueField t₂) (f.fiber t₂)
          (((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₂)).obj L) ^ p) := by
    intro p
    have : (L ^ p).IsLineBundle := isLineBundle_zpow L p
    have : (L ^ p).IsCoherent :=
      AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree (L ^ p)
    obtain ⟨e₁⟩ := (AlgebraicGeometry.Scheme.Modules.pullback_linePow (f.fiberι t₁) L p).2
    obtain ⟨e₂⟩ := (AlgebraicGeometry.Scheme.Modules.pullback_linePow (f.fiberι t₂) L p).2
    rw [← AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e₁,
      ← AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e₂]
    exact (eulerCharacteristic_isLocallyConstant_in_flat_family f (L ^ p)
      (twistPow_isFlatOver f L p)).apply_eq_of_preconnectedSpace t₁ t₂
  -- step 4: the two Snapper polynomials agree on `ℤ`, hence are equal
  obtain ⟨P₁, -, hP₁⟩ := exists_snapper_polynomial (k := T.residueField t₁) (f.fiber t₁) h₁
    ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₁)).obj L)
  obtain ⟨P₂, -, hP₂⟩ := exists_snapper_polynomial (k := T.residueField t₂) (f.fiber t₂) h₂
    ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₂)).obj L)
  have hPP : P₁ = P₂ := by
    refine Polynomial.eq_of_infinite_eval_eq P₁ P₂
      ((Set.infinite_range_of_injective (Int.cast_injective (α := ℚ))).mono ?_)
    rintro _ ⟨p, rfl⟩
    show P₁.eval (p : ℚ) = P₂.eval (p : ℚ)
    rw [← hP₁ p, ← hP₂ p, hχ p]
  -- step 5: top self-intersection = `d!·(coefficient of p^d)`
  have h1 := topSelfIntersection_eq_leadingCoeff (k := T.residueField t₁) (f.fiber t₁) h₁
    (AlgebraicGeometry.isProjectiveOver_fiber_of_isProjectiveMorphism f t₁)
    ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₁)).obj L) _ rfl P₁ hP₁
  have h2 := topSelfIntersection_eq_leadingCoeff (k := T.residueField t₂) (f.fiber t₂) h₂
    (AlgebraicGeometry.isProjectiveOver_fiber_of_isProjectiveMorphism f t₂)
    ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₂)).obj L) _ rfl P₂ hP₂
  have : ((AlgebraicGeometry.topSelfIntersection (k := T.residueField t₁) (f.fiber t₁) h₁
      ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₁)).obj L) : ℤ) : ℚ)
      = (AlgebraicGeometry.topSelfIntersection (k := T.residueField t₂) (f.fiber t₂) h₂
      ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₂)).obj L) : ℤ) := by
    rw [← h1, ← h2, hPP, hdim]
  exact_mod_cast this

end
