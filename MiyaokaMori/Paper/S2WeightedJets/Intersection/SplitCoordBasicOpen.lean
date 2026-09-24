import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraSufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication

/-! # The basic open set of a split coordinate

The relative basic open set `D_+(x_{i,q})` of the coordinate `x_{i,q}` on `Y^sp`: over an affine open `V ⊆ C`
trivializing `Q_i`, `π_sp⁻¹(V) = Proj_{O(V)} O(V)[x]` and the open set is `Proj.basicOpen x_{i,q}`; these local
pieces are compatible with restriction and glue to an open subset of `Y^sp` (the non-vanishing locus of the
coordinate `x_{i,q}`, used for eq. (2.10) of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `D_+(x_{i,q})` is taken to be the non-vanishing locus of the line bundle section `x_{i,q}^{m/q}`, where
   `m := lcm(1, …, kk)`: every weight `q ≤ kk` divides `m`, so `O(m)` is invertible, and
   `x_{i,q}^{m/q} = splitTwistMul (x_{i,q}^{⊗ m/q})` is a global section of the line bundle
   `O(m) ⊗ π^*Q_i^{⊗ m/q}`; locally (over an affine `V` trivializing `Q_i`, `π⁻¹V = Proj O(V)[x]`) it is
   `Proj.basicOpen x_{i,q}^{m/q} = Proj.basicOpen x_{i,q}`.
   We do not take the non-vanishing locus of `x_{i,q}` itself: in the weighted case `O(q)` need not be
   invertible, and the locus where "the section is nonzero on the fiber" may be larger than `D_+(x_{i,q})`. -/

/-- The line bundle `O(m) ⊗ π^*Q_i^{⊗ m/q}` (`m = lcm(1..kk)`, `q = p.2 + 1`). -/

noncomputable def splitCoordBasicOpen.lineBundle {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (kk : ℕ)
    (p : Fin (n + 1) × Fin kk) :
    (splitWeightedProjectivization F kk).left.Modules :=
  AlgebraicGeometry.Scheme.Modules.tensor
    (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk)
      (((Finset.Icc 1 kk).lcm id : ℕ) : ℤ))
    ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
        ((Finset.Icc 1 kk).lcm id / ((p.2 : ℕ) + 1))))

/-- `O(m) ⊗ π^*Q_i^{⊗ m/q}` is a line bundle: `m = lcm(1..kk) > 0` (`Finset.lcm_eq_zero_iff`) is divisible by
every weight `q ∈ Icc 1 kk` (`Finset.dvd_lcm`), so `m` is sufficiently divisible
(`splitWeightedAlgebra_sufficientlyDivisible_of_dvd`) and `O(m)` is a line bundle
(`relativeProj.isLineBundle_twist`); `Q_i` is a line bundle (`LineBundle.toModules_isLineBundle`), and tensor
powers (`IsLineBundle.tensorPow`), pullbacks (`IsLineBundle.pullback`) and tensor products (`IsLineBundle.tensor`)
of line bundles are line bundles. -/
theorem splitCoordBasicOpen.lineBundle_isLineBundle {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (kk : ℕ)
    (p : Fin (n + 1) × Fin kk) :
    (splitCoordBasicOpen.lineBundle F kk p).IsLineBundle := by
  have hm : 0 < ((Finset.Icc 1 kk).lcm id : ℕ) := by
    refine Nat.pos_of_ne_zero fun h => ?_
    obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h
    simp only [Finset.mem_Icc, id] at hx hx0
    omega
  have hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ ((Finset.Icc 1 kk).lcm id : ℕ) :=
    fun q hq => Finset.dvd_lcm hq
  have htw : (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk)
      (((Finset.Icc 1 kk).lcm id : ℕ) : ℤ)).IsLineBundle :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (splitWeightedAlgebraOf F kk) _
      (splitWeightedAlgebra_sufficientlyDivisible_of_dvd F kk _ hm hdiv)
  have hpow : (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
      ((Finset.Icc 1 kk).lcm id / ((p.2 : ℕ) + 1))).IsLineBundle :=
    SheafOfModules.IsLineBundle.tensorPow _ _
  have hpull : ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
        ((Finset.Icc 1 kk).lcm id / ((p.2 : ℕ) + 1)))).IsLineBundle :=
    SheafOfModules.IsLineBundle.pullback _ _
  exact SheafOfModules.IsLineBundle.tensor _ _

noncomputable def splitCoordBasicOpen {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (kk : ℕ)
    (p : Fin (n + 1) × Fin kk) : (splitWeightedProjectivization F kk).left.Opens :=
  let q := (p.2 : ℕ) + 1
  let m := (Finset.Icc 1 kk).lcm id
  have hq : q ∈ Finset.Icc 1 kk := by simp only [Finset.mem_Icc, q]; omega
  haveI : (splitCoordBasicOpen.lineBundle F kk p).IsLineBundle :=
    splitCoordBasicOpen.lineBundle_isLineBundle F kk p
  (splitCoordBasicOpen.lineBundle F kk p).nonvanishingLocus
    (splitTwistMul F kk p.1 q m (Finset.dvd_lcm hq)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection (splitWeightedCoord F p.1 q hq) (m / q)))

end
