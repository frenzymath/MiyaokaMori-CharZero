import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperEqChowProjectiveStep
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperEqChowReduceToIntegral
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperEqChowZeroDim
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bep

/-! # The Snapper intersection number equals the Chow intersection number

The intersection number defined by the leading coefficient of `χ` equals the Chow intersection number
(Fulton, Intersection Theory, Example 18.3.6): on a proper scheme `X` of dimension `d`,
`(L_1⋯L_d·X)_χ = deg(c_1(L_1) ∩ ⋯ ∩ c_1(L_d) ∩ [X])`; in particular the leading coefficient of
`χ(X, L^p)` times `d!` is the top self-intersection in the Chow sense (Lazarsfeld, Positivity in
Algebraic Geometry I, §1.1.C footnote 7 and Ex. 1.1.27; used in the proof of Proposition 2.4
of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `P(k, d)` holds for all `d`, by induction on `d` (the skeleton of the proof of Stacks 0BFI). The case
`d = 0` is `SnapperEqChowZeroDim.lean`; for `d + 1`, first reduce to the integral case
(`SnapperEqChowReduceToIntegral.lean`), then treat the projective integral case with the induction
hypothesis (`SnapperEqChowProjectiveStep.lean`). `SnapperEqChowInDim` is quantified over schemes
projective over `k`, so no reduction from proper to projective schemes (Chow's lemma) is needed. -/
private theorem snapperEqChowInDim_all (k : Type u) [Field k] :
    ∀ d : ℕ, AlgebraicGeometry.SnapperEqChowInDim k d
  | 0 => AlgebraicGeometry.snapperEqChowInDim_zero k
  | d + 1 =>
    AlgebraicGeometry.snapperEqChowInDim_of_integral k (d + 1) fun X _ hX hXproj _ _ hd L _ =>
      AlgebraicGeometry.snapperEqChowFor_of_projective_succ k d (snapperEqChowInDim_all k d)
        X hX hXproj hd L

theorem AlgebraicGeometry.snapperIntersection_eq_chow {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (hXproj : IsProjectiveOver k X)
    [AlgebraicGeometry.IsLocallyNoetherian X]
    {d : ℕ} (hd : X.dimension = d) (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle] :
    AlgebraicGeometry.snapperIntersection X hX hd L
      = AlgebraicGeometry.ChowGroupRat.degree X hX
          (AlgebraicGeometry.RatDivisorOp.capProd
            (fun i => AlgebraicGeometry.ratDivisorOpOfLineBundle (L i)) 0
            ((by simp : d = 0 + Fintype.card (Fin d)) ▸
              ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass d))) :=
  snapperEqChowInDim_all k d X hX hXproj hd L

/- The self-intersection case (used for the harmonic intersection and `TopIntersectionFromEuler.lean`):
   `(L^d · X)` defined by the leading coefficient of `χ` equals the Chow top self-intersection
   `topSelfIntersection`. -/

/-- The successive caps with a list consisting of the single operator `D` are the power of `D` (both
sides have the same type, no transport needed). -/
private theorem capList_eq_capPow_of_forall_eq {X : AlgebraicGeometry.Scheme.{u}}
    (D : AlgebraicGeometry.RatDivisorOp X) :
    ∀ (l : List (AlgebraicGeometry.RatDivisorOp X)) (_ : ∀ D' ∈ l, D' = D) (d : ℕ),
      AlgebraicGeometry.RatDivisorOp.capList l d = AlgebraicGeometry.RatDivisorOp.capPow D l.length d
  | [], _, _ => rfl
  | D' :: l, hl, d => by
    obtain rfl : D' = D := hl D' List.mem_cons_self
    show (AlgebraicGeometry.RatDivisorOp.capList l d).comp (D' (d + l.length)) =
      (AlgebraicGeometry.RatDivisorOp.capPow D' l.length d).comp (D' (d + l.length))
    rw [capList_eq_capPow_of_forall_eq D' l (fun x hx => hl x (List.mem_cons_of_mem _ hx)) d]

/-- The power of the operator of a line bundle on `1 ⊗ c` is `1 ⊗ −` of the iterated integral cap with
`c_1(L)`. -/
private theorem capPow_ratDivisorOpOfLineBundle_tmul {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    ∀ (e d : ℕ) (c : AlgebraicGeometry.ChowGroup X (d + e)),
      AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle L) e d
          ((1 : ℚ) ⊗ₜ[ℤ] c)
        = (1 : ℚ) ⊗ₜ[ℤ] (AlgebraicGeometry.firstChernClass.capPow L e d c)
  | 0, _, _ => rfl
  | e + 1, d, c => by
    show AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle L) e d
        ((AlgebraicGeometry.firstChernClass L (d + e + 1)).ratExtend ((1 : ℚ) ⊗ₜ[ℤ] c)) = _
    rw [show (AlgebraicGeometry.firstChernClass L (d + e + 1)).ratExtend ((1 : ℚ) ⊗ₜ[ℤ] c)
        = (1 : ℚ) ⊗ₜ[ℤ] (AlgebraicGeometry.firstChernClass L (d + e + 1) c) from rfl]
    exact capPow_ratDivisorOpOfLineBundle_tmul L e d _

private theorem chowGroupRat_congr_rec_eq_cast {X : AlgebraicGeometry.Scheme.{u}} {a b c : ℕ}
    (h1 : a = b) (h2 : b = c) (z : AlgebraicGeometry.ChowGroupRat X a) :
    AlgebraicGeometry.ChowGroupRat.congr X h2 (h1 ▸ z)
      = cast (congrArg (AlgebraicGeometry.ChowGroupRat X) (h1.trans h2)) z := by
  subst h1; subst h2; rfl

private theorem cast_one_tmul {X : AlgebraicGeometry.Scheme.{u}} {p q : ℕ} (h : p = q)
    (c : AlgebraicGeometry.ChowGroup X p) :
    cast (congrArg (AlgebraicGeometry.ChowGroupRat X) h)
        (((1 : ℚ) ⊗ₜ[ℤ] c : TensorProduct ℤ ℚ _) : AlgebraicGeometry.ChowGroupRat X p)
      = ((1 : ℚ) ⊗ₜ[ℤ] cast (congrArg (AlgebraicGeometry.ChowGroup X) h) c : TensorProduct ℤ ℚ _) := by
  subst h; rfl

private theorem capPow_cast_one_tmul {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]
    {d m : ℕ} (hm : m = d)
    (h : AlgebraicGeometry.ChowGroupRat X d = AlgebraicGeometry.ChowGroupRat X (0 + m))
    (c : AlgebraicGeometry.ChowGroup X d) :
    AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle L) m 0
        (cast h (((1 : ℚ) ⊗ₜ[ℤ] c : TensorProduct ℤ ℚ _) : AlgebraicGeometry.ChowGroupRat X d))
      = ((1 : ℚ) ⊗ₜ[ℤ] AlgebraicGeometry.firstChernClass.capPow L d 0
          (cast (congrArg (AlgebraicGeometry.ChowGroup X) (zero_add d).symm) c) :
            TensorProduct ℤ ℚ _) := by
  subst hm
  rw [← capPow_ratDivisorOpOfLineBundle_tmul]
  exact congrArg _ (cast_one_tmul (zero_add m).symm c)

theorem AlgebraicGeometry.snapperIntersection_self_eq_topSelfIntersection {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (hXproj : IsProjectiveOver k X)
    {d : ℕ} (hd : X.dimension = d) (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.snapperIntersection X hX hd (fun _ => L)
      = (AlgebraicGeometry.topSelfIntersection X hX L : ℚ) := by
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  subst hd
  rw [AlgebraicGeometry.snapperIntersection_eq_chow X hX hXproj rfl (fun _ => L)]
  unfold AlgebraicGeometry.topSelfIntersection AlgebraicGeometry.RatDivisorOp.capProd
  rw [LinearMap.comp_apply,
    capList_eq_capPow_of_forall_eq (AlgebraicGeometry.ratDivisorOpOfLineBundle L) _
      (by intro D' hD'; simp only [List.mem_map] at hD'; obtain ⟨_, _, rfl⟩ := hD'; rfl)]
  erw [chowGroupRat_congr_rec_eq_cast]
  refine (congrArg (AlgebraicGeometry.ChowGroupRat.degree X hX)
    (capPow_cast_one_tmul L (by simp) _ _)).trans ?_
  rw [AlgebraicGeometry.ChowGroupRat.degree_tmul, one_mul]

end
