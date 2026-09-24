import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.CapCommutes
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapDivisorEqFirstChernClass
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.DivisorToOneCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02sp
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.SurfaceIntersectionPairingWeilCycleSection

/-! # The intersection pairing on a smooth projective surface

The intersection pairing of Cartier divisors on a smooth projective surface: `D·E := deg(D ∩ [E])`
(the Weil cycle of `E` is a one-cycle); it is symmetric and bilinear.

Source: Hartshorne V.1 / Fulton, Intersection Theory, 2.4.

- Symmetry (Fulton Cor. 2.4.2): `D ∩ [E] = c₁(O(D)) ∩ [E]` (`capDivisor_eq_firstChernClass`); in `A_1(S)`,
  `[E] = c₁(O(E)) ∩ [S]` (`SurfaceIntersectionPairingWeilCycleSection`: `[E] = div_{O(E)}(s)`,
  Hartshorne II.6.13 + Stacks 02SJ); the caps with two `c₁`'s commute (`firstChernClass_comm`,
  Stacks 02TJ), so `D ∩ [E] = c₁(O(D)) ∩ c₁(O(E)) ∩ [S] = c₁(O(E)) ∩ c₁(O(D)) ∩ [S] = E ∩ [D]`; take degrees.
- Additivity and negation on the left: `capDivisor_add` / `capDivisor_neg` (Stacks 02SP), and the degree
  is an additive homomorphism. The versions on the right follow by symmetry.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The intersection pairing `D·E := deg(D ∩ [E])` of Cartier divisors on a smooth projective surface. -/
noncomputable def surfaceIntersection {k : Type u} [Field k] [IsAlgClosed k] (S : SmoothProjectiveSurface k)
    (D E : CartierDivisor S.toVariety) : ℤ :=
  intersectionNumber S.toSmoothProjectiveVariety D
    (SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S ▸ E.weilCycle)

/-- The underlying cycle of the transport `cycleGroup_dim_sub_one_eq_oneCycle S ▸ E.weilCycle` is the
underlying cycle of `[E]` (`▸` only rewrites the index `dim S − 1 = 1`). -/
theorem SmoothProjectiveSurface.coe_cast_weilCycle {k : Type u} [Field k] (S : SmoothProjectiveSurface k)
    (E : CartierDivisor S.toVariety) :
    ((SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S ▸ E.weilCycle : OneCycle S.toVariety) :
        AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) =
      (CartierDivisor.weilCycle S.toVariety E : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) := by
  have coe_cast {i j : ℕ} (h : i = j) (c : CycleGroup S.toVariety i) :
      ((cast (congrArg (fun n : ℕ ↦ ↥(CycleGroup S.toVariety n)) h) c :
        CycleGroup S.toVariety j) : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) = c.1 := by
    cases h
    rfl
  have hdim : S.toVariety.dimension - 1 = 1 := by
    rw [show S.toVariety.dimension = 2 from
      (Variety.dim_eq_scheme_dimension S.toVariety).symm.trans S.dim_eq_two]
  have htype : SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S =
      congrArg (fun n : ℕ ↦ ↥(CycleGroup S.toVariety n)) hdim := Subsingleton.elim _ _
  rw [htype]
  exact coe_cast hdim _

/-- In the Chow group `A_1(S)`, `[E] = c₁(O_S(E)) ∩ [S]` (the surface-divisor form of Stacks 02SJ). -/
theorem SmoothProjectiveSurface.chowMk_weilCycle_eq_firstChernClass_cap {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) (E : CartierDivisor S.toVariety) :
    AlgebraicGeometry.ChowGroup.mk
        (SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S ▸ E.weilCycle : OneCycle S.toVariety) =
      AlgebraicGeometry.firstChernClass E.lineBundle.toModules 2 (S.toScheme.fundamentalChowClass 2) := by
  have hdim : S.toScheme.dimension = 1 + 1 :=
    (Variety.dim_eq_scheme_dimension S.toVariety).symm.trans S.dim_eq_two
  have hmem : (CartierDivisor.weilCycle S.toVariety E : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) ∈
      AlgebraicGeometry.cycleSubgroup S.toScheme 1 := by
    rw [← SmoothProjectiveSurface.coe_cast_weilCycle S E]
    exact (SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S ▸ E.weilCycle : OneCycle S.toVariety).2
  rw [← CartierDivisor.chowMk_weilCycle_eq_firstChernClass_cap_fundamentalChowClass S.toVariety E 1 hdim hmem]
  congr 1
  exact Subtype.ext (SmoothProjectiveSurface.coe_cast_weilCycle S E)

theorem surfaceIntersection_comm {k : Type u} [Field k] [IsAlgClosed k] (S : SmoothProjectiveSurface k)
    (D E : CartierDivisor S.toVariety) : surfaceIntersection S D E = surfaceIntersection S E D := by
  unfold surfaceIntersection intersectionNumber
  congr 1
  rw [capDivisor_eq_firstChernClass, capDivisor_eq_firstChernClass]
  change AlgebraicGeometry.firstChernClass D.lineBundle.toModules 1 (AlgebraicGeometry.ChowGroup.mk
      (SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S ▸ E.weilCycle : OneCycle S.toVariety)) =
    AlgebraicGeometry.firstChernClass E.lineBundle.toModules 1 (AlgebraicGeometry.ChowGroup.mk
      (SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S ▸ D.weilCycle : OneCycle S.toVariety))
  rw [SmoothProjectiveSurface.chowMk_weilCycle_eq_firstChernClass_cap S E,
    SmoothProjectiveSurface.chowMk_weilCycle_eq_firstChernClass_cap S D]
  have h := AlgebraicGeometry.firstChernClass_comm (k := k) D.lineBundle.toModules E.lineBundle.toModules 0
  exact DFunLike.congr_fun h (S.toScheme.fundamentalChowClass 2)

theorem surfaceIntersection_add_left {k : Type u} [Field k] [IsAlgClosed k] (S : SmoothProjectiveSurface k)
    (D D' E : CartierDivisor S.toVariety) :
    surfaceIntersection S (D + D') E = surfaceIntersection S D E + surfaceIntersection S D' E := by
  unfold surfaceIntersection intersectionNumber
  rw [capDivisor_add, AddMonoidHom.add_apply, map_add]

theorem surfaceIntersection_neg_left {k : Type u} [Field k] [IsAlgClosed k] (S : SmoothProjectiveSurface k)
    (D E : CartierDivisor S.toVariety) :
    surfaceIntersection S (-D) E = - surfaceIntersection S D E := by
  unfold surfaceIntersection intersectionNumber
  rw [capDivisor_neg, AddMonoidHom.neg_apply, map_neg]

theorem surfaceIntersection_add_right {k : Type u} [Field k] [IsAlgClosed k] (S : SmoothProjectiveSurface k)
    (D E E' : CartierDivisor S.toVariety) :
    surfaceIntersection S D (E + E') = surfaceIntersection S D E + surfaceIntersection S D E' := by
  rw [surfaceIntersection_comm S D (E + E'), surfaceIntersection_add_left,
    surfaceIntersection_comm S E D, surfaceIntersection_comm S E' D]

theorem surfaceIntersection_neg_right {k : Type u} [Field k] [IsAlgClosed k] (S : SmoothProjectiveSurface k)
    (D E : CartierDivisor S.toVariety) :
    surfaceIntersection S D (-E) = - surfaceIntersection S D E := by
  rw [surfaceIntersection_comm S D (-E), surfaceIntersection_neg_left, surfaceIntersection_comm S E D]

end
