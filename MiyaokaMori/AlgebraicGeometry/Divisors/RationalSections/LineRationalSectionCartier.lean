import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRank
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierLocalData

/-!
# Cartier presentations of the same line module and rational section

`LineCartierPresentation X M s` binds a `CartierLocalData X.scheme`
to the nonzero section `s` of the same module's generic stalk. Every cover member
has an actual rank-one frame. On each nonempty member its Cartier equation is
exactly the coordinate of `s` in that frame, computed by `LineGenericCoordinates`.
The already-defined Cartier data retain actual global unit ratios on overlaps.

This is a data relation that may be quantified in the intersection relation without selecting from
an existence theorem. For the cap construction, `M` is the actual pullback of the target line to an
integral closed curve, and `X.toBase` is that curve's given composite structure map.
No rational function on the target is pulled back along a non-dominant immersion.

The representation existence theorem requires a Noetherian scheme so that a
finite trivializing subcover supplies the locally finite cover required by the
Cartier data. Its proof constructs the overlap units from the same
frames; pointwise stalk units alone are not its global overlap-unit conclusion.
Changing frames for the same section preserves coefficients. Changing the
section changes them by the actual principal divisor of the ratio, with positive
sign. Principal degree zero and numerical independence remain separate obligations.

Sources: Theorem 1.1 of the paper and the proof of Proposition 2.4; Stacks Project
`divisors.tex`,
`section-c1`, `lemma-regular-meromorphic-section-exists-noetherian` and
`lemma-divisor-meromorphic-well-defined`; `chow.tex`,
`definition-divisor-invertible-sheaf` and `definition-cap-c1` (Tag 02SO).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Divisors
open AlgebraicGeometry.Proj AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]

/-- An actual Cartier presentation whose local equations are the coordinates of the
specified nonzero rational section in genuine frames of the same module sheaf. -/
structure LineCartierPresentation (X : SchemeOver k) [IsIntegral X.scheme]
    [IsLocallyNoetherian X.scheme] (M : X.scheme.Modules)
    (s : M.presheaf.stalk (genericPoint X.scheme)) where
  section_ne_zero : s ≠ 0
  cartier : Intersection.CartierLocalData X.scheme
  frame : ∀ i : cartier.index, M.restrict (cartier.opens i).ι ≅
    SheafOfModules.free (R := (cartier.opens i).toScheme.ringCatSheaf) (ULift.{u} (Fin 1))
  equation_eq : ∀ i (hU : Nonempty (cartier.opens i)),
    cartier.equation i =
      LineGenericCoordinates.genericCoordinate X.scheme M (cartier.opens i) hU (frame i) s

/-- A Cartier presentation's actual frame cover witnesses the same rank-one predicate. -/
theorem LineCartierPresentation.isLocallyFreeRank {X : SchemeOver k} [IsIntegral X.scheme]
    [IsLocallyNoetherian X.scheme] {M : X.scheme.Modules}
    {s : M.presheaf.stalk (genericPoint X.scheme)} (P : LineCartierPresentation X M s) :
    IsLocallyFreeRank X M 1 := by
  constructor
  intro x
  have hx : x ∈ ⋃ i, (P.cartier.opens i : Set X.scheme) := by
    rw [P.cartier.cover]
    exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨P.cartier.opens i, hi, ⟨P.frame i⟩⟩

/-- A genuine rank-one module has a nonzero section in its actual generic stalk. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank.exists_nonzero_genericSection {X : SchemeOver k}
    [IsIntegral X.scheme] {M : X.scheme.Modules} (hM : IsLocallyFreeRank X M 1) :
    ∃ s : M.presheaf.stalk (genericPoint X.scheme), s ≠ 0 := by
  obtain ⟨U, hη, ⟨e⟩⟩ := hM.local_frame (genericPoint X.scheme)
  let c := LineGenericCoordinates.lineStalkEquivOfTrivialization X.scheme M U
    ⟨genericPoint X.scheme, hη⟩ e
  refine ⟨c.symm 1, ?_⟩
  intro h
  have h10 : (1 : X.scheme.functionField) = 0 := by
    calc
      1 = c (c.symm 1) := (c.apply_symm_apply 1).symm
      _ = c 0 := congrArg c h
      _ = 0 := map_zero c
  exact one_ne_zero h10

/- The existence theorem `exists_lineCartierPresentation` needs the finite frame cover and the
whole-overlap unit construction, both of which live downstream of this module; it is therefore
declared in `MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineCartierFinitePresentation`. -/

/-- Changing the actual frame cover for the same rational section preserves every
Cartier order coefficient, even when the covers and index types differ. -/
theorem lineCartierPresentation_coefficient_eq {X : SchemeOver k} [IsIntegral X.scheme]
    [IsLocallyNoetherian X.scheme] {M : X.scheme.Modules}
    {s : M.presheaf.stalk (genericPoint X.scheme)}
    (P Q : LineCartierPresentation X M s) (x : X.scheme) :
    P.cartier.coefficient x = Q.cartier.coefficient x := by
  classical
  by_cases hx : Order.coheight x = 1
  · let i := P.cartier.indexAt x
    let j := Q.cartier.indexAt x
    have hxi : x ∈ P.cartier.opens i := P.cartier.indexAt_mem x
    have hxj : x ∈ Q.cartier.opens j := Q.cartier.indexAt_mem x
    obtain ⟨a, ha⟩ := LineGenericCoordinates.genericCoordinate_ratio_is_local_unit
      X.scheme M (P.cartier.opens i) (Q.cartier.opens j) x hxi hxj
      (P.frame i) (Q.frame j) s P.section_ne_zero
    rw [← P.equation_eq i ⟨⟨x, hxi⟩⟩, ← Q.equation_eq j ⟨⟨x, hxj⟩⟩] at ha
    have hunit : X.scheme.ord (P.cartier.equation i / Q.cartier.equation j) x = 0 := by
      apply (Scheme.ord_eq_iff hx
        (div_ne_zero (P.cartier.equation_ne_zero i) (Q.cartier.equation_ne_zero j))).2
      rw [← ha]
      have : Ring.KrullDimLE 1 (X.scheme.presheaf.stalk x) :=
        krullDimLE_of_coheight_le hx.le
      change Ring.ordFrac (X.scheme.presheaf.stalk x)
        (algebraMap (X.scheme.presheaf.stalk x) X.scheme.functionField
          (a : X.scheme.presheaf.stalk x)) = 1
      exact Ring.ordFrac_of_isUnit a.isUnit
    rw [P.cartier.coefficient_eq_ord x hx, Q.cartier.coefficient_eq_ord x hx]
    change X.scheme.ord (P.cartier.equation i) x = X.scheme.ord (Q.cartier.equation j) x
    calc
      X.scheme.ord (P.cartier.equation i) x =
          X.scheme.ord ((P.cartier.equation i / Q.cartier.equation j) *
            Q.cartier.equation j) x := by
        rw [div_mul_cancel₀ _ (Q.cartier.equation_ne_zero j)]
      _ = X.scheme.ord (P.cartier.equation i / Q.cartier.equation j) x +
          X.scheme.ord (Q.cartier.equation j) x :=
        Scheme.ord_mul (x := x)
          (div_ne_zero (P.cartier.equation_ne_zero i) (Q.cartier.equation_ne_zero j))
          (Q.cartier.equation_ne_zero j)
      _ = X.scheme.ord (Q.cartier.equation j) x := by rw [hunit, zero_add]
  · rw [P.cartier.coefficient_eq_zero_of_coheight_ne_one x hx,
      Q.cartier.coefficient_eq_zero_of_coheight_ne_one x hx]

/-- Two nonzero rational sections of the same line differ by one nonzero rational
function, and their Cartier coefficients differ by its actual principal divisor. -/
theorem lineCartierPresentation_change_section {X : SchemeOver k} [IsIntegral X.scheme]
    [IsLocallyNoetherian X.scheme] {M : X.scheme.Modules}
    {s t : M.presheaf.stalk (genericPoint X.scheme)}
    (P : LineCartierPresentation X M s) (Q : LineCartierPresentation X M t) :
    ∃ a : X.scheme.functionFieldˣ, s = (a : X.scheme.functionField) • t ∧
      ∀ x : X.scheme, P.cartier.coefficient x =
        Q.cartier.coefficient x + X.scheme.ord (a : X.scheme.functionField) x := by
  classical
  let i := Q.cartier.indexAt (genericPoint X.scheme)
  have hU : Nonempty (Q.cartier.opens i) :=
    ⟨⟨genericPoint X.scheme, Q.cartier.indexAt_mem (genericPoint X.scheme)⟩⟩
  let c := LineGenericCoordinates.genericCoordinate X.scheme M (Q.cartier.opens i) hU (Q.frame i)
  have hcs : c s ≠ 0 := LineGenericCoordinates.genericCoordinate_ne_zero X.scheme M
    (Q.cartier.opens i) hU (Q.frame i) s P.section_ne_zero
  have hct : c t ≠ 0 := LineGenericCoordinates.genericCoordinate_ne_zero X.scheme M
    (Q.cartier.opens i) hU (Q.frame i) t Q.section_ne_zero
  let a : X.scheme.functionFieldˣ := Units.mk0 (c s / c t) (div_ne_zero hcs hct)
  have ha : s = (a : X.scheme.functionField) • t := by
    apply c.injective
    change c s = c ((c s / c t) • t)
    rw [_root_.map_smul, smul_eq_mul, div_mul_cancel₀ _ hct]
  let R : LineCartierPresentation X M s :=
    { section_ne_zero := P.section_ne_zero
      cartier :=
        { index := Q.cartier.index
          opens := Q.cartier.opens
          cover := Q.cartier.cover
          locallyFinite := Q.cartier.locallyFinite
          equation := fun j ↦ (a : X.scheme.functionField) * Q.cartier.equation j
          equation_ne_zero := fun j ↦ mul_ne_zero a.ne_zero (Q.cartier.equation_ne_zero j)
          ratio_unit := by
            intro j l hV
            obtain ⟨v, hv, heq⟩ := Q.cartier.ratio_unit j l hV
            exact ⟨v, hv, heq.trans
              (mul_div_mul_left (Q.cartier.equation j) (Q.cartier.equation l) a.ne_zero).symm⟩ }
      frame := Q.frame
      equation_eq := by
        intro j hV
        change (a : X.scheme.functionField) * Q.cartier.equation j =
          LineGenericCoordinates.genericCoordinate X.scheme M (Q.cartier.opens j) hV
            (Q.frame j) s
        rw [ha, _root_.map_smul, smul_eq_mul, Q.equation_eq j hV] }
  refine ⟨a, ha, fun x ↦ ?_⟩
  calc
    P.cartier.coefficient x = R.cartier.coefficient x :=
      lineCartierPresentation_coefficient_eq P R x
    _ = Q.cartier.coefficient x + X.scheme.ord (a : X.scheme.functionField) x := by
      by_cases hx : Order.coheight x = 1
      · rw [R.cartier.coefficient_eq_ord x hx, Q.cartier.coefficient_eq_ord x hx]
        change X.scheme.ord ((a : X.scheme.functionField) *
          Q.cartier.equation (Q.cartier.indexAt x)) x =
            X.scheme.ord (Q.cartier.equation (Q.cartier.indexAt x)) x +
              X.scheme.ord (a : X.scheme.functionField) x
        rw [Scheme.ord_mul a.ne_zero (Q.cartier.equation_ne_zero _), add_comm]
      · rw [R.cartier.coefficient_eq_zero_of_coheight_ne_one x hx,
          Q.cartier.coefficient_eq_zero_of_coheight_ne_one x hx,
          Scheme.ord_eq_zero_of_coheight_neq_one hx, add_zero]

end AlgebraicGeometry.Divisors
