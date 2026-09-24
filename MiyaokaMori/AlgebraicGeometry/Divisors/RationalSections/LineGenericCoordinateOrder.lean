import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Independence of generic-coordinate order from a local frame

Two rank-one frames of the same module sheaf give rational coordinates for the same nonzero
generic section. At a point in both frame domains, their quotient is the canonical image of a
unit of the actual local ring. Its order is zero, so the two coordinates have the same order.

This is the local frame comparison in the Stacks Project, `divisors.tex`, preceding
`definition-order-vanishing-meromorphic`. It supplies local arithmetic for the line-section
divisor `D_L` in the proof of Lemma 3.1 of the paper.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Divisors.LineGenericCoordinateOrder

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The order of a nonzero generic section in a rank-one frame is independent of the frame
at every point common to the two frame domains. -/
theorem ord_genericCoordinate_eq
    (M : X.Modules) (U V : X.Opens) (x : X)
    (hxU : x ∈ U) (hxV : x ∈ V)
    (eU : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (eV : M.restrict V.ι ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (s : M.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    X.ord (LineGenericCoordinates.genericCoordinate X M U ⟨⟨x, hxU⟩⟩ eU s) x =
      X.ord (LineGenericCoordinates.genericCoordinate X M V ⟨⟨x, hxV⟩⟩ eV s) x := by
  let f := LineGenericCoordinates.genericCoordinate X M U ⟨⟨x, hxU⟩⟩ eU s
  let g := LineGenericCoordinates.genericCoordinate X M V ⟨⟨x, hxV⟩⟩ eV s
  have hf : f ≠ 0 := LineGenericCoordinates.genericCoordinate_ne_zero X M U _ eU s hs
  have hg : g ≠ 0 := LineGenericCoordinates.genericCoordinate_ne_zero X M V _ eV s hs
  obtain ⟨a, ha⟩ :=
    LineGenericCoordinates.genericCoordinate_ratio_is_local_unit X M U V x hxU hxV eU eV s hs
  have hratio : X.ord (f / g) x = 0 := by
    by_cases hx : Order.coheight x = 1
    · have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
      apply (Scheme.ord_eq_iff hx (div_ne_zero hf hg)).2
      change Ring.ordFrac (X.presheaf.stalk x) (f / g) = 1
      rw [← ha]
      exact Ring.ordFrac_of_isUnit a.isUnit
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _
  calc
    X.ord f x = X.ord ((f / g) * g) x := by rw [div_mul_cancel₀ f hg]
    _ = X.ord (f / g) x + X.ord g x := Scheme.ord_mul (div_ne_zero hf hg) hg
    _ = X.ord g x := by rw [hratio, zero_add]

end AlgebraicGeometry.Divisors.LineGenericCoordinateOrder
