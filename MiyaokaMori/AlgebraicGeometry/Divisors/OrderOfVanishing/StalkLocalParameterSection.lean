import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# A section representing a local parameter of a DVR stalk

At a codimension-one point of an integral locally Noetherian scheme, an irreducible
element of a DVR stalk is represented by a section on an actual open neighbourhood.
Its image in the same scheme's function field has order one.

This is the local representative step (a local parameter at a point of the curve) used in the
proof of Lemma 3.1 of the paper. The DVR hypothesis is
explicit here; deriving it for the original smooth curve is a separate geometric step.
The proof uses the stalk colimit representation and Mathlib's normalization of
`Ring.ordFrac` on an irreducible element of a DVR.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Divisors

/-- A DVR stalk has an irreducible local section whose function-field image has order one. -/
theorem exists_local_parameter_section (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (z : X) (hz : Order.coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] :
    ∃ (U : X.Opens) (hzU : z ∈ U),
      letI : Nonempty U := ⟨⟨z, hzU⟩⟩
      ∃ (π : Γ(X, U)), Irreducible (X.presheaf.germ U z hzU π) ∧
        X.ord (X.germToFunctionField U π) z = 1 := by
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  obtain ⟨U, hzU, π, hπ⟩ := X.presheaf.exists_germ_eq a
  let : Nonempty U := ⟨⟨z, hzU⟩⟩
  refine ⟨U, hzU, π, ?_, ?_⟩
  · simpa only [hπ] using ha
  · rw [← X.algebraMap_germ_eq_germToFunctionField hzU π, hπ]
    have ha' : algebraMap (X.presheaf.stalk z) X.functionField a ≠ 0 := by
      intro h
      apply ha.ne_zero
      exact IsFractionRing.injective (X.presheaf.stalk z) X.functionField (by simpa using h)
    apply (Scheme.ord_eq_iff hz ha').mpr
    simpa only [Scheme.ordHom, WithZero.exp_eq_coe_ofAdd] using
      (Ring.ordFrac_irreducible (K := X.functionField) ha)

end AlgebraicGeometry.Divisors
