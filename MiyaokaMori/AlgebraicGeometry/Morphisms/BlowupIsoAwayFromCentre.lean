import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupOpenIso

/-! # A point blowup is an isomorphism away from its centre

A blowup at a point characterised by its universal property
(`MiyaokaMori.Statement.IsBlowup (pointIdeal Y c) b`) is an isomorphism over every open subset not
containing the centre `c`.

Reference: [Stacks, 02OS(1)] (a blowup is an isomorphism away from its centre); used for the
resolved ruled surface of Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- If the centre `c` does not lie in the open subset `V`, then the pullback of the point ideal
sheaf to `V` is the unit ideal.

Proof: `I := pointIdeal Y c = (Y.fromSpecResidueField c).ker` has support `closure {c}`
(`Scheme.Hom.support_ker` and `Scheme.range_fromSpecResidueField`; the source is a point, hence
quasi-compact). As `V` is open and `c ∉ V`, we get `closure {c} ∩ V = ∅` (if `y ∈ closure {c} ∩ V`,
then `V` is an open neighbourhood of `y` meeting `{c}`, i.e. `c ∈ V`). Hence `I.comap V.ι` has empty
support (`IdealSheafData.support_comap`), so `I.comap V.ι = ⊤` (`support_eq_bot_iff`).
The point `c` need not be closed (compare `pointIdeal_comap_eq_top_of_avoids`, which assumes
`IsClosed {c}`). -/
theorem MiyaokaMori.Statement.pointIdeal_comap_ι_eq_top_of_notMem {Y : Scheme.{u}} (c : Y)
    (V : Y.Opens) (hV : c ∉ V) :
    (MiyaokaMori.Statement.pointIdeal Y c).comap V.ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext t
  change V.ι t ∈ ((MiyaokaMori.Statement.pointIdeal Y c).support : Set Y) ↔ t ∈ (∅ : Set V)
  rw [MiyaokaMori.Statement.pointIdeal, Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField]
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have ht : V.ι t ∈ (V : Set Y) := t.2
  obtain ⟨y, hyV, hyc⟩ := mem_closure_iff.mp h (V : Set Y) V.isOpen ht
  exact hV (Set.mem_singleton_iff.mp hyc ▸ hyV)

/-- A point blowup is an isomorphism over every open subset avoiding the centre.

Proof (using only the universal property): by `pointIdeal_comap_ι_eq_top_of_notMem` we have
`I.comap V.ι = ⊤`, and `IsBlowup.isIsoOverOpen_of_comap_eq_top` ([Stacks, 02OS(1)]: a blowup is an
isomorphism over an open subset on which the centre ideal is the unit ideal) applies: the universal
property for `T = V`, `f = V.ι` gives a unique lift `s`, which lands in `b⁻¹V` and inverts `b ∣_ V`;
both composites are the identity because `V.ι` is a monomorphism and the lift is unique. -/
theorem MiyaokaMori.Statement.IsBlowup.isIso_morphismRestrict_pointIdeal {Y Z : Scheme.{u}} (c : Y)
    (b : Z ⟶ Y) (hb : MiyaokaMori.Statement.IsBlowup (MiyaokaMori.Statement.pointIdeal Y c) b)
    (V : Y.Opens) (hV : c ∉ V) : IsIso (b ∣_ V) :=
  hb.isIsoOverOpen_of_comap_eq_top V
    (MiyaokaMori.Statement.pointIdeal_comap_ι_eq_top_of_notMem c V hV)

end
