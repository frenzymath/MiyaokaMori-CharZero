import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafComapIdealEqMap
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealBasic

/-! # The inverse image ideal sheaf is multiplicative

The inverse image ideal sheaf is multiplicative: `(I·J)·O_X = (I·O_X)(J·O_X)` for
`f : X → Y` and quasi-coherent ideal sheaves `I, J` on `Y` (Mathlib `IdealSheafData.comap`).

Source: Stacks 01HJ (inverse image of a quasi-coherent ideal sheaf; locally `f⁻¹I·O_X` is
`I(U)·Γ(V)` for affine `V ⊆ f⁻¹U`), and `Ideal.map_mul`. Used in the assembly of Stacks 0AHH
(`I·O_S = (I'·O_S)·O_S(−dβ₂⁻¹E)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Affine opens `V ⊆ f⁻¹U` (`U` affine) cover `X`. -/
theorem iSup_affineOpens_le_preimage_eq_top {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    ⨆ p : {p : X.affineOpens × Y.affineOpens // p.1.1 ≤ f ⁻¹ᵁ p.2.1}, p.1.1.1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨U, hU⟩ := Y.exists_affineOpens_mem (f x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (f ⁻¹ᵁ U.1 : Set X) from hU) (f ⁻¹ᵁ U.1).isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨V, hV⟩, U), fun a ha => hVU ha⟩, hxV⟩

/-- `(I * J).comap f = I.comap f * J.comap f`.

Proof: both sides are quasi-coherent ideal sheaves, so it suffices to compare them on the affine
opens `V ⊆ f⁻¹U` (`U` affine), which cover `X` (`ext_of_iSup_eq_top`). There
`(K.comap f)(V) = K(U)·Γ(V)` (`comap_ideal_eq_map_appLE`)
and `Ideal.map` is multiplicative. -/
theorem comap_mul {X Y : AlgebraicGeometry.Scheme.{u}} (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine IdealSheafData.ext_of_iSup_eq_top (fun p : {p : X.affineOpens × Y.affineOpens //
    p.1.1 ≤ f ⁻¹ᵁ p.2.1} => p.1.1) (iSup_affineOpens_le_preimage_eq_top f) ?_
  rintro ⟨⟨V, U⟩, hVU⟩
  rw [IdealSheafData.ideal_mul, Pi.mul_apply,
    IdealSheafData.comap_ideal_eq_map_appLE (I * J) f U V hVU,
    IdealSheafData.comap_ideal_eq_map_appLE I f U V hVU,
    IdealSheafData.comap_ideal_eq_map_appLE J f U V hVU,
    IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

end AlgebraicGeometry.Scheme.IdealSheafData

end
