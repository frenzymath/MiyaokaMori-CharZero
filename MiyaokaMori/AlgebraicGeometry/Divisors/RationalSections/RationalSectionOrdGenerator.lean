import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdCoordinate

/-! # The order of a rational section through an arbitrary generator

Let `W` be integral and locally Noetherian, `M` a line bundle on `W`, `z ∈ W`, `t` **any** generator of
`M_z` as an `O_{W,z}`-module, `s` a nonzero element of the generic stalk and `g ∈ K(W)` with
`g • (image of t at the generic point) = s`. Then `rationalSectionOrd M s z = ord_z(g)` (the
well-definedness of Stacks 02SE).

Proof: take a rank-one trivialization `e_U` near `z` (`exists_trivialization`), with generic coordinate `c`
and stalk coordinate `e_z`. Since `t` generates `M_z`, `e_z(t)` is a unit, so `ord_z(c(j t)) = 0`
(`ord_algebraMap_of_isUnit`); `c(s) = g·c(j t)`; and `rationalSectionOrd_eq_ord_genericCoordinate` gives
`ord_{z,M}(s) = ord_z(c(s)) = ord_z(g)`. (Stacks 02SE, 02SH.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Divisors AlgebraicGeometry.Divisors.LineGenericCoordinates

variable {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]

/-- The "arbitrary generator" characterization of `rationalSectionOrd`: if `t` is any generator of `M_z` and
`g • (image of t at the generic point) = s`, then `ord_{z,M}(s) = ord_z(g)` (the well-definedness of
Stacks 02SE). -/
theorem rationalSectionOrd_eq_ord_of_generator (M : W.Modules) [M.IsLineBundle] (z : W)
    (t : M.presheaf.stalk z) (ht : Submodule.span (W.presheaf.stalk z) {t} = ⊤)
    (g : W.functionField) (s : M.stalk (genericPoint W)) (hs : s ≠ 0)
    (hg : g • moduleStalkToGenericFiber W M z t = s) :
    M.rationalSectionOrd s z = W.ord g z := by
  obtain ⟨U, hz, ⟨eU⟩⟩ := exists_trivialization M z
  let ez := lineStalkEquivOfTrivialization W M U ⟨z, hz⟩ eU
  let c := genericCoordinate W M U ⟨⟨z, hz⟩⟩ eU
  let j := moduleStalkToGenericFiber W M z
  have hj : ∀ m, c (j m) = algebraMap (W.presheaf.stalk z) W.functionField (ez m) :=
    fun m => lineStalkEquivOfTrivialization_toGenericFiber W M U eU ⟨z, hz⟩ _ m
  have hu : IsUnit (ez t) := by
    have hmem : ez.symm 1 ∈ Submodule.span (W.presheaf.stalk z) {t} := by
      rw [ht]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : a * ez t = 1 := by
      have h2 := (ez.map_smul a t).symm.trans (congrArg ez ha)
      rwa [LinearEquiv.apply_symm_apply, smul_eq_mul] at h2
    exact IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact h1)
  have hcu : c (j t) ≠ 0 := by
    rw [hj]
    exact (IsUnit.map (algebraMap (W.presheaf.stalk z) W.functionField) hu).ne_zero
  have hcs : c s = g * c (j t) := (congrArg c hg.symm).trans (c.map_smul g (j t))
  have hg0 : g ≠ 0 := by
    intro h0
    apply hs
    exact hg.symm.trans (by rw [h0]; exact zero_smul _ _)
  have h0 : W.ord (c (j t)) z = 0 := by
    rw [hj]; exact ord_algebraMap_of_isUnit z hu
  rw [rationalSectionOrd_eq_ord_genericCoordinate M U z hz eU s hs]
  show W.ord (c s) z = W.ord g z
  rw [hcs, Scheme.ord_mul hg0 hcu, h0, add_zero]

omit [IsIntegral W] [IsLocallyNoetherian W] in
/-- The stalk of a line bundle is free of rank one: `M_z` has a generator. -/
theorem exists_stalk_generator (M : W.Modules) [M.IsLineBundle] (z : W) :
    ∃ t : M.presheaf.stalk z, Submodule.span (W.presheaf.stalk z) {t} = ⊤ := by
  obtain ⟨U, hz, ⟨eU⟩⟩ := exists_trivialization M z
  let ez := lineStalkEquivOfTrivialization W M U ⟨z, hz⟩ eU
  refine ⟨ez.symm 1, ?_⟩
  rw [eq_top_iff]
  intro m _
  refine Submodule.mem_span_singleton.mpr ⟨ez m, ?_⟩
  apply ez.injective
  exact (ez.map_smul _ _).trans (by rw [LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one])

omit [IsLocallyNoetherian W] in
/-- The generic stalk is a one-dimensional `K(W)`-space: for a generator `t` of `M_z`, every `s` is a
`K(W)`-multiple of the image of `t`. -/
theorem exists_smul_toGenericFiber_eq (M : W.Modules) [M.IsLineBundle] (z : W)
    (t : M.presheaf.stalk z) (ht : Submodule.span (W.presheaf.stalk z) {t} = ⊤)
    (s : M.stalk (genericPoint W)) :
    ∃ g : W.functionField, g • moduleStalkToGenericFiber W M z t = s := by
  obtain ⟨U, hz, ⟨eU⟩⟩ := exists_trivialization M z
  let ez := lineStalkEquivOfTrivialization W M U ⟨z, hz⟩ eU
  let c := genericCoordinate W M U ⟨⟨z, hz⟩⟩ eU
  let j := moduleStalkToGenericFiber W M z
  have hj : ∀ m, c (j m) = algebraMap (W.presheaf.stalk z) W.functionField (ez m) :=
    fun m => lineStalkEquivOfTrivialization_toGenericFiber W M U eU ⟨z, hz⟩ _ m
  have hu : IsUnit (ez t) := by
    have hmem : ez.symm 1 ∈ Submodule.span (W.presheaf.stalk z) {t} := by
      rw [ht]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : a * ez t = 1 := by
      have h2 := (ez.map_smul a t).symm.trans (congrArg ez ha)
      rwa [LinearEquiv.apply_symm_apply, smul_eq_mul] at h2
    exact IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact h1)
  have hcu : c (j t) ≠ 0 := by
    rw [hj]
    exact (IsUnit.map (algebraMap (W.presheaf.stalk z) W.functionField) hu).ne_zero
  refine ⟨c s / c (j t), ?_⟩
  apply c.injective
  exact (c.map_smul _ _).trans (by rw [smul_eq_mul, div_mul_cancel₀ _ hcu])

end AlgebraicGeometry.Scheme.Modules
end
