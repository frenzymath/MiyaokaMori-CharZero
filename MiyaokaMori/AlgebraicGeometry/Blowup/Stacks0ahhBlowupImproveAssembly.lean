import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0ahhLengthSum
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0ahhComapMul
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealComap
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealEqMapGerm
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0ahhBlowupImproveInvertible
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0ahhBlowupImproveLengthTransport
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0ahhBlowupImproveDivide

/-! # Variable-level assembly of the globalized Stacks 0AGT step

The variable-level assembly of the globalized Stacks 0AGT step (`exists_pointBlowup_improve`):
given a morphism `π : W' → W`, a point `x`, an invertible ideal sheaf `E` on `W'` with support
`π⁻¹(x)`, stalk isomorphisms of `π` away from `π⁻¹(x)`, a "local model" `q : X → W'` hitting every
point of `π⁻¹(x)` with a stalk isomorphism, and the 0AGT data `(d, I'_X, T_X)` on `X` for
`(I·O_{W'})·O_X = (E·O_X)^d · I'_X` (with the length sum written exactly as in
`blowup_regularLocalRing_dimTwo_improve`,
via germs at chosen affine opens), produce the divisor `D = dE`, the ideal sheaf `I'` with
`I·O_{W'} = I_D · I'`, the support statement and the strict length inequality.

All the bookkeeping of steps 4–6 of the natural-language proof of `exists_pointBlowup_improve`
happens here, with schemes and morphisms as variables; the concrete inputs (blowup,
0805, 0AGT) are supplied by `Stacks0ahhBlowupImprove.lean`.

Source: Stacks 0AHH proof (second paragraph), Stacks 0AGT.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Stalk ideals along an isomorphism on stalks: the comap of an ideal sheaf along `f` has, at `x`,
the image of the stalk ideal at `f x`, and the image can be undone (`Ideal.comap_map_of_bijective`). -/
theorem stalkIdeal_le_of_map_le {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) {I J : Ideal R} (h : I.map φ ≤ J.map φ) : I ≤ J := by
  calc I = (I.map φ).comap φ := (Ideal.comap_map_of_bijective φ hφ).symm
    _ ≤ (J.map φ).comap φ := Ideal.comap_mono h
    _ = J := Ideal.comap_map_of_bijective φ hφ

/-- **Assembly of the globalized 0AGT step** (variable level). See the module docstring. -/
theorem exists_improve_of_localModel
    {W W' X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian W']
    (π : W' ⟶ W) (x : W) (I : W.IdealSheafData) (hI : (I.support : Set W).Finite)
    (hfin : I.lengthSum hI.toFinset ≠ ⊤) (hxI : x ∈ I.support)
    (E : W'.IdealSheafData) (hE : MiyaokaMori.Statement.IsInvertibleIdeal E)
    (hEsupp : (E.support : Set W') = π ⁻¹' {x})
    (hπiso : ∀ y : W', π y ≠ x → IsIso (π.stalkMap y)) (hπinj : Set.InjOn π {y | π y ≠ x})
    (q : X ⟶ W') (hq : ∀ y : W', π y = x → ∃ y' : X, q y' = y ∧ IsIso (q.stalkMap y'))
    (hEq : MiyaokaMori.Statement.IsInvertibleIdeal (E.comap q))
    (d : ℕ) (I'X : X.IdealSheafData)
    (hprod : ∀ U : X.affineOpens,
      ((I.comap π).comap q).ideal U = (E.comap q).ideal U ^ d * I'X.ideal U)
    (TX : Finset X) (hTX : (I'X.support : Set X) = TX)
    (hsum0 : ∀ (Wf : TX → X.affineOpens) (hWf : ∀ t : TX, t.1 ∈ ((Wf t : X.affineOpens) : X.Opens)),
      ∑ t : TX, Module.length (X.presheaf.stalk t.1)
          (X.presheaf.stalk t.1 ⧸
            (I'X.ideal (Wf t)).map (X.presheaf.germ ((Wf t : X.affineOpens) : X.Opens) t.1 (hWf t)).hom)
        < Module.length (W.presheaf.stalk x) (W.presheaf.stalk x ⧸ I.stalkIdeal x)) :
    ∃ (D : AlgebraicGeometry.EffectiveCartierDivisor W') (I' : W'.IdealSheafData)
      (hI' : (I'.support : Set W').Finite),
      I.comap π = D.idealSheaf * I' ∧ (∀ y ∈ I'.support, π y ∈ I.support) ∧
      I'.lengthSum hI'.toFinset < I.lengthSum hI.toFinset := by
  classical
  -- (0) the 0AGT length sum in terms of stalk ideals (`stalkIdeal_eq_map_germ`)
  have hsum : ∑ y ∈ TX, Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸ I'X.stalkIdeal y) <
      Module.length (W.presheaf.stalk x) (W.presheaf.stalk x ⧸ I.stalkIdeal x) := by
    choose Wf hWf using fun t : TX => X.exists_affineOpens_mem t.1
    have h := hsum0 Wf hWf
    rw [← Finset.sum_coe_sort TX]
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun t _ => ?_) h
    rw [stalkIdeal_eq_map_germ I'X t.1 (Wf t) (hWf t)]
  -- (1) the 0AGT equation as an equation of ideal sheaves on `X`
  have hprod' : (I.comap π).comap q = (E.comap q) ^ d * I'X :=
    IdealSheafData.ext (funext fun U => by
      rw [ideal_mul, Pi.mul_apply, ideal_pow, Pi.pow_apply]; exact hprod U)
  have hEtop : ∀ y : W', π y ≠ x → E.stalkIdeal y = ⊤ := fun y hy =>
    stalkIdeal_eq_top_of_notMem_support E y (fun h => hy (by
      have h' : y ∈ (E.support : Set W') := h
      rwa [hEsupp] at h'))
  -- (2) `I·O_{W'} ≤ E^d`, checked on stalks
  have hle : I.comap π ≤ E ^ d := by
    refine le_of_forall_stalkIdeal_le fun y => ?_
    by_cases hy : π y = x
    · obtain ⟨y', rfl, hiso⟩ := hq y hy
      have hbij : Function.Bijective (q.stalkMap y').hom := ConcreteCategory.bijective_of_isIso _
      have h1 : ((I.comap π).comap q).stalkIdeal y' = ((E.comap q) ^ d * I'X).stalkIdeal y' := by
        rw [hprod']
      rw [stalkIdeal_comap (I.comap π) q y', stalkIdeal_mul, stalkIdeal_pow,
        stalkIdeal_comap E q y'] at h1
      refine stalkIdeal_le_of_map_le _ hbij ?_
      rw [h1, stalkIdeal_pow, Ideal.map_pow]
      exact Ideal.mul_le_left
    · rw [stalkIdeal_pow, hEtop y hy, Ideal.top_pow]
      exact le_top
  -- (3) divide by `E^d`
  obtain ⟨I', hI'eq⟩ :=
    exists_eq_mul_of_le_of_isInvertibleIdeal (isInvertibleIdeal_pow hE d) hle
  -- (4) support of `I'`
  have hsupp : ∀ y ∈ I'.support, π y ∈ I.support := by
    intro y hy
    have h1 : y ∈ (I.comap π).support := by
      rw [hI'eq, support_mul, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup]
      exact Set.mem_union_right _ hy
    rw [support_comap] at h1
    exact h1
  -- (5) `I'_X = I'·O_X` by cancellation
  have hI'X : I'X = I'.comap q := by
    refine eq_of_pow_mul_eq_pow_mul hEq d fun U => ?_
    have h1 : ((I.comap π).comap q).ideal U = ((E.comap q) ^ d * I'X).ideal U := by rw [hprod']
    have h2 : ((I.comap π).comap q).ideal U = ((E ^ d * I').comap q).ideal U := by rw [hI'eq]
    rw [ideal_mul, Pi.mul_apply, ideal_pow, Pi.pow_apply] at h1
    rw [comap_mul, comap_pow, ideal_mul, Pi.mul_apply, ideal_pow, Pi.pow_apply] at h2
    rw [← h1, h2]
  -- (6) finiteness of the support of `I'`
  have hfar : (π ⁻¹' ((hI.toFinset.erase x : Finset W) : Set W)).Finite := by
    refine Set.Finite.preimage ?_ (Finset.finite_toSet _)
    intro y₁ hy₁ y₂ hy₂ h
    have hy₁' : π y₁ ≠ x := (Finset.mem_erase.mp hy₁).1
    have hy₂' : π y₂ ≠ x := (Finset.mem_erase.mp hy₂).1
    exact hπinj hy₁' hy₂' h
  have hfibmem : ∀ y' : X, IsIso (q.stalkMap y') → q y' ∈ I'.support → y' ∈ (TX : Set X) := by
    intro y' hiso hy
    have hbij : Function.Bijective (q.stalkMap y').hom := ConcreteCategory.bijective_of_isIso _
    rw [← hTX]
    show y' ∈ I'X.support
    rw [mem_support_iff_stalkIdeal_ne_top, hI'X, stalkIdeal_comap]
    intro htop
    apply stalkIdeal_ne_top_of_mem_support I' (q y') hy
    rw [← Ideal.comap_map_of_bijective _ hbij (I := I'.stalkIdeal (q y')), htop, Ideal.comap_top]
  have hI' : (I'.support : Set W').Finite := by
    refine (hfar.union (TX.finite_toSet.image q)).subset ?_
    intro y hy
    by_cases hyx : π y = x
    · obtain ⟨y', hqy, hiso⟩ := hq y hyx
      exact Or.inr ⟨y', hfibmem y' hiso (hqy ▸ hy), hqy⟩
    · refine Or.inl ?_
      show π y ∈ (hI.toFinset.erase x : Finset W)
      exact Finset.mem_erase.mpr ⟨hyx, hI.mem_toFinset.mpr (hsupp y hy)⟩
  refine ⟨⟨E ^ d, isInvertibleIdeal_pow hE d⟩, I', hI', hI'eq, hsupp, ?_⟩
  -- (7) the length sums
  set T' := hI'.toFinset with hT'
  set lenW' : W' → ℕ∞ := fun y =>
    Module.length (W'.presheaf.stalk y) (W'.presheaf.stalk y ⧸ I'.stalkIdeal y) with hlenW'
  set lenW : W → ℕ∞ := fun t =>
    Module.length (W.presheaf.stalk t) (W.presheaf.stalk t ⧸ I.stalkIdeal t) with hlenW
  set lenX : X → ℕ∞ := fun y' =>
    Module.length (X.presheaf.stalk y') (X.presheaf.stalk y' ⧸ I'X.stalkIdeal y') with hlenX
  have hterm_far : ∀ y : W', π y ≠ x → lenW' y = lenW (π y) := by
    intro y hy
    have hiso := hπiso y hy
    have hbij : Function.Bijective (π.stalkMap y).hom := ConcreteCategory.bijective_of_isIso _
    have hIy : I'.stalkIdeal y = (I.stalkIdeal (π y)).map (π.stalkMap y).hom := by
      have h1 : (I.comap π).stalkIdeal y = (E ^ d * I').stalkIdeal y := by rw [hI'eq]
      rw [stalkIdeal_comap I π y, stalkIdeal_mul, stalkIdeal_pow, hEtop y hy, Ideal.top_pow,
        Ideal.top_mul] at h1
      exact h1.symm
    show Module.length (W'.presheaf.stalk y) (W'.presheaf.stalk y ⧸ I'.stalkIdeal y) =
      Module.length (W.presheaf.stalk (π y)) (W.presheaf.stalk (π y) ⧸ I.stalkIdeal (π y))
    rw [hIy]
    exact (Module.length_quotient_eq_of_bijective _ hbij _).symm
  have hterm_fib : ∀ y' : X, IsIso (q.stalkMap y') → lenW' (q y') = lenX y' := by
    intro y' hiso
    have hbij : Function.Bijective (q.stalkMap y').hom := ConcreteCategory.bijective_of_isIso _
    show Module.length (W'.presheaf.stalk (q y')) (W'.presheaf.stalk (q y') ⧸ I'.stalkIdeal (q y')) =
      Module.length (X.presheaf.stalk y') (X.presheaf.stalk y' ⧸ I'X.stalkIdeal y')
    rw [hI'X, stalkIdeal_comap]
    exact Module.length_quotient_eq_of_bijective _ hbij _
  have hsplit : I'.lengthSum T' = ∑ y ∈ T'.filter (fun y => π y ≠ x), lenW' y +
      ∑ y ∈ T'.filter (fun y => ¬ (π y ≠ x)), lenW' y :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- far part
  have hfar_le : ∑ y ∈ T'.filter (fun y => π y ≠ x), lenW' y ≤
      ∑ t ∈ hI.toFinset.erase x, lenW t := by
    rw [Finset.sum_congr rfl (fun y hy => hterm_far y (Finset.mem_filter.mp hy).2)]
    have hinj : Set.InjOn π (T'.filter (fun y => π y ≠ x) : Set W') := by
      intro y₁ hy₁ y₂ hy₂ h
      exact hπinj (Finset.mem_filter.mp hy₁).2 (Finset.mem_filter.mp hy₂).2 h
    rw [← Finset.sum_image hinj]
    apply Finset.sum_le_sum_of_subset
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_filter] at hy
    exact Finset.mem_erase.mpr ⟨hy.2, hI.mem_toFinset.mpr (hsupp y (hI'.mem_toFinset.mp hy.1))⟩
  -- fibre part
  have hfib_le : ∑ y ∈ T'.filter (fun y => ¬ (π y ≠ x)), lenW' y ≤ ∑ y' ∈ TX, lenX y' := by
    set S := T'.filter (fun y => ¬ (π y ≠ x)) with hS
    have hSx : ∀ y ∈ S, π y = x := fun y hy => not_not.mp (Finset.mem_filter.mp hy).2
    let g : S → X := fun y => Classical.choose (hq y.1 (hSx y.1 y.2))
    have hg : ∀ y : S, q (g y) = y.1 ∧ IsIso (q.stalkMap (g y)) := fun y =>
      Classical.choose_spec (hq y.1 (hSx y.1 y.2))
    have hterm : ∀ y : S, lenW' y.1 = lenX (g y) := by
      intro y
      rw [← (hg y).1]
      exact hterm_fib (g y) (hg y).2
    have hinj : Set.InjOn g (Finset.univ : Finset S) := by
      intro y₁ _ y₂ _ h
      apply Subtype.ext
      rw [← (hg y₁).1, ← (hg y₂).1, h]
    rw [← Finset.sum_coe_sort S, Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.sum_image hinj]
    apply Finset.sum_le_sum_of_subset
    intro y' hy'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hy'
    have hmem : q (g y) ∈ I'.support := by
      rw [(hg y).1]
      exact hI'.mem_toFinset.mp (Finset.mem_filter.mp y.2).1
    exact hfibmem (g y) (hg y).2 hmem
  -- total
  have hfin' : ∑ t ∈ hI.toFinset.erase x, lenW t ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (Finset.sum_le_sum_of_subset (Finset.erase_subset x _))
  have hx' : x ∈ hI.toFinset := hI.mem_toFinset.mpr hxI
  calc I'.lengthSum T' = _ := hsplit
    _ < ∑ t ∈ hI.toFinset.erase x, lenW t + lenW x :=
      ENat.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top hfin' hfar_le) hfar_le
        (lt_of_le_of_lt hfib_le hsum)
    _ = I.lengthSum hI.toFinset := Finset.sum_erase_add _ _ hx'

end AlgebraicGeometry.Scheme.IdealSheafData

end
